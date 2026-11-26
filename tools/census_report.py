"""Summarize a complete receipt and rank exact-fingerprint groups by common-root use."""
import argparse
from collections import Counter
from graphlib import TopologicalSorter
import json
from pathlib import Path
import sqlite3
import zlib


def unpack(blob):
    return json.loads(zlib.decompress(blob))


def report(database, tree, roots, output, *, modules_only=False):
    with sqlite3.connect(database) as db:
        rules, = (r[0] for r in db.execute("SELECT DISTINCT rules FROM snapshot WHERE tree=?", (tree,)))
        db.execute("""CREATE TEMP TABLE selected AS SELECT s.name, m.id FROM snapshot s
                    LEFT JOIN modules m USING(name,sha,rules) WHERE s.tree=? AND s.rules=?""", (tree, rules))
        total, ready = db.execute("SELECT COUNT(*), COUNT(id) FROM selected").fetchone()
        if total != ready:
            raise ValueError(f"snapshot still incomplete: {ready}/{total} modules")
        imports, ids = {}, {}
        for name, mid, imps in db.execute("SELECT s.name, s.id, m.imports FROM selected s JOIN modules m ON s.id=m.id"):
            imports[name] = unpack(imps)
            ids[name] = mid
        todo = ["Main"]
        reachable_modules = set()
        while todo:
            m = todo.pop()
            if m not in reachable_modules and m in imports:
                reachable_modules.add(m)
                todo.extend(imports[m])
        graph = {m: [d for d in imports[m] if d in reachable_modules] for m in sorted(reachable_modules)}
        masks = {name: 1 << i for i, name in enumerate(roots)}
        if modules_only:
            module_counts = {}
        else:
            db.execute("CREATE TEMP TABLE reachable(module_id INTEGER,name TEXT,mask INTEGER,PRIMARY KEY(module_id,name))")
        ndecls = 0
        for m in reversed(tuple(TopologicalSorter(graph).static_order())):
            blob, = db.execute("SELECT edges FROM modules WHERE id=?", (ids[m],)).fetchone()
            edges = dict(unpack(blob))
            if m == "Main" and not set(roots) <= edges.keys():
                raise ValueError("missing export root")
            ndecls += len(edges)
            todo = [n for n in edges if n in masks]
            while todo:
                n = todo.pop()
                for dep in edges[n]:
                    prev = masks.get(dep, 0)
                    if (mask := prev | masks[n]) != prev:
                        masks[dep] = mask
                        if dep in edges:
                            todo.append(dep)
            if modules_only:
                module_counts[m] = {"declarations": len(edges),
                                    "reached_from_any_export": sum(n in masks for n in edges)}
            else:
                db.executemany("INSERT INTO reachable VALUES(?,?,?)",
                               ((ids[m], n, masks[n]) for n in edges if n in masks))
        if modules_only:
            output.write_text(json.dumps({"tree": tree, "roots": roots, "modules": module_counts}))
            return
        db.execute("CREATE TEMP TABLE catalog AS SELECT p.*,s.name AS module FROM proofs p JOIN selected s ON p.module_id=s.id")
        db.execute("CREATE INDEX catalog_key ON catalog(arity,type_hash,body_hash)")
        db.execute("""CREATE TEMP TABLE grouped AS SELECT arity,type_hash,body_hash,COUNT(*) AS n
                    FROM catalog GROUP BY arity,type_hash,body_hash HAVING COUNT(*) > 1""")
        count, = db.execute("SELECT COUNT(*) FROM catalog").fetchone()
        possible, = db.execute("""SELECT COUNT(*) FROM catalog c JOIN reachable r
                                ON c.module_id=r.module_id AND c.name=r.name""").fetchone()
        hits = Counter()
        records = db.execute("""SELECT p.arity,p.type_hash,p.body_hash,p.module,p.name,coalesce(r.mask,0)
            FROM grouped g JOIN catalog p USING(arity,type_hash,body_hash)
            LEFT JOIN reachable r ON p.module_id=r.module_id AND p.name=r.name
            ORDER BY p.arity,p.type_hash,p.body_hash,p.module,p.name""")
        from itertools import groupby
        with output.open("w") as dest:
            for _, items in groupby(records, key=lambda row: row[:3]):
                copies = [[m, name, mask] for _, _, _, m, name, mask in items]
                seen = overlap = 0
                for _, _, mask in copies:
                    overlap |= seen & mask
                    seen |= mask
                hits["hash_groups"] += 1
                hits["theorems_in_hash_groups"] += len(copies)
                hits["groups_with_possible_same_root"] += int(bool(overlap))
                print(json.dumps({"copies": copies, "candidate_roots": [n for i, n in enumerate(roots) if overlap & (1 << i)]},
                                 ensure_ascii=False), file=dest)
        print(dict(modules=total, main_import_modules=len(graph), constants_in_main_imports=ndecls,
                   indexed_theorem_bodies=count, on_candidate_root_paths=possible,
                   outside_five_root_paths=count-possible, **hits), flush=True)


if __name__ == "__main__":
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("database", type=Path)
    p.add_argument("tree")
    p.add_argument("export_targets", type=Path)
    p.add_argument("output", type=Path)
    p.add_argument("--module-coverage", action="store_true",
                   help="report declaration reachability by module inside Main's import closure")
    a = p.parse_args()
    report(a.database, a.tree, a.export_targets.read_text().splitlines()[1].split(), a.output,
           modules_only=a.module_coverage)
