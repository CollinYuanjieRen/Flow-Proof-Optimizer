"""Find incoming kernel references to private candidate families across an entire receipt."""
import argparse
from collections import defaultdict
import json
from pathlib import Path
import sqlite3

from census_report import unpack


def summarize(database, inventory, output):
    rows = list(map(json.loads, inventory.read_text().splitlines()))
    tree, = {r["tree"] for r in rows}
    targets = {str(Path(r["file"]).with_suffix("")).replace("/", "."): r["declarations"]
               for r in rows if r["declarations"]}
    with sqlite3.connect(database) as db:
        rules, = (r[0] for r in db.execute("SELECT DISTINCT rules FROM snapshot WHERE tree=?", (tree,)))
        ids = dict(db.execute("""SELECT s.name,m.id FROM snapshot s
                  LEFT JOIN modules m USING(name,rules,sha) WHERE s.tree=? AND s.rules=?""", (tree, rules)))
        missing = sum(mid is None for mid in ids.values())
        if missing:
            raise ValueError(f"still missing {missing} modules")
        def edges(mid):
            data, = db.execute("SELECT edges FROM modules WHERE id=?", (mid,)).fetchone()
            return unpack(data)

        def project_imports(module):
            seen = {module}
            todo = [module]
            while todo:
                current = todo.pop()
                data, = db.execute("SELECT imports FROM modules WHERE id=?", (ids[current],)).fetchone()
                for dep in unpack(data):
                    if dep in ids and dep not in seen:
                        seen.add(dep)
                        todo.append(dep)
            return seen

        owners = {}
        for module, names in targets.items():
            found = set()
            for name, _ in edges(ids[module]):
                prefix = name
                while prefix:
                    if prefix in names:
                        if name in owners:
                            raise ValueError(f"ambiguous declaration {name} in {owners[name][0]} and {module}")
                        owners[name] = (module, prefix)
                        if name == prefix:
                            found.add(name)
                        break
                    prefix = prefix.rpartition(".")[0]
            if set(names) - found:
                raise ValueError(f"unknown private theorem: {module}")
        keep, linked, externals = {}, defaultdict(set), defaultdict(list)
        for module, mid in ids.items():
            imports = None
            for name, deps in edges(mid):
                for used in deps:
                    if used not in owners:
                        continue
                    target_module, target = owners[used]
                    if target_module != module:
                        # Separate realizations of a generated Lean name may occur in unrelated modules.
                        if imports is None:
                            imports = project_imports(module)
                        if target_module not in imports:
                            continue
                        externals[target].append([module, name, used])
                    if name in owners and owners[name][0] == module:
                        linked[owners[name][1]].add(target)
                    else:
                        keep.setdefault(target, [module, name, used])
        queue = list(keep)
        while queue:
            n = queue.pop()
            for child in linked[n]:
                if child not in keep:
                    keep[child] = ["retained candidate", n, child]
                    queue.append(child)
        result = {n: {"retained_reference": keep.get(n), "outside_module": externals.get(n, [])}
                  for names in targets.values() for n in names}
        output.write_text(json.dumps(result, ensure_ascii=False))
        print("modules", len(ids), "private source candidates", len(result), "owned kernel declarations", len(owners),
              "reached from retained declarations", len(keep), "with outside-module references", len(externals))


if __name__ == "__main__":
    p = argparse.ArgumentParser(description=__doc__)
    for name in ("database", "inventory", "output"):
        p.add_argument(name, type=Path)
    a = p.parse_args()
    summarize(a.database, a.inventory, a.output)
