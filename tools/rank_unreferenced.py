"""Rank named source theorems with zero incoming checked declaration references.

Only the final edits are verified with exact compiler spans, uses of generated
auxiliaries, attributes, project interfaces and recompilation. The source line
counts here schedule that work.
"""
import argparse
from collections import Counter, defaultdict
from contextlib import nullcontext
import gzip
from itertools import groupby
import json
from pathlib import Path
import sqlite3

from census_report import unpack
from source_pairs import command, declaration_spelling, header


def rank(database, tree, sources, exports, dest, *, zero_names=None, objects=None):
    roots = set(exports)
    used = set(roots)
    counts = Counter()
    candidates = []
    with sqlite3.connect(database) as db:
        modules = list(db.execute("""
            SELECT s.name, m.id FROM snapshot s LEFT JOIN modules m USING(name,rules,sha)
            WHERE s.tree=? ORDER BY s.name
        """, (tree,)))
        if not modules or any(mid is None for _, mid in modules):
            raise ValueError("a complete compiled snapshot is required")
        if zero_names is not None:
            print(json.dumps({"tree": tree}), file=zero_names)
        for _, mid in modules:
            blob, = db.execute("SELECT edges FROM modules WHERE id=?", (mid,)).fetchone()
            for _, refs in unpack(blob):
                used.update(refs)
        # The receipt indexes proof fingerprints, not module IDs. Stream the catalog once.
        selected = dict((mid, name) for name, mid in modules)
        catalog = db.execute("SELECT module_id,name FROM proofs ORDER BY module_id")
        for mid, rows in groupby(catalog, key=lambda row: row[0]):
            if mid not in selected:
                continue
            module = selected[mid]
            proofs = [name for _, name in rows]
            counts["compiled_theorems"] += len(proofs)
            unused = set(proofs).difference(used)
            counts["zero_incoming_nonexported"] += len(unused)
            if not unused:
                continue
            if zero_names is not None:
                print(json.dumps([module, sorted(unused)]), file=zero_names)
            file = Path(*module.split(".")).with_suffix(".lean")
            lines = (sources / file).read_text().splitlines()
            if objects is not None:
                info = json.loads((objects / file.with_suffix(".ilean")).read_bytes())
                if info["module"] != module:
                    raise ValueError(f"reference data belongs to a different module: {module}")
                for name in unused.intersection(info["decls"]):
                    pos = info["decls"][name]
                    spelling = declaration_spelling(lines, name, pos)
                    if spelling is not None:
                        candidates.append(dict(module=module, file=str(file), name=name,
                            theorem=spelling, first_line=pos[0]+1, theorem_line=pos[4]+1,
                            last_line=pos[2]+1, lines_hint=pos[2]-pos[4]+1))
                continue
            by_last = defaultdict(list)
            for n in proofs:
                by_last[n.rsplit(".", 1)[-1]].append(n)
            commands = [i for i, line in enumerate(lines) if command.match(line)]
            claimed = defaultdict(list)
            for start, stop in zip(commands, commands[1:] + [len(lines)]):
                match = header.match(lines[start])
                if not match:
                    continue
                short = match[1]
                matches = [n for n in by_last.get(short.rsplit(".", 1)[-1], ())
                           if n == short or n.endswith("." + short)]
                if len(matches) != 1 or matches[0] not in unused:
                    continue
                while stop > start + 1 and not lines[stop - 1].strip():
                    stop -= 1
                name = matches[0]
                claimed[name].append(dict(module=module, file=str(file), name=name,
                                          theorem=short, first_line=start+1, last_line=stop,
                                          lines_hint=stop-start))
            for rows in claimed.values():
                if len(rows) == 1:
                    candidates.extend(rows)
    candidates.sort(key=lambda r: (-r["lines_hint"], r["module"], r["name"]))
    with dest.open("w") as stream:
        for row in candidates:
            print(json.dumps(row, ensure_ascii=False), file=stream)
    counts["source_hints"] = len(candidates)
    counts["modules"] = len(modules)
    return counts


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    for key in ("database", "sources", "export_targets", "output"):
        parser.add_argument(key, type=Path)
    parser.add_argument("tree")
    parser.add_argument("--objects", type=Path, help="locate declarations using .ilean files from this revision")
    parser.add_argument("--zero-names", type=Path,
                        help="also write all zero-incoming names by module as gzip JSON lines")
    args = parser.parse_args()
    roots = args.export_targets.read_text().splitlines()[1].split()
    with (gzip.open(args.zero_names, "wt") if args.zero_names else nullcontext()) as stream:
        counts = rank(args.database, args.tree, args.sources, roots, args.output,
                      zero_names=stream, objects=args.objects)
    print(json.dumps(counts))
