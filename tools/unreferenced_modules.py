"""Rank entire modules without external kernel references or named export roots.

This ranks candidates. Source commands, registrations, re-exports, import users
and overlapping upstream work still need inspection before removing a module.
"""
import argparse
from collections import Counter
import json
from pathlib import Path
import sqlite3

from census_report import unpack


def rank(database, tree, source, roots):
    external = set(roots)
    import_counts = Counter()
    rows = []
    query = """
        SELECT m.edges, m.imports, s.name FROM snapshot s
        LEFT JOIN modules m USING(name, rules, sha) WHERE s.tree=?
    """
    with sqlite3.connect(database.resolve().as_uri() + "?mode=ro", uri=True) as db:
        count = 0
        for edges, imports, module in db.execute(query, (tree,)):
            if edges is None:
                raise ValueError(f"snapshot incomplete at {module}")
            local = unpack(edges)
            references = {name for _, uses in local for name in uses}
            references.difference_update(name for name, _ in local)
            external.update(references)
            import_counts.update(set(unpack(imports)))
            count += 1
        if not count:
            raise ValueError("unknown source tree")
        empty = 0
        for edges, _, module in db.execute(query, (tree,)):
            decls = unpack(edges)
            if not decls:
                empty += 1
                continue
            if any(name in external for name, _ in decls):
                continue
            file = Path(*module.split(".")).with_suffix(".lean")
            lines = len((source / file).read_bytes().splitlines())
            rows.append(dict(module=module, file=str(file), lines=lines, declarations=len(decls),
                             direct_importers=import_counts[module]))
    rows.sort(key=lambda row: (-row["lines"], row["module"]))
    return dict(tree=tree, modules=count, empty_modules=empty, candidates=rows)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("database", type=Path)
    parser.add_argument("tree")
    parser.add_argument("sources", type=Path)
    parser.add_argument("export_targets", type=Path)
    args = parser.parse_args()
    roots = args.export_targets.read_text().splitlines()[1].split()
    print(json.dumps(rank(args.database, args.tree, args.sources, roots), ensure_ascii=False))
