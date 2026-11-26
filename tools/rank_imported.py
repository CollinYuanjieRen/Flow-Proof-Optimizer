"""Rank exact copies in one consumer that can reuse proofs from its existing imports."""
import argparse
from collections import defaultdict
from graphlib import TopologicalSorter
import json
from pathlib import Path
import sqlite3

from census_report import unpack


def rank(database, exact_groups, root_index):
    if root_index < 0:
        raise ValueError("root index must be nonnegative")
    classes = []
    tree = None
    mask = 1 << root_index
    for record in exact_groups:
        if tree is not None and tree != record["tree"]:
            raise ValueError("mixed source trees")
        tree = record["tree"]
        for group in record["classes"]:
            rows = [row for row in group if row[2] & mask]
            if len({r[0] for r in rows}) > 1:
                classes.append(rows)

    modules = sorted({r[0] for rows in classes for r in rows})
    bits = {m: 1 << i for i, m in enumerate(modules)}
    with sqlite3.connect(database) as db:
        imports = {m: unpack(z) for m, z in db.execute(
            "select name,imports from modules join snapshot using(name,rules,sha) where tree=?", (tree,))}
    if not bits.keys() <= imports.keys():
        raise ValueError("candidate modules missing from the compiled snapshot")

    ancestors = {}
    for m in TopologicalSorter(imports).static_order():
        seen = 0
        for parent in imports.get(m, ()):
            seen |= ancestors[parent] | bits.get(parent, 0)
        ancestors[m] = seen

    consumers = defaultdict(dict)
    for rows in classes:
        for module, name, _, lines in rows:
            choices = [(m, n) for m, n, _, _ in rows if ancestors[module] & bits[m]]
            if choices:
                # Prefer an available public name, then a direct import.
                provider, anchor = min(choices, key=lambda x: (
                    x[1].startswith("_private."), x[0] not in imports[module], x))
                consumers[module][name] = [provider, anchor, name, lines]

    out = []
    for module, copies in consumers.items():
        pairs = sorted(copies.values(), key=lambda p: (-p[3], p[2]))
        out.append(dict(drop=module, root_index=root_index, lines_hint=sum(p[3] for p in pairs),
                        pairs=pairs))
    return sorted(out, key=lambda r: (-r["lines_hint"], r["drop"]))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("database", type=Path)
    parser.add_argument("exact_groups", type=Path)
    parser.add_argument("--root-index", type=int, required=True)
    args = parser.parse_args()
    with args.exact_groups.open() as stream:
        for result in rank(args.database, map(json.loads, stream), args.root_index):
            print(json.dumps(result, ensure_ascii=False))
