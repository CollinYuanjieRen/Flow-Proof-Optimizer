"""Find aligned direct callers of previously verified duplicate declarations.

Input is verify_groups JSONL. Each proposed boundary is a pair of resolved
source references. Implicit kernel arguments, binder compatibility and proof
identity still need checking when a proposed helper is instantiated.
"""
import argparse
from collections import Counter, defaultdict
from functools import cache
from itertools import combinations, product
import json
from pathlib import Path
import sqlite3

from census_report import unpack
from private_duplicate import source_span


def reference_sequence(source, info, span, owner):
    declaration = info["decls"][owner]
    start, stop = span(declaration)
    name_range = span(declaration[4:])
    names = {name_range: None}
    refs = iter(info["references"])
    for key, data in zip(refs, refs, strict=True):
        if len(key) != 3 or key[0] != 0:
            continue
        for use in data["usages"]:
            if use[-1] != owner or use[:2] == use[2:4]:
                continue
            position = span(use)
            if position == name_range and key[2] == owner:
                continue
            if names.setdefault(position, key[2]) != key[2]:
                return None
    fragments = []
    order = []
    for (left, right), name in sorted(names.items()):
        if not start <= left < right <= stop:
            return None
        fragments.append(source[start:left])
        order.append(name)
        start = right
    fragments.append(source[start:stop])
    return fragments, order


def classify(left, right):
    if left is None or right is None:
        return "ambiguous_ranges", {}
    if left[0] != right[0]:
        return "unaligned_source", {}
    pairs = Counter(zip(left[1], right[1], strict=True))
    if (None, None) not in pairs or len({a for a, b in pairs}) != len(pairs) or len(
        {b for a, b in pairs}
    ) != len(pairs):
        return "inconsistent_names", {}
    return "aligned", {pair: n for pair, n in pairs.items() if pair[0] != pair[1]}


def scan(groups, database, tree, source_root, library):
    @cache
    def module(name):
        path = Path(*name.split("."))
        src = (source_root / path).with_suffix(".lean").read_text()
        info = json.loads((library / path).with_suffix(".ilean").read_bytes())
        row = database.execute(
            "SELECT edges FROM snapshot JOIN modules USING(name,rules,sha) WHERE tree=? AND name=?",
            (tree, name),
        ).fetchone()
        callers = defaultdict(list)
        for owner, deps in unpack(row[0]):
            if owner in info["decls"]:
                for dep in set(deps):
                    callers[dep].append(owner)
        return src, info, source_span(src), callers

    @cache
    def sequence(site):
        m, n = site
        src, info, span, _ = module(m)
        return reference_sequence(src, info, span, n)

    exact = set()
    callers = set()
    for group in groups:
        if group["tree"] != tree:
            raise ValueError("the compiled census and duplicate groups use different source trees")
        for cls in group["classes"]:
            for (a, x, *_), (b, y, *_) in combinations(sorted(cls), 2):
                if a != b:
                    exact.add(((a, x), (b, y)))
                    for u, v in product(module(a)[3][x], module(b)[3][y]):
                        callers.add(((a, u), (b, v)))
    counts = Counter()
    candidates = []
    for left, right in sorted(callers):
        status, pairs = classify(sequence(left), sequence(right))
        if status != "aligned":
            counts[status] += 1
            continue
        residual = [(x, y, n) for (x, y), n in pairs.items()
                    if ((left[0], x), (right[0], y)) not in exact]
        counts["with_boundary" if residual else "no_boundary"] += 1
        if residual:
            lengths = []
            for m, n in (left, right):
                start, _, end, *_ = module(m)[1]["decls"][n]
                lengths.append(end - start + 1)
            candidates.append(dict(callers=[left, right], lines=lengths, differing=residual,
                                   verified_duplicate_pairs=len(pairs) - len(residual)))
    candidates.sort(key=lambda row: -min(row["lines"]))
    return dict(tree=tree, seed_pairs=len(exact), modules=module.cache_info().currsize,
                caller_pairs=len(callers), counts=dict(counts), candidates=candidates)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    for arg in ("groups", "database", "source", "library"):
        parser.add_argument(arg, type=Path)
    parser.add_argument("tree")
    args = parser.parse_args()
    with args.groups.open() as file, sqlite3.connect(
        args.database.resolve().as_uri() + "?mode=ro", uri=True
    ) as database:
        print(json.dumps(scan(map(json.loads, file), database, args.tree, args.source, args.library),
                         ensure_ascii=False, indent=2))
