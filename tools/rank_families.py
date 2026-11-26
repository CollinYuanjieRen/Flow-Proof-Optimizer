"""Aggregate exact duplicates by source module pair, counting each removable declaration once."""
import argparse
from collections import defaultdict
import json
from pathlib import Path


def families(records):
    totals = defaultdict(dict)
    for group in records:
        for part in group["classes"]:
            by_mod = defaultdict(list)
            for mod, name, roots, lines in part:
                by_mod[mod].append((name, roots, lines))
            for keep, available in by_mod.items():
                for drop, candidates in by_mod.items():
                    # Within one module the proposed family needs a retained copy.
                    anchors = available if keep != drop else [min(available, key=lambda x: (x[2], x[0]))]
                    for name, mask, lines in candidates:
                        for bit in range(mask.bit_length()):
                            options = [n for n, other, _ in anchors if mask & other & (1 << bit)
                                       and (drop != keep or n != name)]
                            if options:
                                totals[keep, drop, bit][name] = [min(options), name, lines]
    out = []
    best = {}
    for (keep, drop, bit), rows in totals.items():
        size = sum(v[2] for v in rows.values())
        if (keep, drop) not in best or size > best[keep, drop][0]:
            best[keep, drop] = size, bit, rows
    for (keep, drop), (size, bit, rows) in best.items():
        out.append(dict(keep=keep, drop=drop, root_index=bit, lines_hint=size,
                        pairs=sorted(rows.values(), key=lambda v: (-v[2], v[1]))))
    return sorted(out, key=lambda r: (-r["lines_hint"], r["keep"], r["drop"]))


if __name__ == "__main__":
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("exact_groups", type=Path)
    a = p.parse_args()
    with a.exact_groups.open() as f:
        for row in families(map(json.loads, f)):
            print(json.dumps(row, ensure_ascii=False))
