"""Rank repeated source declarations inside common-root fingerprint groups.

The score counts source lines under compiler declaration spans, retaining the
shortest copy. Scope, import cost and full term equality are checked on the
selected source group before a patch is generated.
"""
import argparse
from collections import defaultdict
from heapq import heapify, heappop, heappush
import json
from pathlib import Path

from source_pairs import declaration_spelling


def representative_jobs(exact_groups, root_index):
    """Choose a representative of each repeated exact class for a root.

    Prefer modules covering many remaining classes to reduce artifact loads.
    These representatives schedule discovery. Verify each proposed replacement.
    """
    mask = 1 << root_index
    classes = {}
    by_module = defaultdict(dict)
    for group in exact_groups:
        for index, part in enumerate(group["classes"]):
            members = [row for row in part if row[2] & mask]
            if len(members) < 2:
                continue
            key = group["group"], index
            classes[key] = members
            for module, name, _, _ in members:
                choices = by_module[module]
                choices[key] = min(name, choices.get(key, name))
    remaining = set(classes)
    heap = [(-len(choices), module) for module, choices in by_module.items()]
    heapify(heap)
    jobs = []
    while remaining:
        score, module = heappop(heap)
        choices = by_module[module]
        covered = remaining.intersection(choices)
        if not covered:
            continue
        # Scores decrease as modules are selected. Refresh only the top entry.
        if len(covered) != -score:
            heappush(heap, (-len(covered), module))
            continue
        jobs.append((module, {choices[key]: key for key in sorted(covered)}))
        remaining.difference_update(covered)
    return classes, jobs


def rank(group_file, source, objects, overlay=None):
    by_module = defaultdict(list)
    with group_file.open() as stream:
        for group_id, line in enumerate(stream):
            for mod, name, mask in json.loads(line)["copies"]:
                by_module[mod].append((group_id, name, mask))
    spans = defaultdict(dict)
    for module, queries in by_module.items():
        rel = Path(*module.split("."))
        obj = rel.with_suffix(".ilean")
        path = overlay / obj if overlay and (overlay / obj).exists() else objects / obj
        if not path.exists():
            raise ValueError(f"missing declaration ranges for {module}")
        decls = json.loads(path.read_bytes())["decls"]
        found = [(group, name, mask, decls[name]) for group, name, mask in queries if name in decls]
        if not found:
            continue
        lines = (source / rel.with_suffix(".lean")).read_text().splitlines()
        for group, name, mask, pos in found:
            a, col, b = pos[:3]
            if declaration_spelling(lines, name, pos) is None:
                continue
            key = module, a, col, b, pos[3]
            old = spans[group].get(key)
            if old:
                name = min(name, old[1])
                mask |= old[2]
            spans[group][key] = (module, name, mask, b - a + 1)
    for group, locations in spans.items():
        copies = list(locations.values())
        if len(copies) < 2:
            continue
        def removable(rows):
            sizes = [row[3] for row in rows]
            return sum(sizes) - min(sizes) if sizes else 0
        bits = max(row[2] for row in copies).bit_length()
        live = max((removable(row for row in copies if (row[2] >> i) & 1) for i in range(bits)), default=0)
        yield {"group": group, "copies": sorted(copies), "same_root_lines_hint": live,
               "all_lines_hint": removable(copies)}


if __name__ == "__main__":
    p = argparse.ArgumentParser(description=__doc__)
    for name in ("groups", "source", "objects"):
        p.add_argument(name, type=Path)
    p.add_argument("--overlay", type=Path)
    a = p.parse_args()
    hits = sorted(rank(a.groups, a.source, a.objects, a.overlay),
                  key=lambda g: (-g["same_root_lines_hint"], -g["all_lines_hint"], g["group"]))
    for hit in hits:
        print(json.dumps(hit, ensure_ascii=False))
