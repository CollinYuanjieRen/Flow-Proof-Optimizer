"""Rank same-root proof pairs with multiple separated runs of matching source lines.

One line unique to the two eligible declarations seeds the comparison. Matches
nominate proof fragments. Binder identity and equality still need Lean replay.
"""
import argparse
from collections import defaultdict
from difflib import SequenceMatcher
import gzip
import json
from pathlib import Path

from long_duplicates import tactic_bodies
from root_paths import linked_reachability
from source_pairs import matches_declaration_name


def located_bodies(source, library, active):
    for module, owners in sorted(active.items()):
        rel = Path(*module.split(".")).with_suffix(".lean")
        lines = (source / rel).read_text().splitlines()
        declarations = json.loads((library / rel.with_suffix(".ilean")).read_bytes())["decls"]
        by_line = defaultdict(list)
        for name in owners & declarations.keys():
            pos = declarations[name]
            by_line[pos[4]].append((name, pos[2] + 1))
        for short, first, start, stop in tactic_bodies(lines, 1):
            matches = [(name, end) for name, end in by_line[first]
                       if matches_declaration_name(name, short)]
            if len(matches) != 1:
                continue
            name, end = matches[0]
            numbers = []
            body = []
            for index in range(start, min(stop, end)):
                line = lines[index].strip()
                if line and not line.startswith(("--", "/-", "*")):
                    numbers.append(index + 1)
                    body.append(line)
            if body:
                yield name, (str(rel), numbers, body)


def scan(source, library, graph, roots):
    masks, _ = linked_reachability(graph.items(), roots, [])
    active = defaultdict(set)
    for name in masks:
        active[graph[name][0]].add(name)
    bodies = dict(located_bodies(source, library, active))
    owners = defaultdict(set)
    for name, (_, _, body) in bodies.items():
        for line in set(body):
            owners[line].add(name)

    anchors = defaultdict(set)
    for line, names in owners.items():
        if len(names) == 2:
            left, right = sorted(names)
            if masks[left] & masks[right]:
                anchors[left, right].add(line)

    rows = []
    for (left, right), shared in anchors.items():
        lf, ls, a = bodies[left]
        rf, rs, b = bodies[right]
        blocks = SequenceMatcher(None, a, b, autojunk=False).get_matching_blocks()
        runs = [run for run in blocks if run.size and (run.size > 1 or a[run.a] in shared)]
        if len(runs) >= 2:
            spans = [[ls[i], ls[i + k - 1], rs[j], rs[j + k - 1]] for i, j, k in runs]
            rows.append(dict(left=left, right=right, lf=lf, rf=rf, matched=sum(r.size for r in runs),
                             longest=max(r.size for r in runs), lengths=[len(a), len(b)],
                             anchors=len(shared), ranges=spans, root_mask=masks[left] & masks[right]))
    rows.sort(key=lambda r: (-r["matched"], -r["anchors"], r["left"], r["right"]))
    return dict(roots=roots, eligible=len(bodies), seeded_pairs=len(anchors), rows=rows)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    for arg in ("source", "library", "linked_graph", "comparator", "output"):
        parser.add_argument(arg, type=Path)
    args = parser.parse_args()
    with gzip.open(args.linked_graph, "rt") as stream:
        graph = dict(map(json.loads, stream))
    roots = json.loads(args.comparator.read_bytes())["theorem_names"]
    result = scan(args.source, args.library, graph, roots)
    args.output.write_text(json.dumps(result, ensure_ascii=False))
    print(f"{result['eligible']} eligible proofs, {result['seeded_pairs']} seeded pairs, "
          f"{len(result['rows'])} candidates")
