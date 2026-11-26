"""Find repeated complete Lean tactic branches in compiler-located theorem bodies.

The proposals are source intervals, including the bullets. An application prefix
leaves its remaining premises at each caller. Elaboration and replay decide
whether a proposal can actually implement one shared proof.
"""
import argparse
from collections import defaultdict
import json
from pathlib import Path

from unreferenced_family import source_declarations


def branch_sites(lines, first, stop, minimum, stats):
    """Yield source shapes and one-based inclusive ranges within a half-open interval."""
    ends = {}
    stack = []
    for i in range(stop - 1, first - 1, -1):
        line = lines[i].rstrip()
        if not line:
            continue
        indent = len(line) - len(line.lstrip())
        while stack and stack[-1][0] > indent:
            stack.pop()
        next_sibling = stack[-1][1] if stack else stop
        stack.append((indent, i))
        if not (line.strip() == "·" or line.lstrip().startswith("· ")):
            continue
        end = next_sibling
        while end > i + 1 and not lines[end - 1].strip():
            end -= 1
        key = tuple(s[indent:].rstrip() for s in lines[i:end])
        ends[i] = (indent, next_sibling, end, key)
        stats["complete_branches"] += 1
        if end - i >= minimum:
            yield ("branch", key), i + 1, end
    for i in range(first, stop):
        tactic = lines[i].strip()
        if not tactic.startswith("apply "):
            continue
        indent = len(lines[i]) - len(lines[i].lstrip())
        j = i + 1
        prefix = []
        while j in ends and ends[j][0] == indent:
            _, j, end, key = ends[j]
            prefix.append(key)
            # The final premise stays with the caller in this rule.
            if j in ends and ends[j][0] == indent and end - i >= minimum:
                stats["application_prefixes"] += 1
                yield ("apply-prefix", tactic, tuple(prefix)), i + 1, end


def branch_candidates(lines, declarations, minimum=6):
    groups = defaultdict(list)
    stats = {"complete_branches": 0, "application_prefixes": 0}
    for name, decl in declarations.items():
        first, stop = decl["first_line"] - 1, decl["last_line"]
        for key, start, end in branch_sites(lines, first, stop, minimum, stats):
            groups[key].append((name, start, end))
    rows = []
    for key, sites in groups.items():
        if len({name for name, _, _ in sites}) < 2:
            continue
        sites = sorted(sites)
        lengths = [end - start + 1 for _, start, end in sites]
        rows.append(dict(kind=key[0], sites=sites, repeated_lines=sum(lengths) - max(lengths)))
    return stats, sorted(rows, key=lambda r: (-r["repeated_lines"], r["kind"], r["sites"]))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path)
    parser.add_argument("ilean", type=Path)
    parser.add_argument("owners", nargs="*")
    parser.add_argument("--min-lines", type=int, default=6)
    args = parser.parse_args()
    decls = source_declarations(args.source, json.loads(args.ilean.read_bytes()))
    if args.owners:
        decls = {n: decls[n] for n in args.owners}
    stats, hits = branch_candidates(args.source.read_text().splitlines(), decls, args.min_lines)
    print(json.dumps(dict(stats=stats, candidates=hits), ensure_ascii=False))
