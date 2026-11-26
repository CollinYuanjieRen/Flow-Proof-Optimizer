"""Find repeated multiline have proofs in Lean source theorems.

Matches are scheduling hints. A shared spelling may resolve to different local
variables at the two sites. Typed proof comparison is required before rewriting.
"""
import argparse
from array import array
from collections import defaultdict
from hashlib import blake2b
from itertools import combinations, groupby
import json
from pathlib import Path

from source_pairs import command, header
from unused_have import have, named_have


def proof_opener(lines, first, stop, match):
    """Recognize typed or parameterized local proof headers, including continuations."""
    tail = lines[first][match.end(2):].lstrip()
    if not tail.startswith((":", "(", "{", "[")):
        return None
    for j in range(first, stop):
        line = lines[j]
        if j > first and line.strip() and len(line) - len(line.lstrip()) <= len(match[1]):
            return None
        if ":=" in line:
            rhs = line.split(":=", 1)[1].strip()
            return rhs if rhs in ("by", "{") else None
    return None


def block_occurrences(lines):
    starts = [i for i, line in enumerate(lines) if command.match(line)]
    for start, stop in zip(starts, starts[1:] + [len(lines)]):
        decl = header.match(lines[start])
        if not decl:
            continue
        for i in range(start + 1, stop):
            match = named_have.match(lines[i])
            if not match:
                continue
            opener = "by" if have.match(lines[i]) else proof_opener(lines, i, stop, match)
            if opener is None:
                continue
            indent = len(match[1])
            end = i + 1
            while end < stop and (not lines[end].strip() or len(lines[end]) - len(lines[end].lstrip()) > indent):
                end += 1
            if opener == "{" and end < stop and lines[end].rstrip() == match[1] + "}":
                end += 1
            while end > i + 1 and not lines[end - 1].strip():
                end -= 1
            if end == i + 1:
                continue
            # Keep every token after the binder name, including the type.
            body = tuple(lines[j][indent:] for j in range(i + 1, end))
            key = (lines[i][match.end(2):], body)
            yield key, dict(theorem=decl[1], theorem_line=start+1, binder=match[2],
                            first_line=i+1, last_line=end)


def repeated_blocks(lines):
    for _, blocks in groupby(block_occurrences(lines), key=lambda entry: entry[1]["theorem_line"]):
        by_text = defaultdict(list)
        for text, site in blocks:
            prior = by_text[text]
            if prior:
                yield dict(**site, earlier=prior.copy(), lines_hint=site["last_line"]-site["first_line"])
            prior.append({k: site[k] for k in ("binder", "first_line", "last_line")})


def shared_blocks(lines):
    """Group matching local proofs from distinct declarations in a single module."""
    by_text = defaultdict(list)
    for text, site in block_occurrences(lines):
        by_text[text].append(site)
    for sites in by_text.values():
        if len({s["theorem_line"] for s in sites}) > 1:
            yield dict(sites=sites, body_lines=sites[0]["last_line"]-sites[0]["first_line"])


def cross_module_groups(directory):
    """Index local source blocks by digest; the caller must verify hits on typed proofs."""
    occurrences = defaultdict(list)
    for path in directory.rglob("*.lean"):
        source = path.read_text()
        if "have " not in source:
            continue
        file = str(path.relative_to(directory))
        for (typ, body), site in block_occurrences(source.splitlines()):
            digest = blake2b("\n".join((typ, *body)).encode(), digest_size=20).digest()
            occurrences[digest].append((file, site["theorem"], site["theorem_line"],
                                        site["binder"], site["first_line"], site["last_line"]))
    for digest, sites in occurrences.items():
        if len(sites) > 1 and any(s[0] != sites[0][0] for s in sites[1:]):
            sites.sort()
            size = sites[0][-1] - sites[0][-2]
            yield dict(hash=digest.hex(), body_lines=size, sites=sites,
                       files=len({s[0] for s in sites}), lines_hint=size*(len(sites)-1))


def covered_source_lines(sites):
    """Count distinct source lines occupied by possibly overlapping candidate blocks."""
    by_file = defaultdict(list)
    for site in sites:
        by_file[site["file"]].append((site["first_line"], site["last_line"]))
    total = 0
    for intervals in by_file.values():
        end = 0
        for start, stop in sorted(intervals):
            total += max(0, stop - max(start - 1, end))
            end = max(end, stop)
    return total


def anchored_runs(directory, groups):
    """Extend matching have blocks into maximal equal runs of stripped source lines."""
    wanted = defaultdict(set)
    for group in groups:
        for file, _, theorem_line, *_ in group["sites"]:
            wanted[file].add(theorem_line)

    # Intern lines so frequent anchors reuse the same theorem and the same strings.
    parts = {}
    line_ids = {}
    for file, needed in wanted.items():
        lines = (directory / file).read_text().splitlines()
        starts = [i for i, line in enumerate(lines) if command.match(line)]
        for begin, end in zip(starts, starts[1:] + [len(lines)]):
            if begin + 1 in needed:
                parts[file, begin + 1] = array("I", (
                    line_ids.setdefault(line.strip(), len(line_ids)) for line in lines[begin:end]))
    del line_ids

    runs = defaultdict(set)
    for group in groups:
        for left, right in combinations(sorted(group["sites"]), 2):
            f, n, a, _, start, stop = left
            h, o, b, _, other, other_stop = right
            if f == h or stop-start != other_stop-other:
                continue
            xs, ys = parts[f, a], parts[h, b]
            i, j = start-a, other-b
            size = stop-start+1
            if xs[i] != ys[j]:  # Matching local proofs may name their result differently.
                i += 1
                j += 1
                size -= 1
            if not size or xs[i:i+size] != ys[j:j+size]:
                continue
            while i and j and xs[i-1] == ys[j-1]:
                i -= 1
                j -= 1
                size += 1
            while i+size < len(xs) and j+size < len(ys) and xs[i+size] == ys[j+size]:
                size += 1
            runs[f, n, a, h, o, b, a+i, b+j, size].add(group["hash"])

    for (f, n, a, h, o, b, i, j, size), hashes in runs.items():
        yield dict(files=[f, h], names=[n, o], theorem_lines=[a, b], starts=[i, j],
                   lines=size, anchors=sorted(hashes))


def aligned_runs(runs):
    """Find maximum matching line coverage, in order and without overlap in either theorem."""
    by_pair = defaultdict(list)
    for run in runs:
        key = (tuple(run["files"]), tuple(run["theorem_lines"]), tuple(run["names"]))
        by_pair[key].append((*run["starts"], run["lines"]))
    for (files, theorem_lines, names), intervals in by_pair.items():
        intervals.sort()
        scores = []
        previous = []
        for i, (a, b, length) in enumerate(intervals):
            score, predecessor = 0, None
            for j in range(i):
                x, y, size = intervals[j]
                if x + size <= a and y + size <= b and scores[j] > score:
                    score, predecessor = scores[j], j
            scores.append(score + length)
            previous.append(predecessor)
        best = max(range(len(scores)), key=scores.__getitem__)
        total = scores[best]
        chain = []
        while best is not None:
            chain.append(intervals[best])
            best = previous[best]
        yield dict(files=files, theorem_lines=theorem_lines, names=names,
                   lines=total, intervals=chain[::-1])


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path)
    scope = parser.add_mutually_exclusive_group()
    scope.add_argument("--across-declarations", action="store_true")
    scope.add_argument("--across-modules", action="store_true")
    scope.add_argument("--anchored-runs", action="store_true",
                       help="rank matching source runs around cross-module have blocks")
    scope.add_argument("--aligned-runs", action="store_true",
                       help="rank theorem pairs by disjoint matching source runs in order")
    args = parser.parse_args()
    if args.across_modules or args.anchored_runs or args.aligned_runs:
        groups = sorted(cross_module_groups(args.source), key=lambda r: (-r["lines_hint"], r["hash"]))
        if args.anchored_runs:
            groups = sorted(anchored_runs(args.source, groups),
                            key=lambda r: (-r["lines"], r["files"], r["starts"], r["theorem_lines"]))
        elif args.aligned_runs:
            groups = sorted(aligned_runs(anchored_runs(args.source, groups)),
                            key=lambda r: (-r["lines"], r["files"], r["theorem_lines"]))
        for row in groups:
            print(json.dumps(row, ensure_ascii=False))
        raise SystemExit(0)
    scan = shared_blocks if args.across_declarations else repeated_blocks
    for path in args.source.rglob("*.lean"):
        source = path.read_text()
        if "have " in source:
            for row in scan(source.splitlines()):
                print(json.dumps(dict(file=str(path.relative_to(args.source)), **row), ensure_ascii=False))
