"""Rank contiguous repeated source in Lean tactic proofs for typed verification."""
import argparse
from array import array
from collections import defaultdict, deque
from itertools import combinations
import json
from pathlib import Path
import re

from source_pairs import command, header


def winnowed_anchors(lines, gram, window):
    """Report the rightmost minimum rolling hash in each window, once per position."""
    base = 1_000_003
    modulus = 1 << 64
    mask = modulus - 1
    power = pow(base, gram - 1, modulus)
    value = 0
    minima = deque()
    previous = -1
    for end, line in enumerate(lines):
        if end >= gram:
            value = (value - lines[end - gram] * power) & mask
        value = (value * base + line) & mask
        start = end - gram + 1
        if start < 0:
            continue
        while minima and minima[-1][0] >= value:
            minima.pop()
        minima.append((value, start))
        while minima[0][1] <= start - window:
            minima.popleft()
        if start + 1 >= window and minima[0][1] != previous:
            yield minima[0]
            previous = minima[0][1]


def tactic_bodies(lines, minimum):
    starts = [i for i, line in enumerate(lines) if command.match(line)]
    for first, end in zip(starts, starts[1:] + [len(lines)]):
        if end - first < minimum:
            continue
        decl = header.match(lines[first])
        if not decl:
            continue
        by = next((i for i in range(first, end) if re.search(r":=\s*by\s*$", lines[i])), None)
        if by is None:
            continue
        body = by + 1
        while end > body and (not lines[end - 1].strip() or not lines[end - 1][:1].isspace()):
            end -= 1
        if end - body >= minimum:
            yield decl[1], first, body, end


def multi_declaration_runs(matches, bodies, sites, minimum):
    """Rank shared blocks using one occurrence per declaration and at least three declarations."""
    occurrences = defaultdict(set)
    for u, v, left, right, size in matches:
        if u == v:
            continue
        for offset in range(size - minimum + 1):
            # The line IDs compare spellings exactly. Hash collisions cannot merge blocks.
            block = bodies[u][left + offset:left + offset + minimum].tobytes()
            occurrences[block].update(((u, left + offset), (v, right + offset)))

    alignments = defaultdict(set)
    for copies in occurrences.values():
        first = {}
        for declaration, start in sorted(copies):
            first.setdefault(declaration, start)
        if len(first) < 3:
            continue
        reference = next(iter(first.values()))
        alignment = tuple((index, start - reference) for index, start in first.items())
        alignments[alignment].add(reference)

    rows = []
    for alignment, starts in alignments.items():
        for first in starts:
            if first - 1 in starts:
                continue
            last = first
            while last + 1 in starts:
                last += 1
            length = last - first + minimum
            locations = sorted([*sites[i][:3], sites[i][3] + first + delta] for i, delta in alignment)
            rows.append(dict(lines=length, copies=len(locations), gross=(len(locations) - 1) * length,
                             sites=locations))
    return sorted(rows, key=lambda row: (-row["gross"], -row["lines"], row["sites"]))


def scan(source, minimum=80, *, multi_copy=False):
    """Scan line spellings ignoring outer whitespace. Results are source hints."""
    if minimum < 1:
        raise ValueError("minimum must be positive")
    # Reserve a sampling window for short runs as well. Exact extension checks each hit.
    gram = min(24, max(1, minimum // 2))
    window = minimum - gram + 1
    symbols = {}
    bodies = []
    sites = []
    anchors = defaultdict(list)
    files = 0
    for path in sorted(source.rglob("*.lean")):
        files += 1
        lines = path.read_text().splitlines()
        if len(lines) < minimum:
            continue
        for name, first, start, end in tactic_bodies(lines, minimum):
            body = array("I", (symbols.setdefault(line.strip(), len(symbols) + 1)
                               for line in lines[start:end]))
            index = len(bodies)
            bodies.append(body)
            sites.append((str(path.relative_to(source)), name, first + 1, start + 1))
            for key, offset in winnowed_anchors(body, gram, window):
                anchors[key].append((index, offset))

    matches = set()
    covered = defaultdict(list)
    for group in anchors.values():
        for (u, i), (v, j) in combinations(group, 2):
            x, y = bodies[u], bodies[v]
            diagonal = (u, v, j - i)
            if any(a <= i and i + gram <= b for a, b in covered.get(diagonal, ())):
                continue
            if x[i:i + gram] != y[j:j + gram]:
                continue
            left, right = i, i + gram
            while left > 0 and j + left - i > 0 and x[left - 1] == y[j + left - i - 1]:
                left -= 1
            while right < len(x) and j + right - i < len(y) and x[right] == y[j + right - i]:
                right += 1
            covered[diagonal].append((left, right))
            length = right - left
            if u == v:
                length = min(length, j - i)
            if length >= minimum:
                matches.add((u, v, left, j + left - i, length))
    rows = [dict(sites=[sites[u], sites[v]], starts=[sites[u][3] + i, sites[v][3] + j], lines=size)
            for u, v, i, j, size in matches]
    rows.sort(key=lambda r: (-r["lines"], r["sites"], r["starts"]))
    result = dict(minimum=minimum, gram=gram, window=window, files=files, eligible=len(sites),
                anchors=sum(map(len, anchors.values())), runs=len(rows), rows=rows)
    if multi_copy:
        result["groups"] = multi_declaration_runs(matches, bodies, sites, minimum)
    return result


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path)
    parser.add_argument("--minimum", type=int, default=80)
    parser.add_argument("--multi-copy", action="store_true",
                        help="also rank shared blocks across three or more declarations by gross lines")
    args = parser.parse_args()
    print(json.dumps(scan(args.source, args.minimum, multi_copy=args.multi_copy), ensure_ascii=False))
