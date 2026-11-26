"""Rank identical proof scripts across modules; the scores are source-line estimates."""
import argparse
import hashlib
import json
import re
from collections import defaultdict
from pathlib import Path

from source_pairs import command, header


def proof_blocks(source, min_lines):
    starts = [m.start() for m in command.finditer(source)] + [len(source)]
    line = 1 + source.count("\n", 0, starts[0])
    for a, b in zip(starts, starts[1:]):
        start = line
        line += source.count("\n", a, b)
        if line - start < min_lines:
            continue
        m = header.match(source[a:b].rstrip())
        if not m:
            continue
        signature, sep, proof = m[2].partition(":= by")
        if not sep:
            continue
        # Blank lines and standalone line comments make poor volume estimates.
        rows = [s.rstrip() for s in proof.splitlines() if s.strip() and not s.lstrip().startswith("--")]
        if len(rows) < min_lines:
            continue
        digest = hashlib.sha256("\n".join(rows).encode()).hexdigest()
        yield digest, start, m[1], len(rows)


def groups(root, min_lines):
    index = defaultdict(list)
    for path in root.rglob("*.lean"):
        rel = str(path.relative_to(root))
        for key, line, name, size in proof_blocks(path.read_text(), min_lines):
            index[key].append((rel, line, name, size))
    for copies in index.values():
        if len(copies) >= 2:
            copies.sort()
            # Keep one proof and replace the body of every other copy by one line.
            yield (len(copies) - 1) * (copies[0][3] - 1), copies


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("src", type=Path)
    parser.add_argument("--min-lines", type=int, default=8, help="candidate discovery scope")
    args = parser.parse_args()
    for score, copies in sorted(groups(args.src, args.min_lines), reverse=True):
        print(json.dumps({"lines": score, "copies": copies}, ensure_ascii=False))
