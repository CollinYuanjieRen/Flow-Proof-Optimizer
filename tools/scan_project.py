"""Classify source candidates on the built RH checkout, one native process per module."""
import argparse
import csv
import hashlib
import json
import subprocess
import sys
import tempfile
from collections import Counter, defaultdict
from pathlib import Path
from time import monotonic

import source_pairs


def committed_sources(root, revision, known=()):
    """Yield each Lean path and blob ID, with content for blobs outside the caller's cache."""
    entries = subprocess.check_output(["git", "ls-tree", "-rz", revision + ":src"], cwd=root)
    with subprocess.Popen(["git", "cat-file", "--batch"], cwd=root,
                          stdin=subprocess.PIPE, stdout=subprocess.PIPE) as git:
        for entry in entries.split(b"\0"):
            if not entry.endswith(b".lean"):
                continue
            metadata, path = entry.split(b"\t", 1)
            oid = metadata.split()[2].decode()
            content = None
            if oid not in known:
                git.stdin.write(oid.encode() + b"\n")
                git.stdin.flush()
                actual, kind, n = git.stdout.readline().split()
                if kind != b"blob" or actual.decode() != oid:
                    raise ValueError(f"unexpected Git object for {path!r}")
                content = git.stdout.read(int(n))
                if git.stdout.read(1) != b"\n":
                    raise ValueError("incomplete Git blob")
            yield Path(path.decode()), oid, content
        git.stdin.close()
    if git.returncode:
        raise RuntimeError("git cat-file failed")


def committed_candidates(root, cache):
    """Cache only source hints. All selected .olean and .ilean files are read again."""
    parser_hash = hashlib.sha256(Path(source_pairs.__file__).read_bytes()).hexdigest()
    saved = json.loads(cache.read_text()) if cache.exists() else {}
    known = saved.get("blobs", {}) if saved.get("parser") == parser_hash else {}
    current, groups = {}, {}
    misses = 0
    for path, oid, content in committed_sources(root, "HEAD", known):
        if content is not None:
            known[oid] = list(source_pairs.candidates(content.decode()))
            misses += 1
        current[oid] = known[oid]
        if current[oid]:
            groups[path] = current[oid]
    if misses or len(current) != len(known) or not cache.exists():
        with tempfile.NamedTemporaryFile(mode="w", dir=cache.parent, delete=False) as tmp:
            json.dump({"parser": parser_hash, "blobs": current}, tmp, separators=(",", ":"))
        Path(tmp.name).replace(cache)
    print(f"source_blobs={len(current)} parsed={misses}", file=sys.stderr)
    return groups


def classify(root, binary, whole_modules, cache):
    started = monotonic()
    if cache:
        groups = committed_candidates(root, cache)
    else:
        groups = {}
        src = root / "src"
        for path in src.rglob("*.lean"):
            hits = list(source_pairs.candidates(path.read_text()))
            if hits:
                groups[path.relative_to(src)] = hits
    print(f"source_s={monotonic()-started:.3f}", file=sys.stderr)
    # Large same-file repetitions first. The path breaks ties reproducibly.
    schedule = sorted(groups, key=lambda p: (-max(r[0] for r in groups[p]), p))
    for path in schedule:
        obj = (root / ".lake/build/lib/lean" / path).with_suffix(".olean")
        info = json.loads(obj.with_suffix(".ilean").read_text())
        by_line = defaultdict(list)
        for name, span in info["decls"].items():
            by_line[span[4] + 1, name.split(".")[-1]].append(name)
        pairs = []
        for size, line_a, a, line_b, b in groups[path]:
            def resolve(line, name):
                hits = by_line[line, name.split(".")[-1]]
                return hits[0] if len(hits) == 1 else ""
            pairs.append((size, resolve(line_a, a), resolve(line_b, b), a, b))
        names = sorted({name for _, a, b, _, _ in pairs for name in (a, b) if name})
        classes = {}
        if names:
            argv = [binary, str(obj)] + ([] if whole_modules else ["--only", *names])
            proc = subprocess.run(argv, capture_output=True, text=True)
            if proc.returncode:
                raise RuntimeError(f"{path}: {proc.stderr}")
            for row in csv.reader(proc.stdout.splitlines(), delimiter="\t"):
                kind, a, b = row
                classes[frozenset((a, b))] = kind
        for size, a, b, source_a, source_b in pairs:
            status = classes.get(frozenset((a, b)), "unmatched-statement") if a and b else "unresolved-name"
            yield size, path, status, a or source_a, b or source_b


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("checkout", type=Path)
    parser.add_argument("scanner", type=Path)
    parser.add_argument("--whole-modules", action="store_true", help="check the unscheduled baseline")
    parser.add_argument("--candidate-cache", type=Path,
                        help="reuse source-only hints by committed Git blob; use with artifacts built at HEAD")
    args = parser.parse_args()
    start = monotonic()
    counts = Counter()
    modules = set()
    for row in classify(args.checkout, args.scanner.resolve(), args.whole_modules, args.candidate_cache):
        counts[row[2]] += 1
        modules.add(row[1])
        print(*row, sep="\t", flush=True)
    print(f"modules={len(modules)} elapsed_s={monotonic()-start:.3f} {dict(counts)}", file=sys.stderr)
