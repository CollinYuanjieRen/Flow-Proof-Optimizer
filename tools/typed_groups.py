"""Combine typed same-file findings with typed checks of selected cross-file script groups."""
import argparse
import csv
import itertools
import json
import subprocess
from collections import defaultdict
from functools import cache
from pathlib import Path


def verified_pairs(objects, scanner, within_rows, groups, min_group_lines):
    pairs = {}
    exact = {"same-body", "same-body-via-helpers"}

    def remember(first, second, kind, estimate):
        key = tuple(sorted((first, second)))
        if first != second and (key not in pairs or pairs[key]["estimated_lines"] < estimate):
            pairs[key] = dict(left=key[0], right=key[1], kind=kind, estimated_lines=estimate)

    def module(path):
        return ".".join(Path(path).with_suffix("").parts)

    for size, path, kind, a, b in within_rows:
        if kind in exact:
            remember((module(path), a), (module(path), b), kind, int(size) - 1)

    @cache
    def names(path):
        info = json.loads((objects / path).with_suffix(".ilean").read_bytes())
        result = defaultdict(list)
        for name, span in info["decls"].items():
            result[(span[4] + 1, name.split(".")[-1])].append(name)
        return result

    by_files = defaultdict(list)
    for group in groups:
        if group["lines"] < min_group_lines:
            continue
        resolved = []
        for path, line, name, size in sorted(group["copies"]):
            hits = names(path).get((line, name.split(".")[-1]), ())
            if len(hits) == 1:
                resolved.append((path, hits[0], size))
        for (fa, a, sa), (fb, b, sb) in itertools.combinations(resolved, 2):
            by_files[fa, fb].append((a, b, min(sa, sb) - 1))

    for (fa, fb), candidates in sorted(by_files.items()):
        files = [(objects / f).with_suffix(".olean") for f in dict.fromkeys((fa, fb))]
        args = [scanner, files[0]] if fa == fb else [scanner, files[0], "--cross", files[1]]
        data = subprocess.check_output(args, text=True, stderr=subprocess.PIPE)
        matches = {(a, b): k for k, a, b in csv.reader(data.splitlines(), delimiter="\t") if k in exact}
        for a, b, estimate in candidates:
            kind = matches.get((a, b)) or (matches.get((b, a)) if fa == fb else None)
            if kind:
                remember((module(fa), a), (module(fb), b), kind, estimate)
    return sorted(pairs.values(), key=lambda r: (-r["estimated_lines"], r["left"], r["right"]))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("objects", type=Path)
    parser.add_argument("scanner", type=Path)
    parser.add_argument("same_file_tsv", type=Path, help="scan_project.py output")
    parser.add_argument("groups_jsonl", type=Path, help="large_groups.py output")
    parser.add_argument("--min-group-lines", type=int, default=0)
    args = parser.parse_args()
    with args.same_file_tsv.open() as within, args.groups_jsonl.open() as groups:
        pairs = verified_pairs(args.objects, args.scanner.resolve(), csv.reader(within, delimiter="\t"),
                               map(json.loads, groups), args.min_group_lines)
    print(json.dumps(pairs, ensure_ascii=False))
