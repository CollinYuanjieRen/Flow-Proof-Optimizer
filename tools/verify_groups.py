"""Partition source candidates by exact Lean proof equality on the pinned archives."""
import argparse
from collections import defaultdict
import gzip
import json
from pathlib import Path
import subprocess
import tempfile

from census import unpack


def batches(rows):
    batch, modules = [], set()
    for row in rows:
        needed = {v[0] for v in row["copies"]}
        if batch and len(modules | needed) > 32:
            yield batch
            batch, modules = [], set()
        batch.append(row)
        modules.update(needed)
    if batch:
        yield batch


def verify(group_file, manifest, artifacts, scanner, leantar, output):
    with gzip.open(manifest) as stream:
        tree = json.loads(next(stream))["source_tree"]
        entries = {r[0]: r for r in map(json.loads, stream)}
    groups = same = split = doubles = 0
    with group_file.open() as stream, output.open("w") as dest:
        for batch in batches(map(json.loads, stream)):
            requests = defaultdict(list)
            for row in batch:
                for i, (module, name, *_) in enumerate(row["copies"]):
                    requests[module].append(dict(name=name, group=row["group"], index=i))
            with tempfile.TemporaryDirectory(prefix="rh-exact-proofs-") as tmp:
                files = unpack([entries[m] for m in requests], artifacts, leantar, tmp)
                data = subprocess.check_output([scanner, files[0], "--partition", *files[1:]],
                                               input=json.dumps(list(requests.values())), text=True)
            classes = defaultdict(lambda: defaultdict(list))
            for line in data.splitlines():
                group, index, rep = json.loads(line)
                classes[group][rep].append(index)
            for row in batch:
                membership = classes[row["group"]]
                indices = sorted(i for part in membership.values() for i in part)
                if indices != list(range(len(row["copies"]))):
                    raise ValueError("incomplete exact classification")
                parts = [[row["copies"][i] for i in sorted(part)] for part in membership.values()]
                print(json.dumps(dict(tree=tree, group=row["group"], classes=parts), ensure_ascii=False), file=dest)
                groups += 1
                same += sum(len(part) > 1 for part in parts)
                doubles += sum(len(part) - 1 for part in parts)
                split += len(parts) > 1
            dest.flush()
    print("source groups classified", groups, "exact repeated classes", same,
          "fingerprint buckets split", split, "excess declarations before rewrite eligibility", doubles)


if __name__ == "__main__":
    p = argparse.ArgumentParser(description=__doc__)
    for name in ("groups", "manifest", "artifacts", "scanner", "leantar", "output"):
        p.add_argument(name, type=Path)
    a = p.parse_args()
    verify(a.groups, a.manifest, a.artifacts, a.scanner.resolve(), a.leantar.resolve(), a.output)
