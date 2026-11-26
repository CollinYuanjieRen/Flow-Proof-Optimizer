"""Resolve source hints to declarations and inspect their compiled local binders."""
import argparse
from collections import defaultdict
import gzip
import json
from pathlib import Path
import subprocess
import tempfile

from census import unpack
from source_pairs import matches_declaration_name


def check(obj, rows, scanner):
    info = json.loads(obj.with_suffix(".ilean").read_bytes())
    declarations = defaultdict(set)
    for name, span in info["decls"].items():
        declarations[span[0] + 1].add(name)
        # A preceding docstring can move the declaration start above its identifier.
        if len(span) > 4:
            declarations[span[4] + 1].add(name)
    selected = {}
    for row in rows:
        short = row["theorem"]
        names = [n for n in declarations[row["theorem_line"]]
                 if matches_declaration_name(n, short)
                 and info["decls"][n][2] + 1 >= row.get("last_line", row["first_line"])]
        if len(names) == 1:
            selected[row["first_line"]] = names[0]

    binders = defaultdict(list)
    if selected:
        data = subprocess.check_output([scanner, obj, "--local-lets", *sorted(set(selected.values()))], text=True)
        for name, (binder, (used, size)) in map(json.loads, data.splitlines()):
            binders[name, binder].append([used, size])
    result = []
    for row in rows:
        name = selected.get(row["first_line"])
        result.append(dict(**row, qualified=name, kernel_binders=binders[name, row["name"]]))
    return result


def run(manifest, candidates, artifacts, leantar, scanner, ledger):
    with gzip.open(manifest) as stream:
        tree = json.loads(next(stream))["source_tree"]
        archive = {row[0]: row for row in map(json.loads, stream)}
    by_module = defaultdict(list)
    with candidates.open() as stream:
        for row in map(json.loads, stream):
            by_module[row["file"][:-5].replace("/", ".")].append(row)
    done = set()
    if ledger.exists():
        with ledger.open() as stream:
            for rec in map(json.loads, stream):
                if rec["tree"] != tree:
                    raise ValueError("output belongs to a different source tree")
                done.add(rec["module"])
    pending = [m for m in by_module if m not in done]
    with ledger.open("a") as out:
        for i in range(0, len(pending), 8):
            batch = pending[i:i + 8]
            with tempfile.TemporaryDirectory(prefix="rh-local-have-") as tmp:
                files = unpack([archive[m] for m in batch], artifacts, leantar, tmp)
                for m, obj in zip(batch, files, strict=True):
                    rows = check(obj, by_module[m], scanner)
                    print(json.dumps(dict(tree=tree, module=m, rows=rows), ensure_ascii=False), file=out, flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    for arg in ("manifest", "candidates", "artifacts", "leantar", "scanner", "ledger"):
        parser.add_argument(arg, type=Path)
    run(**vars(parser.parse_args()))
