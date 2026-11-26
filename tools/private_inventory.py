"""Check every plain private theorem on an immutable RH source tree, without a size cutoff."""
import argparse
import gzip
import json
from pathlib import Path
import subprocess
import tempfile

from census import unpack
from private_islands import private, unused


def retained_uses(candidates, edges):
    """Return all source roots that must be kept because other kernel terms use them."""
    owners = {}
    for name in edges:
        prefix = name
        while prefix:
            if prefix in candidates:
                owners[name] = prefix
                break
            prefix = prefix.rpartition(".")[0]
    deps = {n: set() for n in candidates}
    live = set()
    for name, refs in edges.items():
        targets = {owners[r] for r in refs if r in owners}
        if name in owners:
            deps[owners[name]].update(targets)
        else:
            live.update(targets)
    todo = list(live)
    while todo:
        extra = deps[todo.pop()] - live
        live.update(extra)
        todo.extend(extra)
    return live


def run(source, manifest, artifacts, leantar, scanner, output):
    with gzip.open(manifest) as stream:
        tree = json.loads(next(stream))["source_tree"]
        entries = list(map(json.loads, stream))
    if subprocess.check_output(["git", "rev-parse", "HEAD:src"], cwd=source, text=True).strip() != tree:
        raise ValueError("source tree differs from the receipt")
    subprocess.run(["git", "diff", "--exit-code", "--quiet", "HEAD", "--", "src"], cwd=source, check=True)
    rows = []
    for entry in entries:
        module = entry[0]
        file = source.joinpath("src", *module.split(".")).with_suffix(".lean")
        text = file.read_text()
        if any(private.match(line) for line in text.splitlines()):
            rows.append(entry)
    print("tree", tree, "compiled modules", len(entries), "modules with plain private theorem syntax", len(rows), flush=True)
    previous = []
    if output.exists():
        with output.open() as existing:
            previous = list(map(json.loads, existing))
    if any(r["tree"] != tree for r in previous):
        raise ValueError("existing private inventory belongs to another source tree")
    completed = {r["file"] for r in previous}
    expected = len(rows)
    rows = [r for r in rows if str(Path(*r[0].split(".")).with_suffix(".lean")) not in completed]
    eligible = sum(r["eligible"] for r in previous)
    dead = sum(len(r["declarations"]) for r in previous)
    deadlines = sum(r["lines"] for r in previous)
    with output.open("a") as report:
        for idx in range(0, len(rows), 16):
            batch = rows[idx:idx + 16]
            with tempfile.TemporaryDirectory(prefix="rh-private-inventory-") as tmp:
                files = unpack(batch, artifacts, leantar, tmp)
                for (module, _, _, _), path in zip(batch, files, strict=True):
                    rel = Path(*module.split(".")).with_suffix(".lean")
                    text = (source / "src" / rel).read_text()
                    info = json.loads(path.with_suffix(".ilean").read_bytes())
                    lines = text.splitlines()
                    total = sum(1 for n, r in info["decls"].items() if n.startswith("_private.")
                                and r[1] == 0 and private.match(lines[r[0]]))
                    eligible += total
                    candidates = unused(text, info)
                    if candidates:
                        out = subprocess.check_output([scanner, path, "--edges"], text=True)
                        edges = dict(map(json.loads, out.splitlines()))
                        if set(candidates) - edges.keys():
                            raise ValueError(f"missing private declaration in {module}")
                        keep = retained_uses(candidates, edges)
                        candidates = {n: v for n, v in candidates.items() if n not in keep}
                    dead += len(candidates)
                    size = sum(b - a + 1 for a, b in candidates.values())
                    deadlines += size
                    print(json.dumps(dict(tree=tree, file=str(rel), eligible=total, lines=size,
                                          declarations=candidates), ensure_ascii=False), file=report)
            report.flush()
            if (idx + len(batch)) % 1024 == 0:
                print("modules checked", idx + len(batch), "eligible", eligible, "candidates", dead, flush=True)
    print("complete", expected, "eligible", eligible, "candidates", dead, "declaration lines", deadlines, flush=True)


if __name__ == "__main__":
    p = argparse.ArgumentParser(description=__doc__)
    for name in ("source", "manifest", "artifacts", "leantar", "scanner", "output"):
        p.add_argument(name, type=Path)
    a = p.parse_args()
    run(a.source, a.manifest, a.artifacts, a.leantar.resolve(), a.scanner.resolve(), a.output)
