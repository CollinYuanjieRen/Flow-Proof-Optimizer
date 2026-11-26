"""Index every compiled RH module in an immutable upstream receipt. Resume by artifact hash."""
import argparse
import gzip
import hashlib
import json
import os
from pathlib import Path
import sqlite3
import subprocess
import tempfile
from time import monotonic
import zlib


def pack(value):
    return zlib.compress(json.dumps(value, separators=(",", ":"), ensure_ascii=False).encode(), 1)


def unpack(batch, artifacts, leantar, directory, *, workers=1):
    jobs, files = [], []
    for i, (module, key, archive, sha) in enumerate(batch):
        obj = artifacts / archive
        if hashlib.sha256(obj.read_bytes()).hexdigest() != sha:
            raise ValueError(f"artifact checksum mismatch: {module}")
        dest = Path(directory) / str(i)
        dest.mkdir()
        jobs.append(dict(file=str(obj), hash=key, base=[str(dest), str(dest)]))
        files.append((dest / module.split(".")[-1]).with_suffix(".olean"))
    # Use the RH cache client's Rust stack setting for large compressed Lean terms.
    env = {**os.environ, "RUST_MIN_STACK": str(max(8388608, int(os.environ.get("RUST_MIN_STACK", 0))))}
    subprocess.run([leantar, "--jobs", str(workers), "-f", "-x", "-j", "-"],
                   input=json.dumps(jobs), text=True, check=True, env=env)
    return files


def run(manifest, artifacts, scanner, leantar, ledger, limit=None):
    with gzip.open(manifest) as stream:
        identity = json.loads(next(stream))
        entries = list(map(json.loads, stream))
    rules = hashlib.sha256(scanner.read_bytes()).hexdigest()
    with sqlite3.connect(ledger) as db:
        db.executescript("""
            CREATE TABLE IF NOT EXISTS modules(
                id INTEGER PRIMARY KEY, rules TEXT, name TEXT, sha TEXT,
                imports BLOB, edges BLOB, UNIQUE(rules, name, sha));
            CREATE TABLE IF NOT EXISTS proofs(
                module_id INTEGER, name TEXT, arity INTEGER, type_hash TEXT, body_hash TEXT);
            CREATE TABLE IF NOT EXISTS snapshot(
                tree TEXT, rules TEXT, name TEXT, sha TEXT, PRIMARY KEY(tree,rules,name));
        """)
        tree = identity["source_tree"]
        # A dependency update can change compiled proofs without changing src.
        # Keep the source-tree lookup current and the build-specific lookup pinned.
        for key in {tree, identity.get("input_fingerprint", tree)}:
            db.execute("DELETE FROM snapshot WHERE tree=? AND rules=?", (key, rules))
            db.executemany("INSERT INTO snapshot VALUES(?,?,?,?)",
                           ((key, rules, m, s) for m, _, _, s in entries))
        db.commit()
        done = set(db.execute("SELECT name,sha FROM modules WHERE rules=?", (rules,)))
        todo = [row for row in entries if (row[0], row[3]) not in done]
        print("tree", tree, "modules", len(entries), "pending", len(todo), flush=True)
        start = monotonic()
        if limit is not None:
            todo = todo[:limit]
        for index in range(0, len(todo), 16):
            batch = todo[index:index + 16]
            with tempfile.TemporaryDirectory(prefix="rh-proof-census-") as directory:
                files = unpack(batch, artifacts, leantar, directory)
                out = subprocess.check_output([scanner, files[0], "--census", *files[1:]], text=True)
                # Empty modules produce a delimiter just like nonempty modules.
                blocks, block = [], []
                for line in out.splitlines():
                    if line:
                        block.append(json.loads(line))
                    else:
                        blocks.append(block)
                        block = []
                if block:
                    raise ValueError("incomplete final module")
                with db:
                    for (module, _, _, sha), path, rows in zip(batch, files, blocks, strict=True):
                        ilean = json.loads(path.with_suffix(".ilean").read_bytes())
                        if ilean["module"] != module:
                            raise ValueError(f"compiled module identity mismatch: {module}")
                        edges = [(name, deps) for name, _, deps in rows]
                        imports = [imp[0] for imp in ilean["directImports"]]
                        mid = db.execute("INSERT INTO modules(rules,name,sha,imports,edges) VALUES(?,?,?,?,?)",
                                         (rules, module, sha, pack(imports), pack(edges))).lastrowid
                        db.executemany("INSERT INTO proofs VALUES(?,?,?,?,?)",
                                       ((mid, n, *sig) for n, sig, _ in rows if sig is not None))
            if (index + len(batch)) % 1024 == 0 or index + len(batch) == len(todo):
                print("newly indexed", index + len(batch), "elapsed_s", round(monotonic() - start, 1), flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    for arg in ("manifest", "artifacts", "scanner", "leantar", "ledger"):
        parser.add_argument(arg, type=Path)
    parser.add_argument("--max-modules", type=int, help="optional pilot batch")
    args = parser.parse_args()
    run(args.manifest, args.artifacts, args.scanner.resolve(), args.leantar.resolve(),
        args.ledger, args.max_modules)
