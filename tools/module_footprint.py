"""Measure the reachable compiled bodies of a single-module rewrite.

Use the unmodified project's LinkedRoots graph and root list
(from comparator.json), and a ProofPairs scanner compatible with both oleans.
External witnesses are direct references in other baseline project modules.
"""

import argparse
import gzip
import json
from pathlib import Path
import sqlite3
import subprocess

from census_report import unpack
from root_paths import closure, linked_reachability


def measure(scanner, obj, entries):
    def scan(*args):
        return subprocess.check_output([scanner, obj, *args], text=True).splitlines()

    edges = dict(map(json.loads, scan("--edges")))
    missing = entries - edges.keys()
    if missing:
        raise ValueError(f"{obj} is missing reachable entry points: {sorted(missing)}")
    dependencies = closure(entries, edges)
    names = sorted(dependencies & edges.keys())
    bodies = [json.loads(line)[0] for line in scan("--proof-info", *names)]
    stats = subprocess.check_output(
        [scanner, "--footprint"], input=json.dumps([[str(obj), bodies]]), text=True
    )
    return {"names": bodies, "stats": json.loads(stats)}, dependencies - edges.keys()


def external_witnesses(census, manifest, module, masks, roots, wanted):
    found = {}
    if not wanted:
        return found
    with gzip.open(manifest, "rt") as stream:
        tree = json.loads(next(stream))["input_fingerprint"]
    query = """SELECT m.name, m.edges FROM snapshot s JOIN modules m USING(rules, name, sha)
               WHERE s.tree = ? AND m.name != ?"""
    all_roots = (1 << len(roots)) - 1
    with sqlite3.connect(census.resolve().as_uri() + "?mode=ro", uri=True) as db:
        for owner_module, data in db.execute(query, (tree, module)):
            for owner, refs in unpack(data):
                if masks.get(owner) == all_roots:
                    for name in wanted.intersection(refs):
                        found.setdefault(name, [owner_module, owner])
            if len(found) == len(wanted):
                break
    return found


def compare(args):
    roots = json.loads(args.comparator.read_bytes())["theorem_names"]
    with gzip.open(args.graph, "rt") as stream:
        graph = dict(map(json.loads, stream))
    masks, paths = linked_reachability(graph.items(), roots, args.targets)
    entries = {root for root in roots if graph[root][0] == args.module}
    entries.update(child for owner in masks if graph[owner][0] != args.module
                   for child in graph[owner][1] if graph[child][0] == args.module)
    before, old_refs = measure(args.scanner, args.before, entries)
    after, new_refs = measure(args.scanner, args.after, entries)
    added = new_refs - old_refs
    witnesses = external_witnesses(args.census, args.manifest, args.module, masks, roots, added)
    return {"paths": paths, "entries": sorted(entries), "before": before, "after": after,
            "newOffmodule": sorted(added), "outsideWitnesses": witnesses}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("scanner", "graph", "comparator", "census", "manifest", "before", "after"):
        parser.add_argument("--" + name, type=Path, required=True)
    parser.add_argument("--module", required=True)
    parser.add_argument("targets", nargs="+", help="target names for baseline root paths")
    print(json.dumps(compare(parser.parse_args())))
