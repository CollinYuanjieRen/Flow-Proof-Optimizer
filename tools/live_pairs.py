"""Find candidate common-root paths for structurally verified theorem pairs.

Input JSON is a list of records with left/right [module, declaration] endpoints.
Read each module in the combined import slice once and keep one path per root.
This inexpensive name-based pass includes types. Before rewriting, replay both
paths with witness_paths.certify to check proof bodies and defining modules.
"""
import argparse
from collections import defaultdict
import json
from pathlib import Path
import subprocess

from root_paths import module_slice_many


def module_edges(scanner, objects, modules, overlay):
    # Amortize Lean process startup while bounding the lifetime of mmap regions.
    for start in range(0, len(modules), 16):
        batch = modules[start:start + 16]
        files = [overlay / p if overlay and (overlay / p).is_file() else objects / p
                 for _, p in batch]
        result = subprocess.run([scanner, files[0], "--edge-batch", *files[1:]],
                                capture_output=True, text=True, check=True)
        blocks = []
        ds = {}
        for line in result.stdout.splitlines():
            if line:
                name, deps = json.loads(line)
                ds[name] = deps
            else:
                blocks.append(ds)
                ds = {}
        for (module, _), decls in zip(batch, blocks, strict=True):
            yield module, decls


def classify(scanner, objects, modules, roots, pairs, overlay=None):
    targets = defaultdict(set)
    for pair in pairs:
        for module, name in (pair["left"], pair["right"]):
            targets[module].add(name)
    # Each predecessor is closer to its own root. Independent witnesses prevent
    # combining a path to the left from one theorem and to the right from another.
    parents = {root: {root: None} for root in roots}
    for module, ds in module_edges(scanner, objects, modules[::-1], overlay):
        if missing := targets[module] - ds.keys():
            raise ValueError(f"missing declarations in {module}: {missing}")
        if module == modules[-1][0] and (missing := set(roots) - ds.keys()):
            raise ValueError(f"missing roots in {module}: {missing}")
        for pred in parents.values():
            todo = [name for name in ds if name in pred]
            while todo:
                name = todo.pop()
                for dep in ds[name]:
                    if dep not in pred:
                        pred[dep] = name
                        if dep in ds:
                            todo.append(dep)
    incorporated = {module for module, _ in modules}

    def paths(endpoint):
        module, name = endpoint
        if module not in incorporated:
            return {}
        result = {}
        for root, pred in parents.items():
            if name in pred:
                route = [name]
                while (parent := pred[route[-1]]) is not None:
                    route.append(parent)
                result[root] = route[::-1]
        return result

    for pair in pairs:
        a, b = paths(pair["left"]), paths(pair["right"])
        yield {**pair, "candidate_roots": sorted(a.keys() & b.keys()), "left_paths": a, "right_paths": b}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("objects", type=Path)
    parser.add_argument("scanner", type=Path)
    parser.add_argument("pairs", type=Path)
    parser.add_argument("--root-module", default="Main")
    parser.add_argument("--roots", nargs="+", required=True)
    args = parser.parse_args()
    pairs = json.loads(args.pairs.read_text())
    targets = {p[key][0] for p in pairs for key in ("left", "right")}
    modules = module_slice_many(args.objects, targets, args.root_module)
    for row in classify(args.scanner.resolve(), args.objects, modules, args.roots, pairs):
        print(json.dumps(row, ensure_ascii=False))
