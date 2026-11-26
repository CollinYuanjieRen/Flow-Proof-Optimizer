"""Nominate same-module lemmas by the project constants in their conclusions.

Run inside the project's Lake environment. Supply corresponding Lean source and
olean files. Results may require new premises, a rewrite, or moving a later lemma.
"""
import argparse
from collections import defaultdict
from fractions import Fraction
import json
from pathlib import Path
import subprocess

from source_pairs import declaration_spelling


def reachable(root, edges):
    seen = {root}
    pending = [root]
    while pending:
        for child in edges.get(pending.pop(), ()):
            if child not in seen:
                seen.add(child)
                pending.append(child)
    return seen


def candidates(source, obj, target, namespace, scanner=None):
    command = [str(scanner)] if scanner else [
        "lake", "env", "lean", "-j1", "--run", str(Path(__file__).with_name("ProofPairs.lean").resolve())
    ]
    output = subprocess.check_output([*command, str(obj), "--result-providers"], text=True)
    lines = source.read_text().splitlines()
    positions = json.loads(obj.with_suffix(".ilean").read_bytes())["decls"]
    graph = {}
    symbols = {}
    for name, (edges, result) in map(json.loads, output.splitlines()):
        graph[name] = edges
        if result is not None and name in positions and declaration_spelling(lines, name, positions[name]):
            symbols[name] = {n for n in result if n.startswith(namespace + ".")}
    goal = symbols[target]
    parents = defaultdict(list)
    for name, edges in graph.items():
        for dep in edges:
            if dep in graph:
                parents[dep].append(name)
    blocked = reachable(target, parents)
    used = reachable(target, graph)
    ranked = []
    for name in symbols.keys() - blocked:
        common = goal & symbols[name]
        if common:
            score = Fraction(len(common), len(goal | symbols[name]))
            ranked.append((score, name))
    ranked.sort(key=lambda pair: (-pair[0], pair[1]))
    return {"target": target, "eligible": len(symbols.keys() - blocked),
            "candidates": [{"name": name, "score": str(score), "alreadyReferenced": name in used}
                           for score, name in ranked]}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path)
    parser.add_argument("olean", type=Path)
    parser.add_argument("target", help="fully qualified compiled theorem name")
    parser.add_argument("--namespace", required=True, help="project namespace, for example New")
    parser.add_argument("--scanner", type=Path, help="compiled ProofPairs executable")
    args = parser.parse_args()
    print(json.dumps(candidates(args.source, args.olean, args.target, args.namespace, args.scanner)))
