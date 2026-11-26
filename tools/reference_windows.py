"""Nominate same-root derivations that cite the same four project lemmas in order."""
import argparse
from collections import defaultdict
import gzip
from itertools import combinations
import json
from pathlib import Path
import sqlite3

from compiler_references import constant_references
from long_duplicates import tactic_bodies
from root_paths import linked_reachability
from source_pairs import matches_declaration_name


def scan(database, tree, source, library, linked_graph, roots):
    with gzip.open(linked_graph, "rt") as stream:
        graph = dict(map(json.loads, stream))
    masks, _ = linked_reachability(graph.items(), roots, [])
    query = """SELECT m.name, p.name FROM snapshot s JOIN modules m USING(name, rules, sha)
               JOIN proofs p ON p.module_id = m.id WHERE s.tree = ?"""
    with sqlite3.connect(database) as db:
        theorems = set(db.execute(query, (tree,)))
    if not theorems:
        raise ValueError("no theorem records for the requested source tree")
    active = defaultdict(set)
    for module, name in theorems:
        if name in masks and graph[name][0] == module:
            active[module].add(name)

    windows = defaultdict(set)
    parents = 0
    for module, owners in sorted(active.items()):
        rel = Path(*module.split("."))
        info = json.loads((library / rel.with_suffix(".ilean")).read_bytes())
        source_lines = (source / rel.with_suffix(".lean")).read_text().splitlines()
        by_line = defaultdict(list)
        for name in owners & info["decls"].keys():
            by_line[info["decls"][name][4]].append(name)
        refs = defaultdict(set)
        for origin, name, record in constant_references(info):
            if (origin, name) in theorems:
                for use in record["usages"]:
                    if len(use) > 4 and use[4] in owners:
                        refs[use[4]].add((*use[:4], origin, name))
        for short, first, start, end in tactic_bodies(source_lines, 1):
            names = [n for n in by_line[first] if matches_declaration_name(n, short)]
            if len(names) != 1:
                continue
            owner = names[0]
            uses = sorted(u for u in refs[owner] if start <= u[0] < end)
            if len(uses) < 4:
                continue
            parents += 1
            direct = set(graph[owner][1])
            for i in range(len(uses) - 3):
                four = uses[i:i + 4]
                terms = tuple((u[4], u[5]) for u in four)
                if len(set(terms)) == 4 and all(
                    n in direct and graph[n][0] == m for m, n in terms
                ):
                    windows[terms].add((module, owner, four[0][0] + 1, four[-1][2] + 1))
    hints = []
    for terms, sites in sorted(windows.items()):
        for left, right in combinations(sorted(sites), 2):
            shared = masks[left[1]] & masks[right[1]]
            if left[1] != right[1] and shared:
                hints.append(dict(terms=terms, left=left, right=right, root_mask=shared))
    return dict(tree=tree, roots=roots, eligible_parents=parents, hints=hints)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    for arg in ("database", "tree", "source", "library", "linked_graph", "comparator", "output"):
        parser.add_argument(arg, type=str if arg == "tree" else Path)
    args = parser.parse_args()
    roots = json.loads(args.comparator.read_bytes())["theorem_names"]
    result = scan(args.database, args.tree, args.source, args.library, args.linked_graph, roots)
    args.output.write_text(json.dumps(result))
    print(f"{result['eligible_parents']} eligible proofs, {len(result['hints'])} candidate pairs")
