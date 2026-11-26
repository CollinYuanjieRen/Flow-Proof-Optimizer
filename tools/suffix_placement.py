"""Find an already imported project module for an identical proof tail.

Read enclosing_suffixes output and the matching compiler census. A proposed host
must itself supply a constant used in the tail and see all its other project
references. The subsequent Lean compilation checks the actual name resolution.
"""
import argparse
from functools import cache
import json
from pathlib import Path
import re
import sqlite3

from census_report import unpack


def suffix_start(lines, first, end):
    start = first - 1
    while start < end and lines[start].startswith(("  letI ", "  haveI ")):
        start += 1
    if start < end and re.match(r"^  [^ ·]", lines[start]):
        return start
    return None


def place_groups(groups, source, library, database, tree):
    with sqlite3.connect(database.resolve().as_uri() + "?mode=ro", uri=True) as db:
        imports = {name: unpack(data) for name, data in db.execute(
            "SELECT s.name, m.imports FROM snapshot s JOIN modules m USING(name,sha,rules) WHERE s.tree=?",
            (tree,),
        )}
    if not imports:
        raise ValueError(f"no compiled modules for source tree {tree}")

    @cache
    def visible(module):
        seen = {module}
        todo = [module]
        while todo:
            for dep in imports[todo.pop()]:
                if dep in imports and dep not in seen:
                    seen.add(dep)
                    todo.append(dep)
        return seen

    for group in groups:
        owners = set()
        deps = set()
        for site in group["sites"]:
            file = Path(site["file"])
            owner = ".".join(file.with_suffix("").parts)
            owners.add(owner)
            lines = (source / file).read_text().splitlines()
            end = site["end"]
            start = suffix_start(lines, site["first"], end)
            if start is None:
                yield {**group, "host": None, "placement": "not a top-level tactic tail"}
                break
            refs = json.loads((library / file).with_suffix(".ilean").read_bytes())["references"]
            for key, info in zip(refs[::2], refs[1::2]):
                if len(key) == 3 and key[1] in imports and any(
                    start <= use[0] < end and use[-1] == site["owner"] for use in info["usages"]
                ):
                    deps.add(key[1])
        else:
            host = next((m for m in sorted(deps - owners)
                         if all(m in visible(owner) for owner in owners) and deps <= visible(m)), None)
            yield {**group, "host": host, "placement": "referenced common module" if host
                   else "no referenced common module", "project_refs": sorted(deps)}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("groups", type=Path, help="JSON list or enclosing_suffixes output")
    parser.add_argument("source", type=Path)
    parser.add_argument("library", type=Path)
    parser.add_argument("database", type=Path)
    parser.add_argument("tree")
    args = parser.parse_args()
    groups = json.loads(args.groups.read_bytes())
    if isinstance(groups, dict):
        groups = groups["enclosing"]
    print(json.dumps(list(place_groups(groups, args.source, args.library, args.database, args.tree))))
