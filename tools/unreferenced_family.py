"""Find local source theorems used exclusively by an unreferenced theorem.

The result is a candidate family. Recompile its removal and check references
to the actual missing kernel constants, including generated declarations.
"""
import argparse
from collections import defaultdict
import json
from pathlib import Path
import sqlite3

from census_report import unpack
from source_pairs import header, matches_declaration_name


def source_declarations(source, info):
    lines = source.read_text().splitlines()
    declarations = {}
    for name, (start, _, end, _, *identifier) in info["decls"].items():
        theorem_line = start
        if identifier and identifier[0] > start and lines[start].lstrip().startswith("/--"):
            name_line = identifier[0]
            prefix = "\n".join(lines[start:name_line]).strip()
            if prefix.endswith("-/") and prefix.count("/-") == prefix.count("-/") == 1:
                theorem_line = name_line
        match = header.match(lines[theorem_line])
        if match and matches_declaration_name(name, match[1]):
            declarations[name] = dict(name=name, theorem=match[1],
                                      first_line=start+1, last_line=end+1)
            if theorem_line != start:
                declarations[name]["theorem_line"] = theorem_line+1
    return declarations


def deletion_range(lines, declaration):
    """Return a half-open source interval, including single-line scoped section commands."""
    first = declaration["first_line"] - 1
    stop = declaration["last_line"]
    while first > 0:
        previous = lines[first - 1].rstrip()
        if not (previous.startswith(("omit ", "include ")) and previous.endswith(" in")):
            break
        first -= 1
    if stop < len(lines) and not lines[stop].strip():
        stop += 1
    return first, stop


def families(database, tree, requests):
    """Answer multiple source/ilean/root requests in one global reference scan.

    A result of None means a retained caller was found for the requested root.
    The graph is restricted to each root's own module when adding its helpers.
    """
    modules_for_roots = []
    declarations = {}
    modules_by_file = {}
    for source, ilean, root in requests:
        if ilean not in modules_by_file:
            info = json.loads(ilean.read_bytes())
            module = info["module"]
            declarations[module] = source_declarations(source, info)
            modules_by_file[ilean] = module
        modules_for_roots.append((modules_by_file[ilean], root))
    return families_from_declarations(database, tree, modules_for_roots, declarations)


def families_from_declarations(database, tree, modules_for_roots, declarations):
    """Use previously resolved source spans for a batch of (module, root) pairs."""
    groups = [(module, (root,)) for module, root in modules_for_roots]
    return combined_families(database, tree, groups, declarations)


def combined_families(database, tree, groups, declarations):
    """Close each group of roots in one module under exclusively used helpers."""
    groups = list(groups)
    for module, roots in groups:
        if not roots or not set(roots) <= declarations[module].keys():
            raise ValueError(f"missing source theorem in {module}: {roots}")
    owners = defaultdict(list)
    users = defaultdict(set)
    dependencies = defaultdict(set)
    external = set()
    with sqlite3.connect(database) as db:
        modules = dict(db.execute("""
            SELECT s.name,m.id FROM snapshot s LEFT JOIN modules m USING(rules,sha,name)
            WHERE s.tree=?
        """, (tree,)))
        if not modules or any(mid is None for mid in modules.values()):
            raise ValueError("a complete compiled snapshot is required")

        def edges(mid):
            data, = db.execute("SELECT edges FROM modules WHERE id=?", (mid,)).fetchone()
            return unpack(data)

        local = {}
        for module, names in declarations.items():
            private_prefix = "_private." + module + ".0."
            local[module] = {}
            for name, _ in edges(modules[module]):
                for spelling in (name, name.removeprefix(private_prefix)):
                    prefix = spelling
                    while prefix and prefix not in names:
                        prefix = prefix.rpartition(".")[0]
                    if prefix:
                        owner = (module, prefix)
                        local[module][name] = owner
                        owners[name].append(owner)
                        break
        for mod, mid in modules.items():
            local_owners = local.get(mod, {})
            for caller, refs in edges(mid):
                owner = local_owners.get(caller)
                for ref in refs:
                    for callee in owners.get(ref, ()):
                        if owner == callee:
                            continue
                        if owner is None or mod != callee[0]:
                            external.add(callee)
                        else:
                            users[callee].add(owner)
                            dependencies[owner].add(callee)
    results = []
    for module, roots in groups:
        selected = {(module, root) for root in roots}
        if any(key in external or not users[key] <= selected for key in selected):
            results.append(None)
            continue
        while True:
            new = {n for caller in selected for n in dependencies[caller]
                   if n not in selected and n not in external and users[n] <= selected}
            if not new:
                break
            selected.update(new)
        names = declarations[module]
        results.append([dict(**names[n], callers=sorted(c[1] for c in users[(module, n)]))
                        for _, n in sorted(selected, key=lambda k: names[k[1]]["first_line"])])
    return results


def independent_removals(blocks, eligible):
    """Largest caller-closed subset of a checked family permitted by overlap or interface rules.

    blocks are from combined_families, which already checks external references.
    Each retained caller keeps all its dependencies alive. Every other eligible
    declaration can be removed together, subject to the usual Lean replay.
    """
    removable = {block["name"] for block in blocks}.intersection(eligible)
    dependencies = defaultdict(list)
    keep = []
    for block in blocks:
        name = block["name"]
        if name not in removable:
            continue
        for caller in block["callers"]:
            dependencies[caller].append(name)
            if caller not in removable:
                keep.append(name)
    while keep:
        name = keep.pop()
        if name in removable:
            removable.remove(name)
            keep.extend(dependencies[name])
    return [block for block in blocks if block["name"] in removable]


def exclusive_imported_dependencies(database, tree, groups, protected=()):
    """Find directly referenced project constants used only by one deletion group.

    Each module supplies the exact kernel names selected for removal. An
    unlisted compiler auxiliary counts as a retained caller. The result gives
    the consumer module, provider module, dependency and actual caller names.
    Source ranges, registration and rewrite eligibility are checked separately.
    """
    protected = set(protected)
    groups = {module: set(names) for module, names in groups.items()}
    with sqlite3.connect(database) as db:
        modules = dict(db.execute("""
            SELECT s.name,m.id FROM snapshot s LEFT JOIN modules m USING(rules,sha,name)
            WHERE s.tree=?
        """, (tree,)))
        if not modules or None in modules.values():
            raise ValueError("a complete compiled snapshot is required")

        def edges(module):
            blob, = db.execute("SELECT edges FROM modules WHERE id=?", (modules[module],)).fetchone()
            return unpack(blob)

        consumers = defaultdict(set)
        callers = defaultdict(set)
        for module, selected in groups.items():
            found = set()
            for name, refs in edges(module):
                if name in selected:
                    found.add(name)
                    for ref in refs:
                        consumers[ref].add(module)
                        callers[ref].add(name)
            if found != selected:
                raise ValueError(f"unknown selected declaration in {module}")

        candidates = {name: next(iter(users)) for name, users in consumers.items()
                      if len(users) == 1 and name not in protected}
        providers = {}
        excluded = set()
        for module in modules:
            selected = groups.get(module, ())
            for name, refs in edges(module):
                if name in candidates:
                    if name in providers:
                        excluded.add(name)
                    providers[name] = module
                owner = module if name in selected else None
                for ref in refs:
                    if ref in candidates and candidates[ref] != owner:
                        excluded.add(ref)
    return sorted((consumer, providers[name], name, sorted(callers[name]))
                  for name, consumer in candidates.items()
                  if name in providers and providers[name] != consumer and name not in excluded)


def family(database, tree, source, ilean, root):
    result, = families(database, tree, [(source, ilean, root)])
    if result is None:
        raise ValueError("root has a retained caller")
    return result


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    for arg in ("database", "source", "ilean"):
        parser.add_argument(arg, type=Path)
    parser.add_argument("tree")
    parser.add_argument("root")
    args = parser.parse_args()
    print(json.dumps(family(args.database, args.tree, args.source, args.ilean, args.root),
                     ensure_ascii=False))
