"""Find local work affected by enclosing proof changes on the same source revision."""
from collections import defaultdict


def module_islands(imports, roots):
    """Connected groups of project modules outside the roots' transitive imports."""
    roots = set(roots)
    if not roots or roots.difference(imports):
        raise ValueError("expected at least one known project root module")
    remaining = set(imports)
    stack = list(roots)
    while stack:
        module = stack.pop()
        if module in remaining:
            remaining.remove(module)
            stack.extend(imports[module])
    neighbors = defaultdict(set)
    for module in remaining:
        for dep in imports[module]:
            if dep in remaining:
                neighbors[module].add(dep)
                neighbors[dep].add(module)
    groups = []
    while remaining:
        group = []
        stack = [remaining.pop()]
        while stack:
            module = stack.pop()
            group.append(module)
            new = neighbors[module] & remaining
            remaining.difference_update(new)
            stack.extend(new)
        groups.append(sorted(group))
    return sorted(groups)


def index_regions(families):
    """Use whole declaration spans for pruning and actual replaced spans for extraction.

    Coordinates are one-based, inclusive source lines. A declaration can have
    several disjoint replaced spans, including spans from different proposals.
    """
    spans = defaultdict(list)
    for family in families:
        file = family["file"]
        for block in family["blocks"]:
            owner = block["name"]
            spans[file, owner, family.get("proposal", owner)].append(
                (block["first_line"], block["last_line"]))
    regions = defaultdict(list)
    for (file, owner, proposal), intervals in spans.items():
        merged = []
        for start, end in sorted(intervals):
            if merged and start <= merged[-1][1] + 1:
                merged[-1] = (merged[-1][0], max(merged[-1][1], end))
            else:
                merged.append((start, end))
        regions[file, owner].extend((start, end, proposal) for start, end in merged)
    return regions


def enclosing_changes(regions, file, site):
    """Return each overlapping proposal and whether it fully contains the local edit."""
    a, b = site["first_line"], site["last_line"]
    overlaps = {}
    for start, end, proposal in regions.get((file, site["qualified"]), ()):
        if start <= b and a <= end:
            overlaps[proposal] = overlaps.get(proposal, False) or (start <= a and b <= end)
    return overlaps


def order_patches(patches):
    """Schedule verified candidates given (name, level, net lines) triples."""
    levels = {"module": 0, "declarations": 1, "derivation": 2, "local": 3}
    return [name for name, level, lines in sorted(
        patches, key=lambda item: (levels[item[1]], -item[2], item[0]))]


def retained_dependencies(dependencies, retained):
    """Return the declarations required by retained callers in a candidate region.

    Keys should identify declarations by module and kernel name. Include a key for
    each declaration under consideration, even when it has no dependencies. Edges
    outside the region are ignored. Pass exported, independently used, registered
    or upstream-covered declarations as appropriate for the particular screen.
    """
    kept = set(retained)
    if not kept.issubset(dependencies):
        raise ValueError("retained declaration outside the candidate region")
    todo = list(kept)
    while todo:
        for callee in dependencies[todo.pop()]:
            if callee in dependencies and callee not in kept:
                kept.add(callee)
                todo.append(callee)
    return kept
