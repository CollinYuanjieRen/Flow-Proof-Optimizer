"""Query checked type/value dependency paths from Main's roots to selected declarations."""
import argparse
from collections import defaultdict, deque
from graphlib import TopologicalSorter
import json
from pathlib import Path
import subprocess


def linked_reachability(rows, roots, targets):
    """Compute root masks and shortest witness paths from LinkedRoots JSONL rows."""
    graph = {name: (module, sorted(edges)) for name, (module, edges) in rows}
    masks = defaultdict(int)
    paths = {}
    for index, root in enumerate(roots):
        parent = {root: None}
        queue = deque([root])
        while queue:
            name = queue.popleft()
            masks[name] |= 1 << index
            for child in graph[name][1]:
                if child not in parent:
                    parent[child] = name
                    queue.append(child)
        paths[root] = {}
        for target in targets:
            if target in parent:
                path = []
                name = target
                while name is not None:
                    path.append([graph[name][0], name])
                    name = parent[name]
                paths[root][target] = path[::-1]
    return dict(masks), paths


def closure(starts, graph):
    seen = set(starts)
    stack = list(seen)
    while stack:
        for dep in graph.get(stack.pop(), ()):
            if dep not in seen:
                seen.add(dep)
                stack.append(dep)
    return seen


def module_slice_many(objects, targets, root):
    # Both directions are needed. A path of kernel references between two
    # project modules must also follow their compiled imports. External packages
    # in this Lake project are upstream of every RH declaration.
    imports, paths = {}, {}
    users = defaultdict(list)
    for path in objects.rglob("*.ilean"):
        info = json.loads(path.read_bytes())
        name = info["module"]
        imports[name] = [imp[0] for imp in info["directImports"]]
        paths[name] = path.relative_to(objects).with_suffix(".olean")
        for dep in imports[name]:
            users[dep].append(name)
    if set(targets) - paths.keys() or root not in paths:
        raise ValueError("missing target or root module in build")

    between = closure(targets, users) & closure([root], imports)
    graph = {m: sorted(set(imports[m]) & between) for m in sorted(between)}
    graph.setdefault(root, [])
    order = list(TopologicalSorter(graph).static_order())
    return [(m, paths[m]) for m in order]


def module_slice(objects, target, root):
    return module_slice_many(objects, [target], root)


def query(scanner, objects, modules, target_module, seeds, root_module, roots):
    # Track a single proof path per reached declaration. Discard each module's
    # unrelated expressions after propagating its local dependencies.
    if target_module not in {m for m, _ in modules}:
        # An independent module may define the same public name. Validate the
        # requested names there, without connecting its declarations to Main.
        path = objects.joinpath(*target_module.split(".")).with_suffix(".olean")
        result = subprocess.run([scanner, path, "--edges"], capture_output=True, text=True, check=True)
        names = {json.loads(line)[0] for line in result.stdout.splitlines()}
        if missing := set(seeds) - names:
            raise ValueError(f"missing seed declarations: {missing}")
    parent = {}
    for m, path in modules:
        proc = subprocess.run([scanner, objects / path, "--edges"],
                              capture_output=True, text=True, check=True)
        ds = dict(map(json.loads, proc.stdout.splitlines()))
        if m == target_module:
            if missing := set(seeds) - ds.keys():
                raise ValueError(f"missing seed declarations: {missing}")
            parent.update(dict.fromkeys(seeds))
        if m == root_module and (missing := set(roots) - ds.keys()):
            raise ValueError(f"missing root declarations: {missing}")
        local_users = defaultdict(list)
        queue = [d for d in ds if d in parent]
        for decl, deps in ds.items():
            for ref in deps:
                if ref in ds:
                    local_users[ref].append(decl)
                if ref in parent and decl not in parent:
                    parent[decl] = ref
                    queue.append(decl)
        while queue:
            ref = queue.pop()
            for decl in local_users[ref]:
                if decl not in parent:
                    parent[decl] = ref
                    queue.append(decl)
    result = {}
    for root in roots:
        route = []
        if root in parent:
            node = root
            while node is not None:
                route.append(node)
                node = parent[node]
        result[root] = route
    return result


if __name__ == "__main__":
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("objects", type=Path, help="project .lake/build/lib/lean on the selected revision")
    p.add_argument("scanner", type=Path)
    p.add_argument("target_module")
    p.add_argument("names", type=Path, help="one fully qualified target declaration per line")
    p.add_argument("--root-module", default="Main")
    p.add_argument("--roots", nargs="+", required=True)
    args = p.parse_args()
    modules = module_slice(args.objects, args.target_module, args.root_module)
    print(json.dumps(query(args.scanner.resolve(), args.objects, modules, args.target_module,
                           args.names.read_text().splitlines(), args.root_module, args.roots), ensure_ascii=False))
