"""Recheck compiled types, proofs and root paths after replacing exact copies."""
from collections import defaultdict
import json
import subprocess

from witness_paths import certify


def check_sharing(replacements, paths, before_file, after_file, partition, scanner):
    """Map each (old module, name) to its shared (new module, name)."""
    endpoints = sorted(set(replacements.values()))
    groups = {endpoint: i for i, endpoint in enumerate(endpoints)}
    requests = defaultdict(list)
    expected = {}
    objects = [(before_file(m), n, target) for (m, n), target in replacements.items()]
    objects += [(after_file(m), n, (m, n)) for m, n in endpoints]
    for index, (obj, name, target) in enumerate(objects):
        group = groups[target]
        expected[index] = group
        requests[obj].append(dict(group=group, index=index, name=name))
    first, *rest = requests
    raw = subprocess.check_output([partition, first, "--partition", *rest],
                                  input=json.dumps(list(requests.values())), text=True)
    reps = defaultdict(set)
    for line in raw.splitlines():
        group, index, rep = json.loads(line)
        if expected.pop(index) != group:
            raise ValueError(f"wrong structural comparison group for {index}")
        reps[group].add(rep)
    if expected or any(len(reps[i]) != 1 for i in groups.values()):
        raise ValueError("shared type or proof structure did not match every original")

    routes = []
    witnessed = set()
    for path in paths:
        old = tuple(path[-1])
        target = replacements[old]
        witnessed.add(old)
        route = [replacements.get((m, n), (m, n))[1] for m, n in path]
        routes.append((route, target[0]))
    if witnessed != replacements.keys():
        raise ValueError("missing root witness for an original declaration")
    return list(certify(after_file, scanner, routes))
