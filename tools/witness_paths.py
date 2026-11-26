"""Check a proposed path using proof bodies and module-qualified elaborator references."""
import json
import subprocess
from functools import cache
from compiler_references import constant_references


def certify(module_file, scanner, routes, root_module="Main", owner_probes=None):
    @cache
    def uses(module):
        path = module_file(module).with_suffix(".ilean")
        data = json.loads(path.read_bytes())
        uses = {}
        unassigned = {}
        declarations_by_name = {}
        for owner, name, ref in constant_references(data):
            declarations_by_name.setdefault(name, set()).add(owner)
            for span in ref["usages"]:
                if len(span) > 4:
                    uses.setdefault((span[4], name), set()).add(owner)
                else:
                    unassigned.setdefault(name, []).append((span, owner))
        return uses, unassigned, data["decls"], declarations_by_name

    @cache
    def local_proof(module, name):
        obj = module_file(module)
        output = subprocess.check_output([scanner, obj, "--proof-info", name], text=True)
        if not output.strip():
            return None
        found, (size, constants) = json.loads(output)
        if found != name:
            raise ValueError(f"missing proof body: {module} {name}")
        return size, set(constants)

    def proof(module, name):
        result = local_proof(module, name)
        if result is None:
            raise ValueError(f"missing proof body: {module} {name}")
        return result

    for route, target_module in routes:
        module = root_module
        steps = []
        for parent, child in zip(route, route[1:]):
            _, constants = proof(module, parent)
            assigned, unassigned, declarations, declarations_by_name = uses(module)
            owners = set(assigned.get((parent, child), ()))
            if parent in declarations:
                bounds = declarations[parent]
                for span, owner in unassigned.get(child, ()):
                    if bounds[:2] <= span[:2] and span[2:4] <= bounds[2:4]:
                        owners.add(owner)
            if child in declarations:
                owners.add(module)
            # Generated local helpers can have a checked body but no source span.
            if not owners and child in constants and local_proof(module, child) is not None:
                owners.add(module)
            # An implicit reference still carries the fully qualified kernel name.
            # Other references in this module can establish its unique owner.
            if not owners and child in constants:
                candidates = declarations_by_name.get(child, ())
                if len(candidates) == 1:
                    owner, = candidates
                    if local_proof(owner, child) is not None:
                        owners.add(owner)
            if not owners and child in constants and owner_probes:
                probe = owner_probes.get((module, child))
                if probe is not None:
                    info = json.loads(probe.read_bytes())
                    if [imp[0] for imp in info["directImports"]] != [module]:
                        raise ValueError(f"lookup probe must import only {module}")
                    resolved = {owner for owner, name, record in constant_references(info)
                                if name == child
                                and any(span[4:] == ["_check"] for span in record["usages"])}
                    if len(resolved) == 1:
                        owner, = resolved
                        if local_proof(owner, child) is not None:
                            owners.add(owner)
            if child not in constants or len(owners) != 1:
                raise ValueError(f"unconfirmed proof-body edge from {module} {parent} to {child}: {owners}")
            steps.append([module, parent])
            module, = owners
        if module != target_module:
            raise ValueError(f"resolved {route[-1]} to {module}, expected {target_module}")
        steps.append([module, route[-1]])
        size, _ = proof(module, route[-1])
        yield {"path": steps, "endpoint_body_expr_objects": size}
