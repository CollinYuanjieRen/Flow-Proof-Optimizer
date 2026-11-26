"""Read module-qualified constant references from Lean's .ilean files."""
import json


def constant_references(info):
    references = info["references"]
    if info["version"] == 5:
        for key, record in references.items():
            constant = json.loads(key).get("c")
            if constant is not None:
                yield constant["m"], constant["n"], record
    elif info["version"] == 6:
        items = iter(references)
        for key, record in zip(items, items, strict=True):
            if key[0] == 0:
                yield key[1], key[2], record
    else:
        raise ValueError(f"unsupported Lean reference format {info['version']}")
