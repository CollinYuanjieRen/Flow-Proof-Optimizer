"""Propose cross-module sharing for a preselected family of matching private proofs.

The scheduler supplies old name pairs after exact comparison, common-root checks
and upstream deduplication. Re-elaborate the output and replay those paths.
"""
from collections import defaultdict
import argparse
import difflib
import json
import sys
from pathlib import Path

from private_duplicate import source_span


def plain_name(module, name):
    prefix = f"_private.{module}.0."
    if not name.startswith(prefix):
        raise ValueError(f"expected a private declaration of {module}: {name}")
    return name[len(prefix):]


def add_import(source, module):
    lines = source.splitlines(keepends=True)
    for line in lines:
        if line.strip() in {f"import {module}", f"public import {module}"}:
            return source
    # Preserve the order of the existing imports, including in unclumped headers.
    index = max(i for i, line in enumerate(lines) if line.startswith(("public import ", "import ")))
    lines.insert(index + 1, f"import {module}\n")
    return "".join(lines)


def clump_members(source, lines):
    members = {}
    current = None
    for i, line in enumerate(source.splitlines()):
        if line.startswith("-- ===== clump member: "):
            current = line.removeprefix("-- ===== clump member: ").removesuffix(" =====")
        elif line.startswith("-- ===== end clump member: "):
            current = None
        if current and i in lines:
            members[i] = current
    return members


def rewritten(source, info, pairs, provider, promote, shared_names, origins, *, import_provider=True):
    if info["version"] != 6:
        raise ValueError("expected version 6 Lean reference data")
    module = info["module"]
    span = source_span(source)
    edits = {}
    removed = []
    needs_import = defaultdict(set)
    for anchor, duplicate in pairs:
        name = anchor if promote else duplicate
        plain_name(module, name)
        decl = info["decls"][name]
        start, end = span(decl)
        name_start, name_end = span(decl[4:])
        forms = {"private theorem ", "private lemma "}
        if not promote:
            forms.add("private noncomputable def ")
        if (source[start:name_start] not in forms
                or source[name_start:name_end] != name.rsplit(".", 1)[-1]):
            raise ValueError(f"unsupported declaration syntax: {name}")
        if promote:
            edits[start, start + len("private ")] = "protected "
            if "." not in plain_name(module, name):
                namespace, _, _ = shared_names[anchor].rpartition(".")
                if not namespace:
                    raise ValueError(f"choose a namespace for this root-level helper: {anchor}")
                edits[name_start, name_start] = namespace + "."
        else:
            # A line such as "omit [Instance X] in" applies only to this command.
            # Leaving it in place can change the type of the following theorem.
            while start and source[start - 1] == "\n":
                previous = source.rfind("\n", 0, start - 1) + 1
                line = source[previous:start - 1]
                if not (line.startswith("omit ") and line.rstrip().endswith(" in")):
                    break
                start = previous
            if source[end:end + 2] == "\n\n":
                end += 2
            edits[start, end] = ""
            removed.append((start, end))

    refs = iter(info["references"])
    uses = {key[-1]: entry["usages"] for key, entry in zip(refs, refs, strict=True)
            if key[:2] == [0, module]}
    for anchor, duplicate in pairs:
        name = anchor if promote else duplicate
        old = plain_name(module, name).split(".")
        new = shared_names[anchor].split(".")
        # A protected helper requires a qualified reference even within its namespace.
        i = 0
        while anchor.startswith("_private.") and i < min(len(old) - 1, len(new) - 2) and old[i] == new[i]:
            i += 1
        for ref in uses.get(name, ()):
            start, end = span(ref)
            if any(a <= start and end <= b for a, b in removed):
                continue
            if source[start:end] != old[-1]:
                raise ValueError(f"unsupported reference spelling: {name}")
            edits[start, end] = ".".join(new[i:])
            if not promote:
                needs_import[ref[0]].add(origins[anchor])

    result = source
    for (start, end), replacement in sorted(edits.items(), reverse=True):
        result = result[:start] + replacement + result[end:]
    if promote:
        return result

    # Unclumping restores per-member imports from these headers.
    member_imports = defaultdict(set)
    for i, member in clump_members(source, needs_import).items():
        member_imports[member].update(needs_import[i])
    tag = "-- clump-header: "
    lines = result.splitlines(keepends=True)
    for i, line in enumerate(lines):
        if line.startswith(tag):
            metadata = json.loads(line[len(tag):])
            if metadata["m"] in member_imports:
                for dependency in sorted(member_imports[metadata["m"]], reverse=True):
                    metadata["h"] = add_import(metadata["h"], dependency)
                lines[i] = tag + json.dumps(metadata, ensure_ascii=False) + "\n"
    result = "".join(lines)
    return add_import(result, provider) if import_provider else result


def propose(sources, objects, provider, consumer, pairs, root_namespaces=None):
    if provider == consumer or not pairs or len({old for _, old in pairs}) != len(pairs):
        raise ValueError("expected two different modules and distinct declarations to remove")
    shared_names = {}
    for anchor, _ in pairs:
        if not anchor.startswith("_private."):
            shared_names[anchor] = anchor
            continue
        name = plain_name(provider, anchor)
        if "." not in name:
            namespace = (root_namespaces or {}).get(anchor)
            if not namespace:
                raise ValueError(f"choose a namespace for this root-level helper: {anchor}")
            name = f"{namespace}.{name}"
        shared_names[anchor] = name

    origins = {}
    patch = []
    lines_saved = bytes_saved = 0
    for module in (provider, consumer):
        rel = Path(*module.split(".")).with_suffix(".lean")
        source = (sources / rel).read_text()
        info = json.loads((objects / rel).with_suffix(".ilean").read_bytes())
        if info["module"] != module:
            raise ValueError(f"wrong reference data for {module}")
        if module == provider:
            locations = {name: info["decls"][name][0] for name in shared_names}
            members = clump_members(source, set(locations.values()))
            origins = {name: members.get(i, provider) for name, i in locations.items()}
        selected = pairs
        if module == provider:
            selected = [(a, d) for a, d in pairs if a.startswith("_private.")]
            if not selected:
                continue
        result = rewritten(source, info, selected, provider, module == provider, shared_names, origins)
        lines_saved += source.count("\n") - result.count("\n")
        bytes_saved += len(source.encode()) - len(result.encode())
        patch.extend(difflib.unified_diff(source.splitlines(True), result.splitlines(True),
                     fromfile=f"a/src/{rel}", tofile=f"b/src/{rel}"))
    if min(lines_saved, bytes_saved) <= 0:
        raise ValueError("the complete patch must reduce both source lines and bytes")
    return patch


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("sources", type=Path)
    parser.add_argument("objects", type=Path)
    parser.add_argument("family", type=Path, help="JSON with keep and drop module names and selected name pairs")
    args = parser.parse_args()
    family = json.loads(args.family.read_text())
    sys.stdout.writelines(propose(args.sources, args.objects, family["keep"], family["drop"], family["pairs"],
                                  family.get("root_namespaces")))
