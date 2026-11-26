"""Propose replacing a private forwarding theorem with its existing public target."""
import argparse
import difflib
import json
from pathlib import Path
import re
import subprocess
import sys

from private_duplicate import source_span
from share_private import plain_name


def rewrite(source, info, wrapper, target):
    module = info["module"]
    name = plain_name(module, wrapper)
    if target.startswith("_private."):
        raise ValueError("the target must be accessible to the callers")
    decl = info["decls"][wrapper]
    span = source_span(source)
    begin, end = span(decl)
    name_start, name_end = span(decl[4:])
    prefix = source[begin:name_start]
    if prefix.startswith("/--"):
        comment, sep, prefix = prefix.partition("-/")
        if not sep or "/-" in comment[3:]:
            raise ValueError("unsupported documentation comment")
        prefix = prefix.lstrip()
    if prefix not in ("private theorem ", "private lemma "):
        raise ValueError("expected an undecorated private theorem")

    def matches(spelling):
        return spelling == name or name.endswith("." + spelling)

    if not matches(source[name_start:name_end]):
        raise ValueError("declaration name does not match the compiler range")
    # Dropping a scoped command can change the interpretation of its successor.
    previous = source[:begin].rstrip().rsplit("\n", 1)[-1]
    if re.search(r"\bin$", previous):
        raise ValueError("scoped command needs a separate edit")
    if source[end:end + 2] == "\n\n":
        end += 2
    edits = {(begin, end): ""}
    refs = iter(info["references"])
    for key, record in zip(refs, refs, strict=True):
        if key != [0, module, wrapper]:
            continue
        for use in record["usages"]:
            a, b = span(use)
            if begin <= a and b <= end:
                continue
            if not matches(source[a:b]):
                raise ValueError("reference spelling does not match the resolved name")
            edits[a, b] = target
    for (a, b), replacement in sorted(edits.items(), reverse=True):
        source = source[:a] + replacement + source[b:]
    return source


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    for arg in ("source", "object", "provider", "scanner"):
        parser.add_argument(arg, type=Path)
    parser.add_argument("wrapper")
    parser.add_argument("target")
    args = parser.parse_args()
    subprocess.run([args.scanner, args.object, "--check-forward", args.provider,
                    args.wrapper, args.target], check=True, stdout=subprocess.DEVNULL)
    src = args.source.read_text()
    info = json.loads(args.object.with_suffix(".ilean").read_bytes())
    result = rewrite(src, info, args.wrapper, args.target)
    sys.stdout.writelines(difflib.unified_diff(src.splitlines(True), result.splitlines(True),
                                              fromfile=str(args.source), tofile=str(args.source)))
