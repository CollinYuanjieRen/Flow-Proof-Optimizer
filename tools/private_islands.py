"""Rank modules by lines in plain private theorems with no indexed live use."""
import argparse
import difflib
from collections import defaultdict
import json
from pathlib import Path
import re
import subprocess
import sys

from source_pairs import command
from compiler_references import constant_references

private = re.compile(r"private (?:theorem|lemma) ")
scoped_variables = re.compile(r"(?:omit|include)(?:[ \t]+(?:[\w']+|\[[^\[\]\n/]+\]))+[ \t]+in[ \t]*")
scoped_open = re.compile(r"open(?:[ \t]+[\w'.]+)+[ \t]+in[ \t]*")
scoped_instance = re.compile(r"attribute[ \t]+\[local instance\](?:[ \t]+[\w'.]+)+[ \t]+in[ \t]*")


def unused(source, data):
    lines = source.splitlines()
    spans = {n: (r[0], r[2]) for n, r in data["decls"].items()
             if n.startswith("_private.") and r[1] == 0 and private.match(lines[r[0]])}
    used_by = defaultdict(set)
    for module, name, info in constant_references(data):
        if module == data["module"] and name in spans:
            for use in info["usages"]:
                used_by[name].add(use[4] if len(use) > 4 else None)
    # A public declaration, instance, untracked command, etc. can keep a whole
    # chain alive. Propagate liveness toward its premises.
    children = defaultdict(set)
    stack = []
    for name, users in used_by.items():
        for user in users:
            if user not in spans:
                stack.append(name)
            else:
                children[user].add(name)
    while stack:
        n = stack.pop()
        if n in spans:
            del spans[n]
            stack.extend(children[n])
    return spans


def rank(root, minimum):
    out = []
    for p in (root / "src").rglob("*.lean"):
        source = p.read_text()
        if "private theorem " not in source and "private lemma " not in source:
            continue
        cmds = list(command.finditer(source))
        # Cheap ranking filter. len + 1 also counts an unterminated final line.
        upper = sum(source.count("\n", m.start(), cmds[i+1].start() if i+1 < len(cmds) else len(source))+1
                    for i,m in enumerate(cmds) if private.match(source,m.start()))
        if upper < minimum:
            continue
        rel = p.relative_to(root / "src")
        artifact = (root / ".lake/build/lib/lean" / rel).with_suffix(".ilean")
        if not artifact.exists():
            raise FileNotFoundError(artifact)
        spans = unused(source, json.loads(artifact.read_text()))
        score = sum(b-a+1 for a,b in spans.values())
        if score >= minimum:
            out.append((score, str(rel), spans))
    return sorted(out, key=lambda row: (-row[0], row[1]))


def patch(root, rel, binary):
    src = Path("src") / rel
    obj = (root / ".lake/build/lib/lean" / rel).with_suffix(".olean")
    original = (root / src).read_text()
    spans = unused(original, json.loads(obj.with_suffix(".ilean").read_text()))
    subprocess.run([binary, obj, "--unused", *sorted(spans)], check=True)
    return deletion_diff(original, src, spans)


def deletion_diff(original, src, spans):
    result = delete_spans(original, spans)
    return difflib.unified_diff(original.splitlines(True), result.splitlines(True),
                                fromfile="a/" + str(src), tofile="b/" + str(src))


def delete_spans(original, spans):
    lines = original.splitlines(keepends=True)
    for a, b in sorted(spans.values(), reverse=True):
        # The compiler's declaration range can start after a single-command scope.
        while a:
            prefix = lines[a - 1].rstrip("\r\n")
            if not any(rule.fullmatch(prefix) for rule in (scoped_variables, scoped_open, scoped_instance)):
                break
            a -= 1
        del lines[a:b + 1 + (lines[b + 1:b + 2] == ["\n"])]
    result = "".join(lines)
    if len(result.encode()) >= len(original.encode()) or result.count("\n") >= original.count("\n"):
        raise ValueError("completed patch must reduce bytes and lines")
    return result


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("repo", type=Path)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--min-lines", type=int, help="minimum potential lines per module for this ranking")
    mode.add_argument("--patch", type=Path, help="propose deletion of the indexed private island in this module")
    parser.add_argument("--scanner", type=Path, help="compiled ProofPairs, used by --patch")
    args = parser.parse_args()
    if args.patch:
        if not args.scanner:
            parser.error("--patch requires --scanner")
        sys.stdout.writelines(patch(args.repo, args.patch, args.scanner.resolve()))
    else:
        for score, file, spans in rank(args.repo, args.min_lines):
            print(json.dumps({"lines": score, "file": file, "declarations": spans}, ensure_ascii=False))
