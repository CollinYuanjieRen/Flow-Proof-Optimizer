"""Rank local have blocks with no later explicit mention in the same theorem.

Tactics can use hypotheses implicitly. This source prefilter does not authorize
deletion; check the elaborated proof and recompile each proposed removal.
"""
import argparse
import json
from pathlib import Path
import re
import sys

from source_pairs import command, header

have = re.compile(r"^( +)have +([^\W\d][\w']*)\s*:\s*.+?\s*:=\s*by\s*$")
named_have = re.compile(r"^( +)have +([^\W\d][\w']*)(?=[\s:({]|$)")
anonymous_have = re.compile(r"^( +)have[ \t]*:")
token = re.compile(r"[\w']+")


def scan(source, additional_forms=False, *, files=None, anonymous=False):
    """Scan all Lean files, or the supplied paths relative to the source root."""
    pattern = named_have if additional_forms else have
    if anonymous:
        pattern = anonymous_have
    allow_single_line = additional_forms or anonymous
    totals = dict(modules=0, declarations=0, matched_headers=0)
    hits = []
    paths = source.rglob("*.lean") if files is None else (source / name for name in files)
    for path in paths:
        totals["modules"] += 1
        text = path.read_text()
        if ("have" if anonymous else "have ") not in text:
            continue
        lines = text.splitlines()
        starts = [i for i, line in enumerate(lines) if command.match(line)]
        for pos, end in zip(starts, starts[1:] + [len(lines)]):
            decl = header.match(lines[pos])
            if not decl:
                continue
            totals["declarations"] += 1
            blocks = []
            for i in range(pos + 1, end):
                m = pattern.match(lines[i])
                if m is None or (additional_forms and have.match(lines[i])):
                    continue
                name = "this" if anonymous else m[2]
                if name != "_":
                    blocks.append((i, len(m[1]), name))
            totals["matched_headers"] += len(blocks)
            if not blocks:
                continue
            names = {name for _, _, name in blocks}
            last = {}
            for i in range(blocks[0][0], end):
                for name in names.intersection(token.findall(lines[i])):
                    last[name] = i
            for i, depth, name in blocks:
                j = i + 1
                while j < end and (not lines[j].strip() or len(lines[j]) - len(lines[j].lstrip()) > depth):
                    j += 1
                if last.get(name, -1) >= j:
                    continue
                while j > i + 1 and not lines[j - 1].strip():
                    j -= 1
                if allow_single_line and not any(":=" in line for line in lines[i:j]):
                    continue
                if allow_single_line or j > i + 1:
                    hits.append(dict(file=str(path.relative_to(source)), theorem=decl[1], name=name,
                                     theorem_line=pos + 1, first_line=i + 1, last_line=j, lines=j-i))
    hits.sort(key=lambda r: (-r["lines"], r["file"], r["first_line"]))
    return totals, hits


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path)
    forms = parser.add_mutually_exclusive_group()
    forms.add_argument("--additional-forms", action="store_true",
                        help="scan other named assignments, including single-line proofs and multiline headers")
    forms.add_argument("--anonymous", action="store_true",
                       help="scan anonymous assignments whose implicit name is this")
    args = parser.parse_args()
    totals, hits = scan(args.source, args.additional_forms, anonymous=args.anonymous)
    print(json.dumps(dict(**totals, candidates=len(hits))), file=sys.stderr)
    for row in hits:
        print(json.dumps(row, ensure_ascii=False))
