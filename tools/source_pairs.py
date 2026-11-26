"""Rank repeated theorem text within a Lean file as hints for the typed scanner."""
import argparse
import re
from pathlib import Path

# This prefilter recognizes only unindented theorem commands. Context and binding
# are checked later on elaborated terms, so matching text alone never edits a file.
command = re.compile(r"^(?![ \t\n\r]|--|/[-*]|\*)\S", re.M)
header = re.compile(r"(?:private\s+|protected\s+)?(?:theorem|lemma)\s+((?:[^\s({\[:.]|\.(?!\{))+)(.*)", re.S)


def matches_declaration_name(name, spelling):
    if spelling.startswith("_root_."):
        if name.startswith("_private."):
            # Lean stores a root-qualified private declaration under _private.<module>.0.
            _, separator, user_name = name.partition(".0.")
            if separator:
                name = user_name
        return name == spelling.removeprefix("_root_.")
    return bool(spelling) and (name == spelling or name.endswith("." + spelling))


def declaration_spelling(lines, name, position):
    """Resolve a compiler's UTF-16 selection range against the pinned source."""
    _, _, last, _, line, start, stop, end = position
    if line != stop or max(line, last) >= len(lines):
        return None
    token = lines[line].encode("utf-16-le")[2*start:2*end].decode("utf-16-le")
    return token if matches_declaration_name(name, token) else None


def candidates(source):
    starts = [m.start() for m in command.finditer(source)] + [len(source)]
    seen = {}
    line = 1 + source.count("\n", 0, starts[0])
    for begin, end in zip(starts, starts[1:]):
        decl_line = line
        line += source.count("\n", begin, end)
        decl = header.match(source[begin:end].rstrip())
        if not decl:
            continue
        name, body = decl.groups()
        if ":= by" not in body:
            continue
        if body in seen:
            yield len(body.splitlines()), *seen[body], decl_line, name
        else:
            seen[body] = decl_line, name


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("directory", type=Path)
    args = parser.parse_args()
    rows = ((size, path, *pair) for path in args.directory.rglob("*.lean")
            for size, *pair in candidates(path.read_text()))
    for row in sorted(rows, reverse=True):
        print(*row, sep="\t")
