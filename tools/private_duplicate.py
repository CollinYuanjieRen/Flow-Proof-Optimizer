"""Emit one reviewable patch for an earlier public and a later private theorem.

Use the typed scan of the unchanged file. Re-elaborate the patch and check that
the use sites resolve to the intended public name before submitting it.
"""
import argparse
import difflib
import json
import sys
from pathlib import Path


def source_span(source):
    lines = source.splitlines(keepends=True)
    starts = [0]
    for line in lines:
        starts.append(starts[-1] + len(line))

    def offset(line, col):
        raw = lines[line].encode("utf-16-le")
        if 2 * col > len(raw):
            raise ValueError("range outside source line")
        return starts[line] + len(raw[:2 * col].decode("utf-16-le"))

    def span(r):
        return offset(*r[:2]), offset(*r[2:4])

    return span


def propose(source, info, pairs, old, keep):
    if info["version"] != 6:
        raise ValueError("expected Lean ilean v6")
    if not any(
        kind in {"same-body", "same-body-via-helpers"} and {a, b} == {old, keep}
        for kind, a, b in (line.split("\t") for line in pairs.splitlines())
    ):
        raise ValueError("missing structural proof-body match")
    span = source_span(source)
    decl = info["decls"][old]
    begin, end = span(decl)
    old_name = old.split(".")[-1]
    name_start, name_end = span(decl[4:])
    if (not old.startswith("_private.") or keep.startswith("_private.")
            or source[begin:name_start] not in {"private theorem ", "private lemma "}
            or source[name_start:name_end] != old_name
            or span(info["decls"][keep])[1] > begin):
        raise ValueError("expected an earlier public theorem and a plain private duplicate")
    if source[end:end + 2] == "\n\n":
        end += 2
    refs = iter(info["references"])
    hits = next(v["usages"] for k, v in zip(refs, refs, strict=True)
                if k == [0, info["module"], old])
    edits = {(begin, end): ""}
    for r in hits:
        a, b = span(r)
        if begin <= a and b <= end:
            continue
        if source[a:b] != old_name or a < end:
            raise ValueError("unexpected use site for the private theorem")
        edits[a, b] = keep.split(".")[-1]
    result = source
    for (a, b), replacement in sorted(edits.items(), reverse=True):
        result = result[:a] + replacement + result[b:]
    if len(result.encode("utf-8")) >= len(source.encode("utf-8")) or result.count("\n") > source.count("\n"):
        raise ValueError("patch must reduce UTF-8 bytes without increasing line count")
    return result


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("source", "ilean", "pairs"):
        parser.add_argument(name, type=Path)
    parser.add_argument("old")
    parser.add_argument("keep")
    args = parser.parse_args()
    source = args.source.read_text()
    result = propose(source, json.loads(args.ilean.read_text()), args.pairs.read_text(), args.old, args.keep)
    sys.stdout.writelines(difflib.unified_diff(source.splitlines(True), result.splitlines(True),
                          fromfile="a/" + str(args.source), tofile="b/" + str(args.source)))
