"""Find a local definition made unused by the preceding checked deletion."""
import argparse
from collections import defaultdict
import json
from pathlib import Path
import re
import subprocess

from unused_have import have


def binder_uses(scanner, obj, theorem):
    raw = subprocess.check_output([scanner, obj, "--local-lets", theorem], text=True)
    out = defaultdict(list)
    for _, (name, (used, _)) in map(json.loads, raw.splitlines()):
        out[name].append(used)
    return out


def candidates(scanner, before, after, source, theorem, pending=()):
    old = binder_uses(scanner, before, theorem)
    new = binder_uses(scanner, after, theorem)
    names = {name for name, usage in new.items() if usage == [False] and (old[name] == [True] or name in pending)}
    info = json.loads(after.with_suffix(".ilean").read_bytes())
    first, _, last, _ = info["decls"][theorem][:4]
    lines = source.splitlines()
    positions = defaultdict(list)
    for i in range(first + 1, last + 1):
        block = have.match(lines[i])
        local = re.fullmatch(r"( +)let +([^\W\d][\w']*)\s*(?::.*?)?\s*:=\s*\S.*", lines[i])
        match = block or local
        if not match or match[2] not in names:
            continue
        indent = len(match[1])
        end = i + 1
        while end <= last and (not lines[end].strip() or len(lines[end]) - len(lines[end].lstrip()) > indent):
            end += 1
        while end > i + 1 and not lines[end - 1].strip():
            end -= 1
        if block or end == i + 1:
            positions[match[2]].append((i + 1, end))
    results = []
    for name, spans in positions.items():
        if len(spans) == 1:
            start, end = spans[0]
            results.append(dict(binder=name, first_line=start, last_line=end))
    return sorted(results, key=lambda r: (r["first_line"] - r["last_line"], r["first_line"]))


def extend_verified(scanner, before, after, source_file, theorem, lean_args, output):
    """Try cascading removals one at a time; keep only exact kernel-term matches."""
    source = source_file.read_text()
    module = json.loads(after.with_suffix(".ilean").read_bytes())["module"]
    relative = Path(*module.split(".")).with_suffix(".lean")
    pending = set()
    accepted = []
    attempts = 0
    while True:
        rows = candidates(scanner, before, after, source, theorem, pending)
        pending = {r["binder"] for r in rows}
        for row in rows:
            attempts += 1
            root = output / str(attempts)
            root.mkdir(parents=True, exist_ok=False)
            path = root / relative
            path.parent.mkdir(parents=True, exist_ok=True)
            lines = source.splitlines(keepends=True)
            del lines[row["first_line"] - 1:row["last_line"]]
            proposed = "".join(lines)
            path.write_text(proposed)
            obj = path.with_suffix(".olean")
            with (root / "check.log").open("w") as log:
                compiled = subprocess.run(
                    ["lean", "-j1", *lean_args, "--root=" + str(root), "-o", obj,
                     "-i", path.with_suffix(".ilean"), path], stdout=log, stderr=subprocess.STDOUT)
                if compiled.returncode:
                    continue
                checked = subprocess.run([scanner, after, "--drop-unused-let", obj,
                                          theorem, theorem, row["binder"]], stdout=log, stderr=subprocess.STDOUT)
                if checked.returncode:
                    continue
            before, after, source = after, obj, proposed
            pending.discard(row["binder"])
            accepted.append(dict(**row, object=str(obj)))
            break
        else:
            return source, accepted


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    for arg in ("scanner", "before", "after", "source"):
        parser.add_argument(arg, type=Path)
    parser.add_argument("theorem")
    args = parser.parse_args()
    for row in candidates(args.scanner, args.before, args.after, args.source.read_text(), args.theorem):
        print(json.dumps(row, ensure_ascii=False))
