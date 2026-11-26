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


def metadata_ranges(source_file, module, line, settings=()):
    tool = Path(__file__).with_name("TacticSpans.lean").resolve()
    args = [arg[2:] for arg in settings if arg.startswith("-D")]
    shell = [arg for arg in settings if arg.startswith("--tstack=")]
    raw = subprocess.check_output(["lean", "-j1", *shell, "--run", tool, source_file,
                                   module, str(line), *args], text=True)
    return list(map(json.loads, raw.splitlines()))


def binder_ranges(source, tactics, names):
    """Locate independent have/let tactics, keeping adjacent tactics and comments."""
    data = source.encode()
    spans = defaultdict(set)
    for t in tactics:
        if t["kind"] not in {"Lean.Parser.Tactic.tacticHave__", "Lean.Parser.Tactic.tacticLet__"}:
            continue
        before, after = t["before"], t["after"]
        if not before or not after or before[1:] != after[1:]:
            continue
        a, b = t["start"], t["end"]
        head = re.match(r"(?:have|let)\s+([^\W\d][\w']*)", data[a:b].decode())
        if not head or head[1] not in names:
            continue
        start = data.rfind(b"\n", 0, a) + 1
        stop = data.find(b"\n", b)
        stop = len(data) if stop < 0 else stop
        left, right = data[start:a], data[b:stop]
        if match := re.match(rb"[ \t]*;[ \t]*", right):
            b += match.end()
        elif not left.strip() and not right.strip():
            a, b = start, min(stop + 1, len(data))
        elif not right.strip() and (match := re.search(rb";[ \t]*$", left)):
            a = start + match.start()
        else:
            continue
        spans[head[1]].add((a, b))
    return [dict(binder=n, start=a, end=b, first_line=data.count(b"\n", 0, a) + 1,
                 last_line=data.count(b"\n", 0, b - 1) + 1)
            for n, hits in spans.items() if len(hits) == 1 for a, b in hits]


def candidates(scanner, before, after, source, theorem, pending=(), *, source_file=None, lean_args=()):
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
        if block or (end == i + 1 and ";" not in lines[i]):
            positions[match[2]].append((i + 1, end))
    results = []
    for name, spans in positions.items():
        if len(spans) == 1:
            start, end = spans[0]
            results.append(dict(binder=name, first_line=start, last_line=end))
    unresolved = names - {r["binder"] for r in results}
    if source_file and unresolved:
        tactics = metadata_ranges(source_file, info["module"], last + 1, lean_args)
        results.extend(binder_ranges(source, tactics, unresolved))
    return sorted(results, key=lambda r: (r["first_line"] - r["last_line"], r["first_line"]))


def extend_verified(scanner, before, after, source_file, theorem, lean_args, output):
    """Try cascading removals one at a time; keep only exact kernel-term matches."""
    source = source_file.read_bytes().decode()
    module = json.loads(after.with_suffix(".ilean").read_bytes())["module"]
    relative = Path(*module.split(".")).with_suffix(".lean")
    pending = set()
    accepted = []
    attempts = 0
    while True:
        rows = candidates(scanner, before, after, source, theorem, pending, source_file=source_file, lean_args=lean_args)
        pending = {r["binder"] for r in rows}
        for row in rows:
            attempts += 1
            root = output / str(attempts)
            root.mkdir(parents=True, exist_ok=False)
            path = root / relative
            path.parent.mkdir(parents=True, exist_ok=True)
            lines = source.splitlines(keepends=True)
            if "start" in row:
                data = source.encode()
                proposed = (data[:row["start"]] + data[row["end"]:]).decode()
            else:
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
            before, after, source, source_file = after, obj, proposed, path
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
    parser.add_argument("--metadata", action="store_true", help="resolve ambiguous spans in the project Lake environment")
    parser.add_argument("--lean-arg", action="append", default=[])
    args = parser.parse_args()
    for row in candidates(args.scanner, args.before, args.after, args.source.read_bytes().decode(), args.theorem,
                          source_file=args.source if args.metadata else None, lean_args=args.lean_arg):
        print(json.dumps(row, ensure_ascii=False))
