"""Try instance synthesis, then library search at a selected cut. Replay the explicit proof."""
import argparse
import difflib
import json
from pathlib import Path
import re
import subprocess
import tempfile


def probe(project, module, source, first, last, options, *, term=False):
    lines = source.read_bytes().decode().splitlines(keepends=True)
    if not 1 <= first <= last <= len(lines):
        raise ValueError("invalid one-based inclusive tactic range")
    indent = re.match(r"[ \t]*", lines[first - 1])[0]
    newline = "\r\n" if lines[first - 1].endswith("\r\n") else "\n"
    original = "".join(lines)
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        path = root.joinpath(*module.split(".")).with_suffix(".lean")
        path.parent.mkdir(parents=True, exist_ok=True)

        def check(tactic):
            if term:
                tactic = tactic.removeprefix("exact ") if tactic.startswith("exact ") else "by " + tactic
            proposed = "".join([*lines[:first - 1], indent + tactic + newline, *lines[last:]])
            path.write_text(proposed)
            proc = subprocess.run(["lake", "env", "lean", "-j1", *options, "--json",
                                   "--root=" + str(root), path], cwd=project,
                                  stdout=subprocess.PIPE, text=True)
            messages = [json.loads(line) for line in proc.stdout.splitlines()]
            return proposed, proc.returncode, messages

        prefix = "first | exact inferInstance | "
        _, code, messages = check(prefix + "exact?")
        errors = [m["data"] for m in messages if m["severity"] == "error"]
        if code:
            return {"status": "search_failed", "errors": errors}
        position = {"line": first, "column": len(indent + prefix) + (3 if term else 0)}
        tactic = "exact inferInstance"
        for msg in messages:
            if msg["pos"] != position or msg["severity"] != "information" or not msg["data"].startswith("Try this:"):
                continue
            match = re.fullmatch(r"Try this:\n\s*(?:\[apply\] )?(exact [^\n]+)", msg["data"])
            if not match:
                return {"status": "no_explicit_single_line_suggestion"}
            tactic = match[1]
            break
        proposed, code, replay = check(tactic)
        if code:
            return {"status": "replay_failed", "suggestion": tactic,
                    "errors": [m["data"] for m in replay if m["severity"] == "error"]}
        patch = difflib.unified_diff(lines, proposed.splitlines(keepends=True),
                                     fromfile=str(source.name), tofile=str(source.name))
        return {"status": "replayed", "suggestion": tactic, "lines_saved": last - first,
                "bytes_saved": len(original.encode()) - len(proposed.encode()), "diff": "".join(patch)}


if __name__ == "__main__":
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("project", type=Path)
    p.add_argument("module")
    p.add_argument("source", type=Path)
    p.add_argument("first", type=int)
    p.add_argument("last", type=int)
    p.add_argument("--lean-arg", action="append", default=[], help="pass a project setting, e.g. --lean-arg=-DautoImplicit=false")
    p.add_argument("--term", action="store_true", help="replace a whole term on separate lines after :=")
    a = p.parse_args()
    print(json.dumps(probe(a.project, a.module, a.source, a.first, a.last, a.lean_arg, term=a.term), ensure_ascii=False))
