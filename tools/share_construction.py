"""Factor named local conclusions, then replay the edited declarations in Lean.

Run in the project's Lake environment. Modules are supplied in import order. Each candidate lemma must be visible
to its consumers through their existing imports. No source tree
is edited. Only an accepted rewrite is returned as accepted.patch.
"""

import argparse
from collections import defaultdict, deque
from dataclasses import dataclass
import difflib
import json
import os
from pathlib import Path
import re
import subprocess
import textwrap

from branch_candidates import branch_sites
from module_overlay import link_unchanged
from projection_share import project_whole_pair
from suffix_placement import suffix_start
from unreferenced_family import source_declarations

TOOLS = Path(__file__).resolve().parent
HAVE = re.compile(r"^( +)have +([^\W\d][\w']*)\s*:\s*")
FUNCTION_HAVE = re.compile(r"^( +)have +([^\W\d][\w']*)\s*[(\[{]")
MARK = re.compile(r":=\s*by\s*$")


@dataclass(frozen=True)
class Site:
    module: str
    owner: str
    written_owner: str
    owner_start: int
    start: int
    assignment: int
    end: int
    indent: int
    branch: bool = False


def find_sites(module, lines, decls, minimum):
    for owner, decl in decls.items():
        start, end = decl["first_line"] - 1, decl["last_line"]
        for i in range(start, end):
            match = HAVE.match(lines[i]) or FUNCTION_HAVE.match(lines[i])
            if not match:
                continue
            indent = len(match[1])
            k = i
            while k + 1 < end and not MARK.search(lines[k]):
                # Stop at a term proof, including a lambda whose body starts with by.
                # A nested have owns its own tactic block.
                code = lines[k].partition("--")[0].rstrip()
                if code.endswith(":=") or re.search(r":=\s*(?:calc|fun\b.*\bby)$", code):
                    break
                k += 1
                if lines[k].strip() and len(lines[k]) - len(lines[k].lstrip()) <= indent:
                    break
            if not MARK.search(lines[k]) or (k != i and len(lines[k]) - len(lines[k].lstrip()) <= indent):
                continue
            stop = k + 1
            while stop < end and (
                not lines[stop].strip() or len(lines[stop]) - len(lines[stop].lstrip()) > indent
            ):
                stop += 1
            while stop > k + 1 and not lines[stop - 1].strip():
                stop -= 1
            if stop - k - 1 >= minimum:
                yield Site(module, owner, decl["theorem"], start, i, k, stop, indent)


def scheduled_branches(module, lines, decls, selected):
    wanted = {(r["start"], r["end"]): r["owner"]["name"] for r in selected
              if r["file"] == module_path(module).as_posix()}
    sites = []
    for owner in sorted(set(wanted.values())):
        decl = decls[owner]
        first = decl["first_line"] - 1
        for key, start, end in branch_sites(lines, first, decl["last_line"], 1,
                                            {"complete_branches": 0, "application_prefixes": 0}):
            if key[0] == "branch" and wanted.get((start, end)) == owner:
                i = start - 1
                indent = len(lines[i]) - len(lines[i].lstrip())
                sites.append(Site(module, owner, decl["theorem"], first, i, i, end, indent, True))
    sites.sort(key=lambda site: site.start)
    if len(sites) != len(wanted) or any(a.end > b.start for a, b in zip(sites, sites[1:])):
        raise ValueError(f"unmatched or overlapping scheduled branches in {module}")
    return sites


def bullet_body(site, lines):
    first = lines[site.start].lstrip()[1:].lstrip()
    rest = [line[site.indent + 2:] for line in lines[site.start + 1:site.end]]
    return "\n".join(([first] if first else []) + rest)


def suffix_sites(module, lines, decls, selected):
    for row in selected:
        if row["file"] != module_path(module).as_posix():
            continue
        decl = decls[row["owner"]]
        start, end = row["first"] - 1, row["end"]
        if not decl["first_line"] - 1 <= start < end == decl["last_line"]:
            raise ValueError(f"suffix outside owner: {row['owner']}")
        start = suffix_start(lines, row["first"], end)
        if start is not None:
            yield Site(module, row["owner"], decl["theorem"], decl["first_line"] - 1,
                       start, start, end, 2)


def rewrite_suffix(lines, sites, host, name, capture, body):
    result = list(lines)
    for site in sorted(sites, key=lambda s: -s.start):
        result[site.start:site.end] = [f"  apply _root_.{name} <;> assumption\n"]
    if host:
        namespace, _, short = name.rpartition(".")
        end = next((i for i in reversed(range(len(lines))) if lines[i].strip()), -1)
        if not namespace or end < 0 or lines[end].strip() != "end " + namespace:
            raise ValueError("host must end in the specified helper namespace")
        header = "theorem " + short
        width = len(header)
        for binder in capture["binders"]:
            if width + 1 + len(binder) > 100:
                header += "\n   "
                width = 3
            header += " " + binder
            width += 1 + len(binder)
        goal = textwrap.indent(capture["goal"], "    ")
        result[end:end] = (header + " :\n" + goal + " := by\n").splitlines(True) + body + ["\n"]
    return result


def run(cmd, env, cwd, log, stdin=None):
    with log.open("w") as out:
        process = subprocess.run(
            cmd, cwd=cwd, env=env, input=stdin, text=True, stdout=out, stderr=subprocess.STDOUT
        )
    return process.returncode == 0


def make_helper(site, lines, capture, name):
    if site.branch:
        result = capture["goal"].replace("\n", "\n    ")
        body = textwrap.indent(bullet_body(site, lines), "  ")
    else:
        first = HAVE.match(lines[site.start])
        signature = [lines[site.start][first.end() :], *lines[site.start + 1 : site.assignment + 1]]
        signature[-1] = MARK.sub("", signature[-1]).rstrip()
        result = signature[0].strip()
        if len(signature) > 1:
            result += "\n" + textwrap.indent(textwrap.dedent("\n".join(signature[1:])), "      ")
        body = textwrap.indent(textwrap.dedent("\n".join(lines[site.assignment + 1 : site.end])), "  ")
    user_owner = site.owner.split(".0.", 1)[-1] if site.owner.startswith("_private.") else site.owner
    written_owner = site.written_owner.removeprefix("_root_.")
    ambient = user_owner.removesuffix(written_owner)
    if not user_owner.endswith(written_owner):
        raise ValueError(f"unresolved namespace for {site.owner}")
    # A root-qualified declaration may elaborate short names differently inside its proof.
    declared = name[len(ambient) :] if name.startswith(ambient) else "_root_." + name
    header = "theorem " + declared + "\n    " + "\n    ".join(capture["binders"])
    return (header + " :\n    " + result + " := by\n" + body + "\n\n").splitlines(True)


def rewrite(lines, sites, provider, capture, name, choices):
    edits = []
    for site in sites:
        call = MARK.sub(":= by", lines[site.assignment].rstrip()) + "\n"
        tactic = "apply _root_." + name + " <;> "
        extras = choices.get(site, [])
        tactic += (
            "first | assumption | " + " | ".join("exact " + x for x in extras) if extras else "assumption"
        )
        edits.append(
            (
                site.assignment,
                site.end,
                ([" " * site.indent + "· " + tactic + "\n"] if site.branch
                 else [call, " " * (site.indent + 2) + tactic + "\n"]),
            )
        )
    if provider in sites:
        edits.append(
            (
                provider.owner_start,
                provider.owner_start,
                make_helper(provider, [s.rstrip("\n") for s in lines], capture, name),
            )
        )
    result = lines.copy()
    for a, b, replacement in sorted(edits, key=lambda x: x[0], reverse=True):
        result[a:b] = replacement
    return result


def module_path(name):
    return Path(*name.split(".")).with_suffix(".lean")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path)
    parser.add_argument("library", type=Path, help="matching compiled project library")
    parser.add_argument("output", type=Path, help="new directory for this experiment")
    parser.add_argument("modules", nargs="+", help="source modules in import order")
    parser.add_argument(
        "--min-lines", type=int, default=10, help="minimum tactic body lines for discovery"
    )
    parser.add_argument("--lean-arg", action="append", default=[])
    parser.add_argument("--helper", default="sharedConstruction", help="fresh fully qualified Lean name")
    group = parser.add_mutually_exclusive_group()
    group.add_argument("--branch-group", type=Path, help="one resolved whole-branch group from the scanner")
    group.add_argument("--suffix-group", type=Path,
                       help="one placed suffix group, or an enclosing group with its host first in modules")
    args = parser.parse_args()
    selection = args.branch_group or args.suffix_group
    group_data = json.loads(selection.read_text()) if selection else None
    selected = group_data["sites"] if group_data is not None else None
    source, lib, out = (p.resolve() for p in (args.source, args.library, args.output))
    out.mkdir(parents=True, exist_ok=False)
    if not re.fullmatch(r"[A-Za-z_]\w*(\.[A-Za-z_]\w*)*", args.helper):
        parser.error("expected a fully qualified identifier")
    if any("/" in m or not all(m.split(".")) for m in args.modules):
        parser.error("expected dotted module names")
    if args.min_lines < 1 or len(set(args.modules)) != len(args.modules):
        parser.error("use a positive minimum size and distinct modules")
    mods = args.modules
    if args.suffix_group and "host" in group_data:
        host = group_data["host"]
        if not host:
            parser.error("this suffix group has no proposed common host")
        mods = [host, *(m for m in mods if m != host)]
    cwd = Path.cwd()
    base_env = {**os.environ, "LEAN_NUM_THREADS": "1"}
    tool_lib = out / "tools"
    tool_lib.mkdir()
    if not run(
        [
            "lean",
            "-j1",
            "--root=" + str(TOOLS),
            "-o",
            tool_lib / "ShareSite.olean",
            TOOLS / "ShareSite.lean",
        ],
        base_env,
        cwd,
        out / "tool.log",
    ):
        raise SystemExit(f"capture tool failed: {out/'tool.log'}")
    paths = {m: module_path(m) for m in mods}
    original = {m: (source / f).read_text().splitlines(True) for m, f in paths.items()}

    def environment(overlay):
        return {
            **base_env,
            "LEAN_PATH": os.pathsep.join([str(tool_lib), str(overlay), base_env.get("LEAN_PATH", "")]),
        }

    def compile_one(m, root, overlay, log):
        f = paths[m]
        target = (overlay / f).with_suffix(".olean")
        return run(
            [
                "lean",
                "-j1",
                *args.lean_arg,
                "--root=" + str(root),
                "-o",
                target,
                "-i",
                target.with_suffix(".ilean"),
                root / f,
            ],
            environment(overlay),
            cwd,
            log,
        )

    # The supplied library is the compiled snapshot of the input sources.
    baseline = lib
    declarations = {}
    catalog = {}
    captures = {}
    grouped = defaultdict(list)
    unresolved = []
    for m in mods:
        f = paths[m]
        info = json.loads((baseline / f).with_suffix(".ilean").read_bytes())
        decls = source_declarations(source / f, info)
        declarations[m] = decls
        lines = [s.rstrip("\n") for s in original[m]]
        sites = (list(suffix_sites(m, lines, decls, selected)) if args.suffix_group else
                 scheduled_branches(m, lines, decls, selected) if selected is not None
                 else list(find_sites(m, lines, decls, args.min_lines)))
        if not sites:
            continue
        marked = original[m].copy()
        expected = {}
        for site in reversed(sites):
            key = f"{m}:{site.start + 1}"
            expected[key] = site
            probe = f'share_site "{key}" "{" ".join(mods)}" =>'
            if args.suffix_group:
                body = textwrap.indent("".join(marked[site.start:site.end]), "  ")
                marked[site.start:site.end] = ["  " + probe + "\n", body]
            elif site.branch:
                body = textwrap.indent(bullet_body(site, lines), " " * (site.indent + 4))
                marked[site.start:site.end] = [(" " * site.indent) + "· " + probe + "\n", body + "\n"]
            else:
                marked[site.assignment] = MARK.sub(":= by " + probe, marked[site.assignment].rstrip()) + "\n"
        insert = next(
            (
                i
                for i, line in enumerate(marked)
                if re.match(r"^(?:(?:public|private|meta) +)*import ", line)
            ),
            None,
        )
        if insert is None:
            insert = next((i + 1 for i, line in enumerate(marked) if line.strip() == "module"), 0)
        marked.insert(insert, "import ShareSite\n")
        path = out / "probe" / f
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text("".join(marked))
        log = out / f"{m}.probe.log"
        ok = run(
            ["lean", "-j1", *args.lean_arg, "--root=" + str(out / "probe"), path],
            environment(baseline),
            cwd,
            log,
        )
        if not ok:
            unresolved.extend(expected)
            continue
        found = set()
        for line in log.read_text().splitlines():
            if not line.startswith("SHARE_SITE "):
                continue
            item = json.loads(line[len("SHARE_SITE ") :])
            key = item["id"]
            if key not in expected or key in found:
                raise ValueError(f"ambiguous probe {key}")
            found.add(key)
            catalog[key] = expected[key]
            captures[key] = item
            grouped[tuple(item["symbols"])].append(key)
        unresolved.extend(sorted(expected.keys() - found))
    report = {
        "modules": mods,
        "min_body_lines": args.min_lines,
        "probed": len(catalog),
        "unresolved": unresolved,
        "symbol_groups": len(grouped),
        "trials": [],
    }

    def save():
        (out / "report.json").write_text(json.dumps(report, indent=2, ensure_ascii=False) + "\n")

    save()
    # Symbol sets only propose candidates. Compilation and exact replay decide.
    proposals = []
    if args.suffix_group and len(catalog) == len(selected) and len(catalog) >= 2:
        keys = sorted(catalog)
        first_capture = captures[keys[0]]
        def tail(key):
            site = catalog[key]
            return original[site.module][site.start:site.end]
        if all(mods[0] != catalog[k].module and mods[0] in captures[k]["imports"]
               and captures[k]["binders"] == first_capture["binders"]
               and captures[k]["goal"] == first_capture["goal"] and tail(k) == tail(keys[0])
               for k in keys):
            proposals.append((0, keys[0], keys))
    for symbols, exact_keys in ([] if args.suffix_group else grouped.items()):
        # Coercions in a specialized caller can introduce additional type constants.
        # Try those callers together first, preserving the exact group as a fallback.
        general = set(symbols)
        compatible = [k for syms, ks in grouped.items() if general.issubset(syms) for k in ks]
        for key in sorted(exact_keys):
            provider = catalog[key]
            if not provider.branch and not HAVE.match(original[provider.module][provider.start]):
                continue
            considered = set()
            for pool in (compatible, exact_keys):
                chosen = [key]
                for other in sorted(
                    pool, key=lambda k: (mods.index(catalog[k].module), catalog[k].start)
                ):
                    site = catalog[other]
                    if (
                        site.module != provider.module
                        and provider.module not in captures[other]["imports"]
                    ):
                        continue
                    if other == key or (
                        site.module == provider.module and site.owner_start < provider.owner_start
                    ):
                        continue
                    if any(
                        site.module == catalog[k].module
                        and max(site.start, catalog[k].start) < min(site.end, catalog[k].end)
                        for k in chosen
                    ):
                        continue
                    chosen.append(other)
                if len(chosen) > 1 and tuple(chosen) not in considered:
                    considered.add(tuple(chosen))
                    hint = sum(catalog[k].end - catalog[k].assignment - 1 for k in chosen[1:])
                    proposals.append((-hint, key, chosen))
    # A repeated branch can reveal two almost identical enclosing proofs.
    whole = {}
    if args.branch_group:
        for _, key, keys in proposals:
            candidate = project_whole_pair(original, [catalog[k] for k in keys], declarations, args.helper)
            if candidate:
                whole[(key, tuple(keys))] = candidate
    pending = deque([(key, keys, True) for _, key, keys in sorted(proposals)
                     if (key, tuple(keys)) in whole]
                    + [(key, keys, False) for _, key, keys in sorted(proposals)])
    attempted = set()
    while pending:
        key, keys, entire = pending.popleft()
        token = (key, tuple(keys), entire)
        if token in attempted:
            continue
        attempted.add(token)
        index = len(attempted) - 1

        def retry_without(excluded):
            remaining = [k for k in keys if k not in excluded]
            if not args.suffix_group and key in remaining and 1 < len(remaining) < len(keys):
                pending.appendleft((key, remaining, False))

        folder = out / f"trial-{index}"
        folder.mkdir()
        provider = catalog[key]
        sites = [catalog[k] for k in keys]
        choices = {}
        for k in keys:
            missing = set(captures[key]["premises"]) - set(captures[k]["premises"])
            choices[catalog[k]] = sorted(
                {
                    s.replace("\n", " ")
                    for head, s in captures[k]["embedded"]
                    if head in missing and "⋯" not in s and "✝" not in s
                }
            )
        trial = {"sites": keys, "provider": key}
        if args.suffix_group:
            trial.update(kind="shared theorem suffix", host=mods[0])
        if entire:
            trial["kind"] = "whole proof with hypothesis projection"
        report["trials"].append(trial)
        changed = {}
        diff = []
        call_lines = {}
        for m in mods:
            local = [s for s in sites if s.module == m]
            f = paths[m]
            new = (rewrite_suffix(original[m], local, m == mods[0], args.helper,
                                  captures[key], tail(key)) if args.suffix_group else
                   whole[(key, tuple(keys))].get(m, original[m]) if entire else
                   rewrite(original[m], local, provider, captures[key], args.helper, choices))
            if new != original[m]:
                changed[m] = list(dict.fromkeys(s.owner for s in local))
                emitted = [
                    i + 1
                    for i, line in enumerate(new)
                    if line.strip().removeprefix("· ").startswith("apply _root_." + args.helper + " <;> ")
                ]
                sorted_keys = sorted(
                    (k for k in keys if catalog[k].module == m), key=lambda k: catalog[k].start
                )
                call_lines[m] = {} if entire else dict(zip(emitted, sorted_keys, strict=True))
            dest = folder / "src" / f
            dest.parent.mkdir(parents=True, exist_ok=True)
            dest.write_text("".join(new))
            diff.extend(
                difflib.unified_diff(
                    original[m], new, fromfile="a/" + f.as_posix(), tofile="b/" + f.as_posix()
                )
            )
        before = "".join("".join(original[m]) for m in mods)
        after = "".join((folder / "src" / paths[m]).read_text() for m in mods)
        trial.update(
            lines_saved=before.count("\n") - after.count("\n"),
            bytes_saved=len(before.encode()) - len(after.encode()),
        )
        if min(trial["lines_saved"], trial["bytes_saved"]) <= 0:
            trial["status"] = "source did not shrink"
            save()
            continue
        patched = folder / "lib"
        link_unchanged(lib, patched, {paths[m].with_suffix("") for m in changed})
        for m in changed:
            if not compile_one(m, folder / "src", patched, folder / (m + ".log")):
                trial["status"] = "compilation failed in " + m
                errors = re.findall(
                    r"^.+?\.lean:(\d+):\d+: error(?:\(|:)", (folder / (m + ".log")).read_text(), re.M
                )
                failed = {call_lines.get(m, {}).get(int(i)) for i in errors}
                if failed and None not in failed:
                    trial["failed_sites"] = sorted(failed)
                    retry_without(failed)
                break
        else:
            request = dict(
                provider=str((patched / paths[mods[0] if args.suffix_group else provider.module]).with_suffix(".olean")),
                helper=args.helper,
                modules=[
                    dict(
                        old=str((baseline / paths[m]).with_suffix(".olean")),
                        new=str((patched / paths[m]).with_suffix(".olean")),
                        owners=owners,
                    )
                    for m, owners in changed.items()
                ],
            )
            (folder / "replay.json").write_text(json.dumps(request))
            accepted = run(
                [
                    "lean",
                    "-j1",
                    "--root=" + str(TOOLS),
                    "--run",
                    TOOLS / "ProofPairs.lean",
                    "--shared-lemma-replay",
                ],
                base_env,
                cwd,
                folder / "replay.log",
                json.dumps(request),
            )
            trial["status"] = "accepted" if accepted else "replay or DAG check failed"
            if not accepted:
                failure = (folder / "replay.log").read_text().strip().splitlines()
                trial["reason"] = failure[-1] if failure else "no checker output"
                mismatch = re.search(r"expanded proof differs: (\S+)$", trial["reason"])
                if mismatch:
                    retry_without({k for k in keys if catalog[k].owner == mismatch[1]})
            if accepted:
                trial["dag"] = json.loads((folder / "replay.log").read_text().splitlines()[-1])
                (out / "accepted.patch").write_text("".join(diff))
                save()
                print(json.dumps(trial))
                return
        save()
    print(json.dumps(report))


if __name__ == "__main__":
    main()
