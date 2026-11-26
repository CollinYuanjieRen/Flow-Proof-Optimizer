"""Index whole tactic proofs with a changed projection or namespace spelling on a Git revision.

Output is a source shortlist. Resolve its intervals against the matching compiler data before
testing a rewrite. The minimum counts proof-body lines, including the initial intro tactic.
"""
import argparse
from collections import Counter, defaultdict
from functools import cache
from hashlib import sha256
import json
from pathlib import Path
import re
import subprocess

from branch_candidates import branch_sites
from projection_share import projection_variants
from scan_project import committed_sources


QUALIFIED = re.compile(r"(?<![\w'.])(?:_root_\.)?(?:[A-Z][\w']*\.)+([a-z_][\w']*)(?![\w'.])")


def intro_bodies(content, minimum, counts):
    if b"\n  intro " not in content:
        return
    lines = content.decode().splitlines(True)
    for i, line in enumerate(lines):
        if not i or not line.startswith("  intro ") or not lines[i - 1].rstrip().endswith(":= by"):
            continue
        counts["intro_sites"] += 1
        end = i + 1
        while end < len(lines) and (not lines[end].strip() or lines[end].startswith(" ")):
            end += 1
        while end > i + 1 and not lines[end - 1].strip():
            end -= 1
        if end - i < minimum:
            continue
        args = line.split()[1:]
        if len(args) != len(set(args)) or not all(arg.isidentifier() for arg in args):
            continue
        counts["eligible_bodies"] += 1
        yield i + 1, end, args, "".join(lines[i:end]).rstrip("\r\n") + "\n"


def digest(text):
    return sha256(text.encode()).digest()


def scan(checkout, revision, minimum):
    commit = subprocess.check_output(["git", "rev-parse", "--verify", revision + "^{commit}"],
                                     cwd=checkout, text=True).strip()
    exact, projected = defaultdict(list), defaultdict(list)
    qualified = defaultdict(lambda: defaultdict(list))
    counts = Counter()
    for path, _, content in committed_sources(checkout, commit):
        counts["files"] += 1
        for first, end, args, body in intro_bodies(content, minimum, counts):
            site = (path.as_posix(), first, end)
            key = digest(body)
            exact[key].append(site)
            qualified[digest(QUALIFIED.sub(r"\1", body))][key].append(site)
            for arg, field, variant in projection_variants(body, args):
                projected[digest(variant)].append((site, arg, field))
                counts["variants"] += 1
    projections = [
        dict(strong=a, weak=b, arg=arg, projection=field, body_lines=b[2] - b[1] + 1)
        for key in exact.keys() & projected.keys()
        for a, arg, field in projected[key] for b in exact[key] if a != b
    ]
    spellings = []
    for forms in qualified.values():
        if len(forms) > 1:
            sites = [s for key in sorted(forms) for s in forms[key]]
            spellings.append(dict(lines=sites[0][2] - sites[0][1] + 1, sites=sites, forms=len(forms)))
    projections.sort(key=lambda r: (-r["body_lines"], r["strong"], r["weak"]))
    spellings.sort(key=lambda r: (-r["lines"], -len(r["sites"]), r["sites"]))
    return dict(base=commit, minimum=minimum, stats=counts, projections=projections, spellings=spellings)


def cross_file_branches(checkout, revision, minimum):
    """Source shortlist; the typed owner and reachability checks follow separately."""
    commit = subprocess.check_output(["git", "rev-parse", "--verify", revision + "^{commit}"],
                                     cwd=checkout, text=True).strip()
    groups = defaultdict(list)
    stats = {"complete_branches": 0, "application_prefixes": 0}
    files = 0
    for path, _, content in committed_sources(checkout, commit):
        files += 1
        if "·".encode() not in content:
            continue
        lines = content.decode().splitlines()
        for key, start, end in branch_sites(lines, 0, len(lines), minimum, stats):
            fingerprint = digest(json.dumps(key, ensure_ascii=False, separators=(",", ":")))
            groups[key[0], fingerprint].append((path.as_posix(), start, end))
    hits = []
    for (kind, fingerprint), sites in groups.items():
        if len({path for path, _, _ in sites}) < 2:
            continue
        sizes = [end - start + 1 for _, start, end in sites]
        hits.append(dict(kind=kind, sha=fingerprint.hex(), sites=sites,
                         repeated_lines=sum(sizes) - max(sizes)))
    hits.sort(key=lambda r: (-r["repeated_lines"], r["kind"], r["sites"]))
    return dict(base=commit, files=files, min_lines=minimum, stats=stats, groups=hits)


def enclosing_suffixes(checkout, revision, groups):
    """Extend indexed branches to identical top-level tactic tails within their owners."""
    commit = subprocess.check_output(["git", "rev-parse", "--verify", revision + "^{commit}"],
                                     cwd=checkout, text=True).strip()

    @cache
    def source(path):
        return subprocess.check_output(["git", "show", f"{commit}:src/{path}"],
                                       cwd=checkout, text=True).splitlines()

    by_interval = {}
    for group in groups:
        rows = group["sites"]
        if len(rows) < 2 or any(r["owner"] is None for r in rows):
            continue
        if len({(r["file"], r["owner"]["name"]) for r in rows}) != len(rows):
            continue
        bodies = []
        for r in rows:
            owner = r["owner"]
            lines = source(r["file"])
            start, end = owner["first_line"] - 1, owner["last_line"]
            header = next((i for i in range(start, r["start"] - 1)
                           if lines[i].rstrip().endswith(":= by")), None)
            if header is None:
                break
            bodies.append(lines[header + 1:end])
        if len(bodies) != len(rows):
            continue
        common = 0
        for peers in zip(*(reversed(body) for body in bodies)):
            if len(set(peers)) != 1:
                break
            common += 1
        # Start on a top-level tactic. A textual match beginning inside a tactic
        # may be a continuation of a different command on either side.
        while common and not re.match(r"^  [^\s]", bodies[0][-common]):
            common -= 1
        if not common:
            continue
        sites = []
        for r, body in zip(rows, bodies):
            end = r["owner"]["last_line"]
            first = end - common + 1
            if first > r["start"] or (first, end) == (r["start"], r["end"]):
                break
            sites.append(dict(file=r["file"], owner=r["owner"]["name"], first=first,
                              end=end, prefix_lines=len(body) - common))
        if len(sites) == len(rows):
            key = tuple(sorted((s["file"], s["owner"], s["first"], s["end"]) for s in sites))
            if key in by_interval:
                by_interval[key].setdefault("also_from_groups", []).append(group["group"])
            else:
                by_interval[key] = dict(group=group["group"], common_lines=common, sites=sites)
    hits = sorted(by_interval.values(), key=lambda h: (-h["common_lines"], h["group"]))
    return dict(base=commit, groups_scanned=len(groups), enclosing=hits)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("checkout", type=Path)
    parser.add_argument("revision", help="Git commit or ref")
    parser.add_argument("--min-lines", type=int, default=25)
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument("--cross-branches", action="store_true",
                       help="find matching complete branches and application prefixes across files")
    modes.add_argument("--branch-groups", type=Path,
                        help="extend compiler-located branch groups from this revision to enclosing tactic tails")
    args = parser.parse_args()
    if args.min_lines < 1:
        parser.error("minimum lines must be positive")
    if args.cross_branches:
        result = cross_file_branches(args.checkout, args.revision, args.min_lines)
    elif args.branch_groups:
        result = enclosing_suffixes(args.checkout, args.revision, json.loads(args.branch_groups.read_bytes()))
    else:
        result = scan(args.checkout, args.revision, args.min_lines)
    print(json.dumps(result, ensure_ascii=False))
