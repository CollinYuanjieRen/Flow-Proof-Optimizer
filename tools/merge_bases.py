"""Resolve unambiguous merge bases locally for read-only PR overlap checks."""
import subprocess


def unique_merge_bases(repository, base, heads):
    """Return only answers available from complete local commit ancestry."""
    heads = sorted(set(heads))
    if not heads or not repository.is_dir():
        return {}
    git = ["git", "--no-lazy-fetch", "--git-dir", str(repository)]
    shallow = subprocess.check_output([*git, "rev-parse", "--is-shallow-repository"], text=True)
    if shallow.strip() != "false":
        return {}
    present = subprocess.check_output(
        [*git, "cat-file", "--batch-check=%(objectname) %(objecttype)"],
        input="\n".join([base, *heads]) + "\n", text=True,
    )
    commits = {oid for oid, kind in (line.split() for line in present.splitlines())
               if kind == "commit"}
    if base not in commits:
        return {}
    result = {}
    for head in heads:
        if head in commits:
            proc = subprocess.run([*git, "merge-base", "--all", base, head],
                                  capture_output=True, text=True)
            bases = proc.stdout.split()
            if proc.returncode == 0 and len(bases) == 1:
                result[head] = bases[0]
    return result


def historical_declaration_changed(before_objects, after_objects, bodies):
    """Detect a change to an older spelling of a declaration absent in today's form.

    Each side covers the same candidate module paths. The caller resolves moved
    declarations elsewhere before treating a difference as actual overlap.
    """
    before_objects = set(before_objects) - {None}
    after_objects = set(after_objects) - {None}
    if before_objects == after_objects:
        return False
    before = {block for oid in before_objects for block in bodies(oid)}
    if not before:
        return False
    after = {block for oid in after_objects for block in bodies(oid)}
    return before != after
