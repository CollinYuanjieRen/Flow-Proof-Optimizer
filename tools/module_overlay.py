"""Link unchanged Lean build products into an isolated compilation directory."""
from collections import defaultdict


def link_unchanged(objects, overlay, changed):
    """Receive changed module paths without extensions, relative to the library root."""
    stems = defaultdict(set)
    for path in changed:
        stems[path.parent].add(path.name)
    branches = {parent for path in changed for parent in path.parents}
    for branch in sorted(branches, key=lambda path: len(path.parts)):
        (overlay / branch).mkdir(parents=True, exist_ok=True)
        for child in (objects / branch).iterdir():
            key = branch / child.name
            stem, dot, _ = child.name.partition(".")
            if key in branches or (dot and stem in stems[branch]):
                continue
            dest = overlay / key
            if not dest.is_symlink() and not dest.exists():
                dest.symlink_to(child)
