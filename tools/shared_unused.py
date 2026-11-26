"""Find theorem helpers that become unused only when several source families are removed."""
from collections import Counter, defaultdict
from pathlib import Path
import sqlite3

from census_report import unpack


def choose_roots(callers):
    """Cover every caller, breaking ties by root name. No minimum-size claim."""
    pending = list(callers.values())
    roots = []
    while pending:
        counts = Counter(root for options in pending for root in options)
        root = min(counts, key=lambda key: (-counts[key], key))
        roots.append(root)
        pending = [options for options in pending if root not in options]
    return roots


def shared_helpers(database, tree, families, exports):
    """families maps (module, root) to its removable local kernel names.

    The result is a source-edit candidate. Attributes, source references and
    the actual kernel delta still need checking after the combined edit.
    """
    members = defaultdict(lambda: defaultdict(set))
    for (module, root), names in families.items():
        for name in names:
            members[module][name].add((module, root))

    with sqlite3.connect(Path(database).resolve().as_uri() + "?mode=ro", uri=True) as db:
        rules, = [r[0] for r in db.execute("SELECT DISTINCT rules FROM snapshot WHERE tree=?", (tree,))]
        modules = dict(db.execute("""
            SELECT s.name, m.id FROM snapshot s LEFT JOIN modules m USING(name,rules,sha)
            WHERE s.tree=? AND s.rules=?
        """, (tree, rules)))
        if None in modules.values():
            raise ValueError("incomplete compiled snapshot")

        def edges(mid):
            blob, = db.execute("SELECT edges FROM modules WHERE id=?", (mid,)).fetchone()
            return unpack(blob)

        wanted = set()
        for module, names in members.items():
            for n, refs in edges(modules[module]):
                if n in names:
                    wanted.update(refs)
        wanted.difference_update(exports)
        ids = set(modules.values())
        candidates = {n for mid, n in db.execute("SELECT module_id,name FROM proofs")
                      if mid in ids and n in wanted}
        owners = {}
        callers = defaultdict(dict)
        for module, mid in modules.items():
            local = members.get(module, {})
            for n, refs in edges(mid):
                if n in candidates:
                    if n in owners:
                        candidates.discard(n)
                    else:
                        owners[n] = module
                for target in refs:
                    if target not in candidates:
                        continue
                    if n not in local:
                        candidates.discard(target)
                    else:
                        callers[target][module, n] = local[n]

    result = []
    for target in sorted(candidates):
        users = callers[target]
        if len(users) < 2 or set.intersection(*users.values()):
            continue
        owner = owners[target]
        if target in members.get(owner, {}):
            continue
        result.append(dict(module=owner, name=target, roots=choose_roots(users),
                           callers=sorted(users)))
    return result
