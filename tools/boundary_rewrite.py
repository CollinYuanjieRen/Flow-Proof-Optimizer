"""Render a shared proof and its calls for simple explicitly written Lean binders.

The caller supplies compiler reference tables, kernel boundary cuts in dependency
order, a helper name and fresh display names. Re-elaboration and instantiation
replay decide whether the proposed source change preserves the original proofs.
"""
import argparse
import json
from pathlib import Path
import re

from private_duplicate import source_span


def groups(source, start, stop):
    """Read consecutive named binder groups following a declaration name."""
    delimiters = {"(": ")", "{": "}", "[": "]"}
    result = []
    while start < stop:
        if source[start].isspace():
            start += 1
            continue
        if source[start] not in delimiters:
            break
        stack = []
        for end in range(start, stop):
            c = source[end]
            if c in delimiters:
                stack.append(delimiters[c])
            elif c in delimiters.values():
                if stack.pop() != c:
                    raise ValueError("unsupported delimiter in declaration header")
                if not stack:
                    break
        else:
            raise ValueError("unterminated binder")
        inside = source[start + 1:end]
        names, colon, typ = inside.partition(":")
        names = names.split()
        if not colon or not names or not all(re.fullmatch(r"[^\W\d][\w']*", n) for n in names):
            raise ValueError("expected typed, named binders")
        result.append((source[start], names, typ.strip(), end + 1))
        start = end + 1
    if source[start:start + 1] != ":":
        raise ValueError("expected declaration result type")
    return result, start + 1


def edits_for_cuts(source, info, span, owner, cuts, labels, bounds):
    edits = []
    wanted = {cut["name"]: (cut, label) for cut, label in zip(cuts, labels, strict=True)}
    refs = iter(info["references"])
    for key, data in zip(refs, refs, strict=True):
        if len(key) != 3 or key[0] != 0 or key[2] not in wanted:
            continue
        cut, label = wanted[key[2]]
        args = cut["explicitCallerArguments"]
        pattern = "".join(r"[ \t]+" + re.escape(arg) for arg in args) + r"(?=$|[\s,;)\]])"
        for use in data["usages"]:
            if use[-1] != owner:
                continue
            a, z = span(use)
            if not bounds[0] <= a < z <= bounds[1]:
                continue
            match = re.match(pattern, source[z:bounds[1]])
            if match:
                z += match.end()
                if (bounds[0] < a and z < bounds[1] and source[a-1] == "(" and source[z] == ")"
                        and (a == 1 or source[a-2].isspace() or source[a-2] == "(")):
                    a -= 1
                    z += 1
            elif not (re.search(r"\b(?:simp(?: only)?|rw)\s*\[[^\]]*$",
                                source[source.rfind("\n", 0, a) + 1:a])
                      and source[z:bounds[1]].lstrip().startswith((",", "]"))):
                raise ValueError(f"unsupported written arguments for {cut['name']}")
            edits.append((a, z, label))
    return edits


def render(source, bounds, edits):
    start, stop = bounds
    pieces = []
    for a, b, replacement in sorted(edits):
        if not start <= a <= b <= stop:
            raise ValueError("overlapping or out-of-range source edits")
        pieces.extend((source[start:a], replacement))
        start = b
    pieces.append(source[start:stop])
    return "".join(pieces)


def parameter_annotation(source, info, owner, cut, earlier, labels):
    span = source_span(source)
    decl = info["decls"][owner]
    _, start = span(decl[4:])
    _, stop = span(decl)
    binders, start = groups(source, start, stop)
    stop = source.index(":=", start, stop)
    bounds = start, stop
    result = render(source, bounds, edits_for_cuts(source, info, span, owner, earlier, labels, bounds)).strip()
    remaining = []
    for opening, names, typ, _ in binders:
        if set(names) <= set(cut["binders"]):
            continue
        if opening != "(" or set(names).intersection(cut["binders"]):
            raise ValueError("unsupported remaining provider binder")
        remaining.append("∀ " + " ".join(names) + " : " + typ + ", ")
    return "".join(remaining) + result


def render_caller(source, info, owner, cuts, helper, labels, annotations=None):
    span = source_span(source)
    decl = info["decls"][owner]
    start, end = span(decl)
    ns, nz = span(decl[4:])
    binders, result = groups(source, nz, end)
    needed = {n for cut in cuts for n in cut["binders"]}
    used = [(i, pos) for i, (_, names, _, pos) in enumerate(binders) if needed.intersection(names)]
    if not used:
        raise ValueError("no written boundary binder")
    i, insert = used[-1]
    left = [n for opening, names, _, _ in binders[:i+1] if opening == "(" for n in names]
    right = [n for opening, names, _, _ in binders[i+1:] if opening == "(" for n in names]
    inst = ["(" + " ".join([c["name"], *c["explicitCallerArguments"]]) + ")" for c in cuts]
    call = "  exact _root_." + helper + " " + " ".join(left + inst + right)
    if annotations is None:
        return call, None
    if source[start:ns] not in ("private theorem ", "private lemma "):
        raise ValueError("expected a private proof")
    signature = " ".join(f"({n} : {t})" for n, t in zip(labels, annotations, strict=True))
    edits = [(start, nz, "theorem " + helper.rsplit(".", 1)[-1]), (insert, insert, "\n    " + signature)]
    edits.extend(edits_for_cuts(source, info, span, owner, cuts, labels, (result, end)))
    return call, render(source, (start, end), edits)


def proposal(candidate, cuts, donor, source, library, helper, labels):
    def inputs(module):
        path = Path(*module.split("."))
        return ((source / path).with_suffix(".lean").read_text(),
                json.loads((library / path).with_suffix(".ilean").read_bytes()))

    ordered = [[c["name"] for c in side] for side in cuts]
    if (len(labels) != len(set(labels)) or len(ordered[0]) != len(labels)
            or set(zip(*ordered, strict=True)) != {(a, b) for a, b, n in candidate["differing"]}):
        raise ValueError("parameter names or correspondence do not match the candidate")
    for left, right in zip(*cuts, strict=True):
        if (left["binderIndices"], left["priorParameters"]) != (right["binderIndices"], right["priorParameters"]):
            raise ValueError("incompatible application positions or dependencies")
    module, owner = candidate["callers"][donor]
    _, info = inputs(module)
    refs = iter(info["references"])
    owners = {key[2]: key[1] for key, data in zip(refs, refs, strict=True)
              if len(key) == 3 and key[0] == 0 and
              any(use[-1] == owner for use in data["usages"])}
    annotations = []
    for i, cut in enumerate(cuts[donor]):
        name = cut["name"]
        annotations.append(parameter_annotation(*inputs(owners[name]), name, cut, cuts[donor][:i], labels[:i]))
    calls = []
    for i, (module, owner) in enumerate(candidate["callers"]):
        call, body = render_caller(*inputs(module), owner, cuts[i], helper, labels,
                                   annotations if i == donor else None)
        calls.append(call)
        if i == donor:
            declaration = body
    return {"helper": declaration, "calls": calls}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("scan", type=Path, help="caller_boundaries.py output")
    parser.add_argument("source", type=Path)
    parser.add_argument("library", type=Path)
    parser.add_argument("cuts", nargs=2, type=Path, help="ProofPairs --boundary-cuts outputs, in caller order")
    parser.add_argument("--candidate", type=int, default=0)
    parser.add_argument("--donor", type=int, choices=(0, 1), required=True)
    parser.add_argument("--helper", required=True)
    parser.add_argument("--labels", nargs="+", required=True)
    args = parser.parse_args()
    row = json.loads(args.scan.read_bytes())["candidates"][args.candidate]
    cuts = [json.loads(p.read_bytes()) for p in args.cuts]
    print(json.dumps(proposal(row, cuts, args.donor, args.source, args.library, args.helper, args.labels),
                     indent=2, ensure_ascii=False))
