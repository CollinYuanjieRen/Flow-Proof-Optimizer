"""Propose sharing two entire tactic proofs differing by hypothesis projections."""

import re


def projection_variants(body, args):
    """Remove one field access on an introduced hypothesis at every matching occurrence."""
    fields = re.compile(r"(?<![\w.'])([^\W\d][\w']*)(\.[\w']+)(?![\w.'])")
    eligible = set(args)
    spans = {}
    for match in fields.finditer(body):
        if match[1] in eligible:
            spans.setdefault(match.groups(), []).append(match.span(2))
    for (arg, projection), cuts in sorted(spans.items()):
        chunks = []
        start = 0
        for a, b in cuts:
            chunks.append(body[start:a])
            start = b
        yield arg, projection, "".join([*chunks, body[start:]])


# Keep dot projections together and strings opaque. This is a candidate filter.
PROOF_TOKENS = re.compile(r'''"(?:\\.|[^"\\])*"|[\w']+(?:\.[\w']+)*|[^\s]''')


def projected_intro_arguments(strong, general):
    """Infer arguments to the general proof by aligning uses after the two intros."""
    def parameters(body):
        first = body[0].split()
        if first[:1] != ["intro"]:
            return []
        args = first[1:]
        return args if all(x.isidentifier() for x in args) and len(set(args)) == len(args) else []

    params, args = parameters(general), parameters(strong)
    if not params or not args:
        return None
    strong_tokens = PROOF_TOKENS.findall("".join(strong[1:]))
    general_tokens = PROOF_TOKENS.findall("".join(general[1:]))
    if len(strong_tokens) != len(general_tokens):
        return None
    bindings = {}
    for given, expected in zip(strong_tokens, general_tokens):
        name, dot, rest = expected.partition(".")
        if name not in params:
            if given != expected:
                return None
            continue
        suffix = dot + rest
        if not given.endswith(suffix):
            return None
        value = given.removesuffix(suffix)
        if value.split(".", 1)[0] not in args or bindings.setdefault(name, value) != value:
            return None
    values = [bindings.get(name, name if name in args else None) for name in params]
    if None in values:
        return None
    return values


def project_whole_pair(original, sites, declarations, helper):
    """The first module provides the helper. All proposed source still requires strict replay."""
    if len(sites) != 2 or sites[0].module == sites[1].module:
        return None
    parts = []
    for site in sites:
        decl = declarations[site.module][site.owner]
        block = original[site.module][site.owner_start:decl["last_line"]]
        cut = next((i + 1 for i, s in enumerate(block) if s.rstrip().endswith(":= by")), None)
        if cut is None or cut == len(block):
            return None
        parts.append((block[:cut], block[cut:]))
    # The more general statement can come from a downstream module.
    for strong, general in ((0, 1), (1, 0)):
        strong_body = parts[strong][1]
        header, general_body = parts[general]
        args = projected_intro_arguments(strong_body, general_body)
        if args is None:
            continue
        old_name = "theorem " + sites[general].written_owner + " "
        if header[0].count(old_name) != 1:
            return None
        lemma = [header[0].replace(old_name, "theorem _root_." + helper + " ", 1),
                 *header[1:], *general_body, "\n"]
        result = {}
        for i, site in enumerate(sites):
            proof = ["  exact @_root_." + helper + "\n"]
            if i == strong:
                proof = [strong_body[0], "  exact @_root_." + helper + " " + " ".join(args) + "\n"]
            replacement = (lemma if i == 0 else []) + parts[i][0] + proof
            lines = original[site.module]
            stop = declarations[site.module][site.owner]["last_line"]
            result[site.module] = lines[:site.owner_start] + replacement + lines[stop:]
        return result
    return None
