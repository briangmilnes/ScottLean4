#!/usr/bin/env python3
"""a7-resolve.py — match scanned citations against the elaborated environment.

Input: the TSV from `a7-cite-scan.py` ("path<TAB>line<TAB>kind<TAB>name") and the
environment dump from `a7-dump-env.sh` ("module<TAB>full-name").

--------------------------------------------------------------------------------
Shape filter, applied first
--------------------------------------------------------------------------------
A backtick span that is identifier-shaped is usually NOT a declaration citation.
Measured on the first full pass: of 2961 unresolved sites, the large majority
were local variables and hypothesis names quoted in docstring prose (`g`, `t`,
`S_f`, `p_N`, `a₁`, `hmono`, `ψ`), tool names (`grep`, `pdftotext`, `lake`), and
projection notation on a local (`q.val`). None is a claim about a declaration.

`plausible()` keeps only tokens with the shape this development's declaration
names actually have. It is deliberately conservative — its cost in recall is
measured and reported (see a7-recall-cost in the r0044 report), because a noisy
list is not usable and precision is the stated priority.

    * must contain a lowercase letter          drops `N`, `D`, `PATH`, `T`
    * dotted   -> first component uppercase    drops `q.val`, `v4.32.2`
    * underscored -> >= 2 components of len>=2 drops `S_f`, `fix_D`, `_bot`
    * bare word -> Uppercase and len >= 4      drops `grep`, `smash`, `hmono`

--------------------------------------------------------------------------------
Resolution tiers
--------------------------------------------------------------------------------
  exact       the token IS a full constant name (`Function.cantor_surjective`).
  pkg-suffix  a component-boundary suffix of a constant declared in a
              `ScottDomains.*` module — how our docs cite our own declarations.
  module      the token names a MODULE (`JungFinite`, `Skeleton.Section6`). A
              module is not a constant, so it cannot resolve above, but citing
              one is correct and common. Taken from the dump's module column.
  namespace   the token names a NAMESPACE (`ScottDomains.Isomorphism`, `Flat`),
              derived as the proper dotted prefixes of our constants. Also not a
              constant, also a correct citation.
  ext-suffix  a component-boundary suffix only of a Mathlib/core constant.
              Reported separately: suffix-matching 265k external names resolves
              nearly anything, and this is the one tier that can hide a defect.

Matching is on COMPONENT BOUNDARIES, never substring or prefix. That distinction
is the whole instrument: `smyth_oneBot_eq_bot` is a proper prefix of the real
`smyth_oneBot_eq_bot_eq_unit_bot`, and a prefix or substring test would call the
known-false citation resolved.

Anything in no tier is unresolved and reported, with the nearest real package
names as a "what it probably meant" hint.

Usage:
    a7-resolve.py <env-names.tsv> <citations.tsv> <stoplist.txt> <out.tsv>
"""

import sys
from collections import defaultdict

PKG = "ScottDomains"

# Lean sorts and syntactic categories: keywords, not constants.
BUILTIN = {"Prop", "Type", "Sort"}

# Sentence cues that a name is cited AS EVIDENCE OF ITS OWN ABSENCE — a zero-hit
# grep, a retired declaration, a list of name variants searched for, or a
# prescription about a name not to introduce. Non-resolution is the CORRECT
# outcome at such a site, so these are separated out rather than counted as
# defects. r0043 documented this class; it is the single largest false-positive
# source in docs/, analyses/, plans/ and reports/, measured at 18 of 35 sampled
# prose sites before this test existed.
ABSENCE_CUES = (
    "there is no", "there are no", "has no", "have no", "had no", "is no ",
    "are no ", "not exist", "doesn't exist", "does not exist",
    "zero hit", "zero occurrence", "0 hits", "returns nothing",
    "returned nothing", "returns zero", "returned zero", "not a live",
    "do not add", "must not", "should not", "was retired", "were retired",
    "not needed", "unnecessary", "searched for", "no biconditional",
    "not formalized", "not formalised", "no predicate",
    # A bare "no `Name`" — the commonest phrasing of a zero-hit grep in these
    # docstrings, e.g. "and Mathlib has no `OrderIso.prodCongr`".
    "no `",
)
# Cues deliberately NOT used, each having been measured to suppress a real
# defect: "never" (`…not_maps_compacts`. It was never the…), "no such" (the
# Egli-Milner order admits no such join — `Plotkin.not_single_le_pair` already
# shows…), and "missing"/"absent"/"grep"/"retired"/"nowhere"/"no longer", which
# fire on ordinary prose about the development's history. Removing them
# restored 3 of 17 suppressed .lean sites.


def absence_claim(ctx):
    """True when the containing line asserts the cited name is NOT present."""
    low = ctx.lower()
    return any(cue in low for cue in ABSENCE_CUES)


def plausible(tok):
    """True when the token has the shape of a declaration name in this tree."""
    if tok in BUILTIN:
        return False
    if not any(c.islower() for c in tok):
        return False
    # A leading underscore marks a quoted name FRAGMENT, not a name: reports
    # write `_of_ne`, `_of_empty`, `_smash_iff` to describe a naming pattern.
    # A trailing or doubled dot is a malformed span (`Combinator.`).
    if tok.startswith("_") or tok.endswith(".") or ".." in tok:
        return False
    if "." in tok:
        # `IsLUB.2` is anonymous-constructor projection on a term, not a name.
        if tok.split(".")[-1].isdigit():
            return False
        # `G.val`, `A.carrier`: projection applied to a local whose name is a
        # single capital. No namespace in this tree is one character long.
        if len(tok.split(".")[0]) == 1:
            return False
        return tok[0].isupper()
    if "_" in tok:
        return sum(1 for p in tok.split("_") if len(p) >= 2) >= 2
    return tok[0].isupper() and len(tok) >= 4


def suffixes(name):
    """Component-boundary suffixes of a dotted name."""
    parts = name.split(".")
    for i in range(len(parts)):
        yield ".".join(parts[i:])


def prefixes(name):
    """Proper dotted prefixes of a name — its enclosing namespaces."""
    parts = name.split(".")
    for i in range(1, len(parts)):
        yield ".".join(parts[:i])


def main():
    if len(sys.argv) != 5:
        raise SystemExit(__doc__)
    env_path, cite_path, stop_path, out_path = sys.argv[1:5]

    full = set()
    pkg_suffix = defaultdict(set)
    ext_suffix = set()
    modules = set()
    namespaces = set()
    # module-suffix -> declaration tails declared in that module. Our docs
    # routinely qualify a declaration by the MODULE it lives in rather than by
    # its namespace, and the two differ throughout this tree: e.g.
    # `ScottDomains.directedOn_val_smashBase` is declared in module
    # `ScottDomains.Smash` but sits in namespace `ScottDomains`, so the docstring
    # citation `Smash.directedOn_val_smashBase` names no constant while naming
    # exactly one real declaration unambiguously. That is a citation convention,
    # not a false claim, and counting it as a defect would be wrong.
    mod_decls = defaultdict(set)
    # last component -> (full name, declaring module) for OUR declarations only.
    tail_index = defaultdict(list)
    with open(env_path, encoding="utf-8", errors="replace") as fh:
        for line in fh:
            if "\t" not in line:
                continue
            mod, name = line.rstrip("\n").split("\t", 1)
            full.add(name)
            modules.add(mod)
            ours = mod == PKG or mod.startswith(PKG + ".")
            for s in suffixes(name):
                if ours:
                    pkg_suffix[s].add(name)
                else:
                    ext_suffix.add(s)
            if ours:
                for p in prefixes(name):
                    namespaces.add(p)
                tail = name.split(".")[-1]
                for ms in suffixes(mod):
                    mod_decls[ms].add(tail)
                tail_index[tail].append((name, mod))

    def misqualified(tok):
        """Classify a name that does not elaborate. Returns (category, real, n).

        `n` is how many package declarations share the cited LAST COMPONENT, so
        a reader can see when the identification is unique and when the last
        component is generic.

        wrong-module-qualifier
            the qualifier's components all occur in the real name or in its
            DECLARING MODULE — the module-path-used-as-namespace error.
            `Smash.directedOn_val_smashBase` names nothing;
            `ScottDomains.directedOn_val_smashBase` is declared in module
            `ScottDomains.Smash`. Mechanically certain, and systematic.
        wrong-qualifier
            the last component is a real declaration of ours but the qualifier
            matches neither its namespace nor its module.
            `ClosureProperties.lem17_fun` for `ScottDomains.lem17_fun`, which is
            declared in module `ScottDomains.Skeleton.Lemma17`. Confident when
            n == 1; when the last component is generic (`le`, `map`, `comp`)
            n is large and the citation names nothing identifiable.
        nonexistent
            no package declaration has that last component at all.
        """
        if "." not in tok:
            return ("nonexistent", "", 0)
        head, last = tok.rsplit(".", 1)
        cands = tail_index.get(last, [])
        if not cands:
            return ("nonexistent", "", 0)
        hcomps = set(head.split("."))
        for fname, fmod in cands:
            if hcomps <= set(fname.split(".")) | set(fmod.split(".")):
                return ("wrong-module-qualifier", fname, len(cands))
        return ("wrong-qualifier", cands[0][0], len(cands))

    # Modules that declare no constant never appear in the dump's module column,
    # so take the authoritative list from the tree as well.
    try:
        with open(env_path + ".modules", encoding="utf-8") as fh:
            for line in fh:
                if line.strip():
                    modules.add(line.strip())
    except OSError:
        pass

    mod_names = set()
    for m in modules:
        for s in suffixes(m):
            mod_names.add(s)
    ns_names = set()
    for n in namespaces:
        for s in suffixes(n):
            ns_names.add(s)

    stop = set()
    try:
        with open(stop_path, encoding="utf-8") as fh:
            for line in fh:
                line = line.split("#", 1)[0].strip()
                if line:
                    stop.add(line)
    except OSError:
        pass

    rows = []
    tally = defaultdict(int)
    # Recall cost: how many citations that DO resolve would the shape filter
    # have thrown away? Reported so the filter's cost is a number, not a claim.
    shaped_out_but_real = 0
    with open(cite_path, encoding="utf-8", errors="replace") as fh:
        for line in fh:
            parts = line.rstrip("\n").split("\t")
            if len(parts) < 4:
                continue
            path, ln, kind, tok = parts[:4]
            ctx = parts[4] if len(parts) > 4 else ""
            window = parts[5] if len(parts) > 5 else ctx
            tally["scanned"] += 1
            resolves = (tok in full or tok in pkg_suffix or tok in mod_names
                        or tok in ns_names or tok in ext_suffix)
            if not plausible(tok):
                tally["shape-filtered"] += 1
                if resolves:
                    shaped_out_but_real += 1
                continue
            if tok in stop:
                tally["stoplisted"] += 1
                continue
            tally["considered"] += 1
            if tok in full:
                tally["exact"] += 1
            elif tok in pkg_suffix:
                tally["pkg-suffix"] += 1
            elif tok in mod_names:
                tally["module"] += 1
            elif tok in ns_names:
                tally["namespace"] += 1
            elif tok in ext_suffix:
                tally["ext-suffix"] += 1
            else:
                cat, real, ncand = misqualified(tok)
                if absence_claim(window):
                    cat = "absence-claim"
                tally[cat] += 1
                rows.append((path, int(ln), kind, tok, cat,
                             real if not real else "%s (n=%d)" % (real, ncand),
                             ctx))

    # "What it probably meant": real package names sharing the token's first
    # underscore-component, ranked by longest common prefix.
    by_head = defaultdict(list)
    for s in pkg_suffix:
        if "." not in s:
            by_head[s.split("_")[0]].append(s)

    def near(tok):
        tail = tok.split(".")[-1]
        cands = by_head.get(tail.split("_")[0], [])

        def common(a, b):
            i = 0
            while i < min(len(a), len(b)) and a[i] == b[i]:
                i += 1
            return i

        return sorted(cands, key=lambda c: (-common(c, tail), len(c)))[:3]

    order = {"lean-doc": 0, "lean-comment": 1, "prose": 2}
    rows.sort(key=lambda r: (r[4], order.get(r[2], 3), r[0], r[1]))
    with open(out_path, "w", encoding="utf-8") as out:
        for path, ln, kind, tok, cat, real, ctx in rows:
            hint = real if real else ";".join(near(tok))
            out.write("%s\t%d\t%s\t%s\t%s\t%s\t%s\n"
                      % (path, ln, kind, tok, cat, hint, ctx[:200]))

    for k in ("scanned", "shape-filtered", "stoplisted", "considered", "exact",
              "pkg-suffix", "module", "namespace", "ext-suffix", "absence-claim",
              "wrong-module-qualifier", "wrong-qualifier", "nonexistent"):
        print("%-16s %d" % (k, tally[k]))
    print("%-16s %d" % ("distinct-reported", len({r[3] for r in rows})))
    print("shape filter discarded %d citations that WOULD have resolved "
          "(recall cost)" % shaped_out_but_real)
    print("wrote %s" % out_path)


if __name__ == "__main__":
    main()
