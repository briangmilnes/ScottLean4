#!/usr/bin/env python3
"""a8-r49-absence.py — r0049 / agent8: decide the LOCUS of every absence claim
whose subject is an English noun phrase rather than a backticked name.

--------------------------------------------------------------------------------
The gap this closes
--------------------------------------------------------------------------------
r0046's `a4-claim-scan.py` asks the elaborated environment about a claim's
subject, and can only do so when the subject is a backticked name. It writes the
rest to `<out>.unresolvable` — 52 sites at r0046, 55 on this tree — and issues no
verdict on any of them. That list is the instrument's whole recall gap: it is
where r0046's sites 7 and 8 hid ("this development **has no strict-step-function
basis** to enumerate" — the subject is `strict-step-function basis`, which names
no constant).

r0046's own recommendation was "a rule that maps a claimed-absent noun phrase to
a class or namespace by keyword". This is that rule, and it is deliberately
weaker than a verdict: it decides WHERE the claim would have to be checked, not
whether it holds. That is the honest strength of a keyword test, and it is
enough — the three loci need three different probes, and mixing them is what
made the 52 a single undifferentiated pile.

  QUOTE    the sentence sits in a `>` blockquote: the PAPER asserts the absence,
           or another author does. Not this development's claim. Convicting it
           is the error the round's evidence rules name.

  MATHLIB  the sentence names Mathlib, a `Mathlib/...` path, or a version of it.
           Probe: `exact?` on the STATEMENT in a Mathlib environment, never a
           grep for the name — r0046 established that a name search decides
           nothing (`RePred` was absent under that name and present as
           `Nat.RePred`, and `Primcodable (Finset ℕ)` was asserted absent and
           synthesizes).

  MODULE   the sentence names scope token 3 or 4 of `docs/ScopedClaims.md` — "in
           this module", "in this file", "at this point in the import order".
           Probe: one file, or one import cone, not the package. A claim at this
           scope does not go stale when a LATER module supplies the thing, which
           is the whole reason the convention distinguishes it. Reported and not
           counted as a standing obligation.

  PKG      the sentence says THIS DEVELOPMENT / this package / this tree lacks
           something, with no narrower scope named. Probe: the declaration index
           from `a4-decl-query.lean`, searched by the keyword the noun phrase
           supplies. These are the checkable ones, and they are the ones that go
           stale, because the tree grows and the sentence does not.

  MATH     no locus: the subject is a mathematical object and the claim is a
           theorem about it (`{a, b}` has no least upper bound; `∅` has no
           element to place a bound under). The surrounding proof elaborates,
           so the claim is already kernel-checked in situ. No standing
           obligation.

Order of tests matters and is fixed: QUOTE, MATHLIB, MODULE, PKG, MATH — widest
authority first, then narrowest scope first. A sentence naming both Mathlib and
this development is about the Mathlib gap: measured, every such sentence in this
corpus reads "Mathlib has no X, so we build it here". A sentence naming both a
module scope and the package is at the module scope, because naming the narrower
one is the deliberate act the convention asks for.

--------------------------------------------------------------------------------
Usage
--------------------------------------------------------------------------------
    a8-r49-absence.py <claims.tsv.unresolvable> <out.tsv>

Work: O(|rows| * |cues|); span: one pass.
"""

import re
import sys
from collections import defaultdict

MATHLIB = re.compile(
    r"\bMathlib\b|`Mathlib/|\bMathlib's\b|\bcore\b(?= *(?:Lean|library))", re.I)

# Scope tokens 3 and 4 of docs/ScopedClaims.md. Tested BEFORE PKG: a sentence
# that names the module scope has done what the convention asks, and counting it
# as a package-wide obligation is the misreading the convention exists to stop.
MODULE = re.compile(
    r"\bthis module\b|\bthe module\b|\bthis file\b|\bin this section\b"
    r"|\bat this point in the import order\b", re.I)

# "this development" and its variants. `\bthe development\b` is included because
# the corpus uses it as often as "this development"; `anywhere in the tree` and
# `in this package` are the other two forms measured.
PKG = re.compile(
    r"\bthis development\b|\bthe development\b|\bthis package\b|\bthe package\b"
    r"|\bthis tree\b|\bthe tree\b|\bin this library\b|\bthis library\b"
    r"|\banywhere in\b|\bnowhere in\b|\bin the development\b|\bto prove\b", re.I)

QUOTE = re.compile(r"(^|\s)> ")


def locus(text):
    if QUOTE.search(text):
        return "QUOTE"
    if MATHLIB.search(text):
        return "MATHLIB"
    if MODULE.search(text):
        return "MODULE"
    if PKG.search(text):
        return "PKG"
    return "MATH"


def main():
    if len(sys.argv) != 3:
        raise SystemExit(__doc__)
    src, out_path = sys.argv[1:3]

    rows = []
    with open(src, encoding="utf-8") as fh:
        for line in fh:
            cols = line.rstrip("\n").split("\t")
            if len(cols) < 5:
                continue
            path, lineno, kind, cue, text = cols[0], cols[1], cols[2], cols[3], cols[4]
            idx = path.find("/ScottDomains/")
            rel = path[idx + 1:] if idx >= 0 else path
            rows.append((locus(text), "%s:%s" % (rel, lineno), kind, cue, text))

    rows.sort()
    with open(out_path, "w", encoding="utf-8") as out:
        out.write("# a8-r49-absence.py — r0049/agent8. locus, site, kind, cue, text\n")
        for r in rows:
            out.write("\t".join(r) + "\n")

    tally = defaultdict(int)
    for r in rows:
        tally[r[0]] += 1
    print("unbackticked absence claims: %d" % len(rows))
    for k in ("QUOTE", "MATHLIB", "MODULE", "PKG", "MATH"):
        print("  %-8s %3d" % (k, tally[k]))
    print("wrote %s" % out_path)


if __name__ == "__main__":
    main()
