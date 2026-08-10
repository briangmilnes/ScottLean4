#!/usr/bin/env python3
"""a2-r50-retired-defs.py — repoint the nine retired `Prop`-valued claim `def`s.

Why this exists, and why it is not the compiler-driven path used for the other
131 aliases: Lean's `autoImplicit` option turns an unknown identifier appearing in
a *type* position into an implicitly bound variable instead of reporting it. All
nine of these names are `Prop`-valued `def`s that appear almost exclusively in
type positions, so deleting their aliases does not produce an
`Unknown identifier` at the reference site. Lean reports a downstream symptom
instead — "Function expected at Thm137", "type of theorem … is not a
proposition", "don't know how to synthesize implicit argument
`Thm29SecondAtDomains`" — none of which carries the offset of the stale
identifier. The error-position-driven fixer therefore cannot see these sites.

What makes the substitution here sound anyway: after phase 1 renamed the nine
`def`s and phase 2 deleted their aliases, **no declaration by the old name exists
in the environment**, in this package or in Mathlib. So every token occurrence of
one of these names — in code, in a docstring, in a comment — is a reference to a
declaration that is gone, and there is nothing else it could denote. The match is
anchored on identifier boundaries, so `Thm137` never matches inside `A5Thm137`,
`Thm137Chains`, or `thm137`. The build then confirms the result.

    Thm137 → Theorem137        Thm29Normal → Theorem29Normal        etc.

Usage: a2-r50-retired-defs.py [--dry-run]
"""
import re
import sys
from collections import Counter
from pathlib import Path

ROOT = Path("/home/milnes/projects/ScottLean4-agent2/ScottDomains/ScottDomains")

# The nine phase-1 aliases whose target is a `def`, confirmed by
#   grep -E '^(noncomputable )?(def|abbrev) <new>' over the package.
RENAMES = {
    "Thm29NormalWithoutDomain": "Theorem29NormalWithoutDomain",
    "Thm29SecondAtDomains": "Theorem29SecondAtDomains",
    "Thm29Normal": "Theorem29Normal",
    "Thm29Second": "Theorem29Second",
    "Thm26Printed": "Theorem26Printed",
    "Thm137Chains": "Theorem137Chains",
    "Thm137Omega": "Theorem137Omega",
    "Thm137": "Theorem137",
    "Lem30Arrow": "Lemma30Arrow",
}

# `\b` is not enough on its own: Lean identifiers admit `'`, `!`, `?` and `_`, and
# a `\b` before `Thm137` would still fire in `A5Thm137` were it not that `5` is a
# word character. Spell both boundaries out so the rule does not depend on that.
IDENT = r"[A-Za-z0-9_'!?]"
PAT = re.compile(
    r"(?<!" + IDENT + r")(" + "|".join(
        sorted(map(re.escape, RENAMES), key=len, reverse=True)) + r")(?!" + IDENT + r")")


def main():
    dry = "--dry-run" in sys.argv
    total = Counter()
    for path in sorted(ROOT.rglob("*.lean")):
        text = path.read_text()
        hits = Counter(m.group(1) for m in PAT.finditer(text))
        if not hits:
            continue
        new = PAT.sub(lambda m: RENAMES[m.group(1)], text)
        if not dry:
            path.write_text(new)
        total.update(hits)
        print(f"{path.relative_to(ROOT)}\t{sum(hits.values())}")
    print("--- per identifier ---")
    for name, n in total.most_common():
        print(f"{n}\t{name}\t-> {RENAMES[name]}")
    print(f"total occurrences: {sum(total.values())}")


main()
