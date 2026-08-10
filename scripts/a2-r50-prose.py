#!/usr/bin/env python3
"""a2-r50-prose.py — repoint retired names cited in docstrings and comments.

Why this exists: phase 2's compiler-driven pass fixes every *reference site*,
because the elaborator reports one at each. It cannot report a retired name
written inside a docstring or a comment — yet after the aliases are deleted such
a citation names a declaration that no longer exists anywhere in the package or
in Mathlib, so it is exactly as stale as a code reference and is a defect of the
same kind. Leaving 474 of them would mean fixing one symptom class and shipping
the other.

This substitutes a name for a name. It changes no statement, no proof, no binder,
and no claim: the sentence around the identifier is untouched.

Two guards run before anything is written, and the script refuses to act if
either fails:

  1. No retired name may map to two different new names. (Several names are
     defined in two modules — `lem17_fun`, `thm27` — which is fine only because
     both copies were renamed the same way.)
  2. No retired name may still be a live declaration. The map is built from the
     alias inventory, but a *third* module could define the same short name and
     never have been renamed; substituting there would point prose at the wrong
     result. Checked against every `theorem`/`lemma`/`def`/`abbrev`/`instance`
     binding in the package.

Matching is anchored on Lean identifier boundaries and longest-name-first, so
`thm18` never fires inside `thm18_of_propertyM` and `lem24` never inside
`lemma24_MPair`.

Usage: a2-r50-prose.py [--dry-run]
"""
import re
import sys
from collections import Counter, defaultdict
from pathlib import Path

ROOT = Path("/home/milnes/projects/ScottLean4-agent2/ScottDomains/ScottDomains")
MAP_TSV = ROOT.parent / "analyses" / "a2-r50-aliases.tsv"

IDENT = r"[A-Za-z0-9_'!?]"

targets = defaultdict(set)
for line in MAP_TSV.read_text().splitlines():
    if line and not line.startswith("#"):
        _f, _s, _e, old, new = line.split("\t")
        targets[old].add(new)

ambiguous = {o: v for o, v in targets.items() if len(v) > 1}
if ambiguous:
    print("REFUSED — a retired name maps to more than one new name:")
    for o, v in ambiguous.items():
        print(f"  {o} -> {sorted(v)}")
    sys.exit(1)

RENAMES = {o: next(iter(v)) for o, v in targets.items()}

# Guard 2: is any retired name still bound by a live declaration?
DECL = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+|partial\s+)*"
    r"(?:theorem|lemma|def|abbrev|instance|structure|inductive)\s+([A-Za-z_][^\s({\[:]*)")
live = Counter()
for path in ROOT.rglob("*.lean"):
    for row in path.read_text().splitlines():
        mo = DECL.match(row)
        if mo and mo.group(1) in RENAMES:
            live[mo.group(1)] += 1
if live:
    print("REFUSED — a retired name is still a live declaration:")
    for o, n in live.items():
        print(f"  {o} ({n} bindings)")
    sys.exit(1)

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
        if not dry:
            path.write_text(PAT.sub(lambda m: RENAMES[m.group(1)], text))
        total.update(hits)
        print(f"{path.relative_to(ROOT)}\t{sum(hits.values())}")
    print("--- per name ---")
    for name, n in total.most_common():
        print(f"{n}\t{name}\t-> {RENAMES[name]}")
    print(f"total occurrences: {sum(total.values())}")


main()
