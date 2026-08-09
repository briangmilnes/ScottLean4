#!/usr/bin/env bash
# a5-r47-conditional.sh — r0047, agent5.
#
# WHAT IT MEASURES.  An `S+H` row in this project's label set is a paper property
# that is *stated* in Lean and whose *proof is open*.  With `sorry` at 0, an open
# proof cannot appear as a hole; it appears as a **conditional theorem** — one
# whose hypothesis list contains a `Prop`-valued claim the development has not
# discharged (or has refuted, in which case the theorem is vacuous).
#
# So the mechanical detector for `S+H` is: find every declaration that takes one
# of the project's open or refuted claims as a hypothesis.  This script emits
# those occurrences per claim, split into the declaring site (`def`) and the
# consuming sites.
#
# WHY IT EXISTS.  r0040 measured the `S+H` rows by hand, section by section, and
# no round since has re-measured them; r0043 re-checked only the `N` rows and
# r0044 only the `S≠` rows.  Six rounds of edits have landed on §§2–6 with no
# instrument watching this label.  grep is used for *discovery* only — every
# candidate it prints is confirmed against the kernel by `a5-r47-probe.lean`.
#
# USAGE: scripts/a5-r47-conditional.sh
# Output: analyses/a5-r47-conditional.txt (and stdout).

set -u

ROOT=/home/milnes/projects/ScottLean4-agent5/ScottDomains
SRC="$ROOT/ScottDomains"
OUT="$ROOT/analyses/a5-r47-conditional.txt"

# The claim census as of r0046 (analyses/zero-props-zero-false-prose.2026-0809-11:40).
OPEN_CLAIMS="Lem30Arrow StepFunctionsDecidable Theorem7ArrowRecursive Theorem7StrictRecursive Lemma30AtV Thm29SecondAtDomains Thm29Normal PreservesRecursivePresentation"
REFUTED_CLAIMS="Thm29Second Lemma28 Lemma30"

{
  echo "# r0047 agent5 — declarations conditional on an open or refuted claim"
  echo "# generated $(date '+%Y-%m-%d %H:%M:%S %Z')"
  echo

  echo "## Open claims — a consumer of one of these is a candidate S+H row"
  for c in $OPEN_CLAIMS; do
    echo
    echo "### $c"
    grep -rn "\b$c\b" "$SRC" --include=*.lean \
      | grep -v '^\s*--' \
      | grep -E "(theorem|lemma|def|abbrev|example)" \
      || echo "  (no declaration-line occurrence)"
  done

  echo
  echo "## Refuted claims — a consumer of one of these is VACUOUS, not conditional"
  for c in $REFUTED_CLAIMS; do
    echo
    echo "### $c"
    grep -rn "\b$c\b" "$SRC" --include=*.lean \
      | grep -E "^\S+:[0-9]+:\s*(theorem|lemma|def|abbrev)" \
      || echo "  (no declaration-line occurrence)"
  done
} > "$OUT" 2>&1

echo "wrote $OUT"
wc -l "$OUT"
