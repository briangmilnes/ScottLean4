#!/usr/bin/env bash
# classical-usage.sh — measure where the development reasons classically.
#
# Why this exists: `#print axioms` answers "which axioms does the kernel need"
# but not "where does the SOURCE reason non-constructively". The two differ.
# Classical.choice enters a footprint through any imported Mathlib lemma, so a
# theorem whose own proof is constructive still reports it. This script measures
# the source-level usage, broken down by construct, so the axiom document can
# separate "we wrote a proof by contradiction" from "Mathlib did".
#
# Output: analyses/classical-usage.<stamp>.orchestrator.log

set -uo pipefail
pkg=/home/milnes/projects/ScottLean4/ScottDomains
src="$pkg/ScottDomains"
out="$pkg/analyses/classical-usage.$(date +%Y%m%d-%H%M%S).orchestrator.log"

count () { grep -rho "$1" "$src" --include='*.lean' | wc -l; }
files () { grep -rl "$1" "$src" --include='*.lean' | wc -l; }

{
  echo "# classical-reasoning usage — $(date '+%Y-%m-%d %H:%M:%S %z')"
  echo
  printf '%-26s %8s %8s\n' construct occurrences files
  printf '%-26s %8s %8s\n' -------------------------- -------- --------
  for c in 'by_contra' 'by_cases' 'push_neg' 'absurd' \
           'Classical\.em' 'Classical\.byContradiction' 'Classical\.choice' \
           'Classical\.dec' 'Classical\.byCases' 'Classical\.' \
           'not_not' 'of_not_not' 'em ' 'Or\.elim' 'exfalso' \
           'open Classical' 'noncomputable'; do
    printf '%-26s %8s %8s\n' "${c//\\/}" "$(count "$c")" "$(files "$c")"
  done
  echo
  echo "## by_contra call sites"
  grep -rn 'by_contra' "$src" --include='*.lean'
  echo
  echo "## Classical.choice / Classical.em written explicitly in source"
  grep -rn 'Classical\.em\|Classical\.choice\|Classical\.byContradiction' \
      "$src" --include='*.lean'
} > "$out"

echo "wrote $out"
