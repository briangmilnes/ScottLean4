#!/bin/bash
# bibliography-cites.sh — which cited works the sources actually lean on.
#
# The project has no .bib file and no \bibitem anywhere; works are cited inline,
# in module docstrings and in the package's prose documents, by author surname.
# This measures, per work held in ScottDomains/papers/, how many Lean modules
# mention it and how many prose documents do, so "we hold this paper" can be told
# apart from "this paper carries proofs we use". Counts are grep hits on the
# surname, so they include passing mentions.
#
# **Why the DOCS columns exist.** Scanning *.lean alone reported Ericson 2026 as
# cited by nothing, when docs/ContinuousLatticeComparison.md is a sustained
# comparison against that formalization — the work carries weight here, in prose
# rather than in a proof. A zero in MODULES means "no proof mentions this", which
# is not the same as uncited, and the two columns now say which is which.
set -u

# The Lean package moved to Dana Scott's own repository in r0094; the papers it
# cites stayed in ScottLean4, in ScottDomains/papers/. Left pointing at the old
# path this script found no .lean files at all and reported 0 for every work,
# which reads exactly like "nothing cites these" -- see the count check below.
PKG=$HOME/projects/ScottProjects/ScottDomains
ROOT=$PKG/ScottDomains

total=$(find "$ROOT" -name '*.lean' 2>/dev/null | wc -l | tr -d ' ')
docs=$(find "$PKG" -name '*.md' -not -path '*/.lake/*' 2>/dev/null | wc -l | tr -d ' ')
if [ "$total" -eq 0 ]; then
  echo "no .lean files under $ROOT -- the package has moved again" >&2
  exit 1
fi

# `grep -c` prints nothing when no file matches, and an empty expression is a
# syntax error to bc, so every sum is seeded with a 0.
sum_lines() {  # sum_lines <glob-root> <include-pattern> <surname>
  grep -rh --include="$2" -w -c "$3" "$1" 2>/dev/null | paste -sd+ - | sed 's/^/0+/' | bc
}

printf '%-12s %8s %8s %8s %8s\n' 'CITED' 'MODULES' 'M-LINES' 'DOCS' 'D-LINES'
for name in Abramsky Jung Plotkin Gunter Mosses Ericson Milner Vaught; do
  modules=$(grep -rl --include='*.lean' -w "$name" "$ROOT" 2>/dev/null | wc -l | tr -d ' ')
  mlines=$(sum_lines "$ROOT" '*.lean' "$name")
  dfiles=$(grep -rl --include='*.md' -w "$name" "$PKG" 2>/dev/null | wc -l | tr -d ' ')
  dlines=$(sum_lines "$PKG" '*.md' "$name")
  printf '%-12s %8s %8s %8s %8s\n' "$name" "$modules" "$mlines" "$dfiles" "$dlines"
done
printf '\n%s .lean modules and %s .md documents scanned under %s\n' "$total" "$docs" "$PKG"
