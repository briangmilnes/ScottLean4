#!/bin/bash
# bibliography-cites.sh — which cited works the Lean sources actually lean on.
#
# The project has no .bib file and no \bibitem anywhere; works are cited inline
# in module docstrings by author surname. This measures, per work held in
# ScottDomains/papers/, how many Lean modules mention it and how many lines do,
# so "we hold this paper" can be told apart from "this paper carries proofs we
# use". Counts are grep hits on the surname, so they include prose mentions.
set -u

# The Lean package moved to Dana Scott's own repository in r0094; the papers it
# cites stayed here, in ScottDomains/papers/. Left pointing at the old path this
# script found no .lean files at all and reported 0 for every work, which reads
# exactly like "nothing cites these" -- see the count check below.
ROOT=$HOME/projects/ScottProjects/ScottDomains/ScottDomains

total=$(find "$ROOT" -name '*.lean' 2>/dev/null | wc -l | tr -d ' ')
if [ "$total" -eq 0 ]; then
  echo "no .lean files under $ROOT -- the package has moved again" >&2
  exit 1
fi

printf '%-12s %8s %8s\n' 'CITED' 'MODULES' 'LINES'
for name in Abramsky Jung Plotkin Gunter Mosses Ericson Milner Vaught; do
  modules=$(grep -rl --include='*.lean' -w "$name" "$ROOT" | wc -l | tr -d ' ')
  # `grep -c` prints nothing when no file matches, and an empty expression is a
  # syntax error to bc, so the sum is seeded with a 0.
  lines=$(grep -rh --include='*.lean' -w -c "$name" "$ROOT" | paste -sd+ - | sed 's/^/0+/' | bc)
  printf '%-12s %8s %8s\n' "$name" "$modules" "$lines"
done
printf '\n%s .lean modules scanned under %s\n' "$total" "$ROOT"
