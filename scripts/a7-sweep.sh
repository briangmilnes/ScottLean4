#!/usr/bin/env bash
# a7-sweep.sh — the r0044 class-4 mechanical sweep: every backticked declaration
# name cited anywhere in the project that does not resolve to a real constant.
#
# Generalizes scripts/r0043-verify-citations.sh, which checked only the five
# r0043 reports and only against a source-lexed list of `theorem`/`lemma`
# openers. Two changes make it usable tree-wide:
#
#   1. the name universe comes from the ELABORATED ENVIRONMENT (a7-dump-env.sh),
#      not from a source lexer, so structure/class projections, inductive
#      constructors, `def`s, instances and Mathlib names all resolve. Those were
#      r0043's three documented false-positive sources and they are now gone by
#      construction rather than by hand-waving;
#   2. the corpus is all 100 `.lean` modules' comments plus every file under
#      docs/, analyses/, plans/ and reports/.
#
# Run scripts/a7-dump-env.sh first (it needs a completed `lake build`).
#
# Output: $SCRATCH/a7-citations.tsv   every scanned citation
#         $SCRATCH/a7-unresolved.tsv  path, line, kind, name, nearest-real-names

set -uo pipefail

wt=/home/milnes/projects/ScottLean4-agent7
pkg="$wt/ScottDomains"
scratch=/tmp/claude-1000/-home-milnes-projects-ScottLean4/ab3f8bb9-d928-40ef-b45c-b2c8efc2bd0e/scratchpad
env_tsv="$scratch/env-names.tsv"
cites="$scratch/a7-citations.tsv"
unres="$scratch/a7-unresolved.tsv"

if [ ! -s "$env_tsv" ]; then
  echo "a7-sweep: $env_tsv missing — run scripts/a7-dump-env.sh first"
  exit 1
fi

list="$scratch/a7-files.txt"
: > "$list"
find "$pkg/ScottDomains" -type f -name '*.lean' >> "$list"
find "$pkg/docs" "$pkg/analyses" "$pkg/plans" "$pkg/reports" -type f \
     \( -name '*.md' -o -name '*.log' -o -name '*.tex' \) >> "$list"

tr '\n' '\0' < "$list" \
  | xargs -0 python3 "$wt/scripts/a7-cite-scan.py" > "$cites"

echo "a7-sweep: scanned $(cut -f1 "$cites" | sort -u | wc -l) files, $(wc -l < "$cites") citations"

python3 "$wt/scripts/a7-resolve.py" \
  "$env_tsv" "$cites" "$wt/scripts/a7-stoplist.txt" "$unres"
