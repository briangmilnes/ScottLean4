#!/usr/bin/env bash
# a7-report-data.sh — emit the tables the r0044 agent7 report quotes, so every
# number in the report is reproducible from the sweep output rather than typed.
#
# Output: $SCRATCH/a7-report-data.txt

set -uo pipefail
scratch=/tmp/claude-1000/-home-milnes-projects-ScottLean4/ab3f8bb9-d928-40ef-b45c-b2c8efc2bd0e/scratchpad
out="$scratch/a7-report-data.txt"

{
  echo "=== defect sites by category and kind ==="
  awk -F'\t' '{print $5"\t"($3=="prose"?"prose":"lean")}' \
    "$scratch/a7-defect-rows.tsv" | sort | uniq -c | sort -rn

  echo
  echo "=== distinct names, .lean sites only ==="
  awk -F'\t' '{n[$4"\t"$5]++} END {for (k in n) printf "%3d  %s\n", n[k], k}' \
    "$scratch/a7-lean-rows.tsv" | sort -rn

  echo
  echo "=== distinct names, prose sites, count >= 2 ==="
  awk -F'\t' '{n[$4"\t"$5]++} END {for (k in n) if (n[k]>=2) printf "%3d  %s\n", n[k], k}' \
    "$scratch/a7-prose-rows.tsv" | sort -rn

  echo
  echo "=== files with the most defect sites ==="
  awk -F'\t' '{sub(/.*\/ScottDomains\//,"",$1); print $1}' \
    "$scratch/a7-defect-rows.tsv" | sort | uniq -c | sort -rn | head -15
} > "$out"

echo "wrote $out"
