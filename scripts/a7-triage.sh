#!/usr/bin/env bash
# a7-triage.sh — summarize a7-sweep.sh's unresolved citations for hand review.
#
# The sweep's raw output is one row per SITE; the same wrong name cited in six
# files is six rows. Classification is per NAME, so this collapses to distinct
# names with an occurrence count, a kind breakdown and one example site, sorted
# by count. This is the file the stoplist is built from — every stoplist entry
# has to be justified by a row here.
#
# Output: $SCRATCH/a7-triage.txt

set -uo pipefail
scratch=/tmp/claude-1000/-home-milnes-projects-ScottLean4/ab3f8bb9-d928-40ef-b45c-b2c8efc2bd0e/scratchpad
unres="$scratch/a7-unresolved.tsv"
out="$scratch/a7-triage.txt"

awk -F'\t' '
{
  n[$4]++
  if (!(($4) in ex)) { ex[$4] = $1 ":" $2 " (" $3 ")" }
  if ($3 == "lean-doc")     d[$4]++
  if ($3 == "lean-comment") c[$4]++
  if ($3 == "prose")        p[$4]++
}
END {
  for (k in n)
    printf "%5d  doc=%-4d cmt=%-4d prose=%-4d  %-45s  %s\n", n[k], d[k]+0, c[k]+0, p[k]+0, k, ex[k]
}' "$unres" | sort -rn > "$out"

echo "a7-triage: $(wc -l < "$out") distinct unresolved names -> $out"
