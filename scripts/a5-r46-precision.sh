#!/usr/bin/env bash
# a5-r46-precision.sh — r0046 / agent5. Measure the sweep's precision.
#
#   scripts/a5-r46-precision.sh
#
# Why this exists: the round's rule is that "a sweep with unmeasured precision is
# not usable and will not be merged". Precision here is
#
#     (distinct candidate sites) - (hand-classified false positives)
#     -----------------------------------------------------------------
#                       distinct candidate sites
#
# The numerator's subtrahend is `scripts/a5-r46-fp.txt`, which is hand-authored,
# one `file:line` per line, with the reason. Every one of the 230 emitted
# candidates was read; this file lists the ones that are regex noise. Keeping the
# false-positive list as data rather than as a number in a report means the next
# round can re-run the sweep, re-run this, and diff the disagreements.
#
# "Distinct sites" deduplicates: a line matching two pattern classes (e.g.
# `FinitaryProjectionPoset.lean:54` matches both N and I) is one sentence.
#
# Work: two passes over the sweep output; span: one sort.
set -eu
root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
sweep="${1:-$root/ScottDomains/analyses/a5-r46-sweep.txt}"
fp="$root/scripts/a5-r46-fp.txt"

rows=$(wc -l < "$sweep")
sites=$(cut -f2 "$sweep" | LC_ALL=C sort -u | wc -l)
fps=$(grep -c '^ScottDomains' "$fp")

# Every listed false positive must actually appear in the sweep, or the
# measurement is quoting a site the instrument never emitted.
missing=0
while read -r line; do
  case "$line" in \#*|"") continue;; esac
  site="${line%%[[:space:]]*}"
  if ! cut -f2 "$sweep" | grep -qxF "$site"; then
    echo "WARNING: false-positive entry not in sweep: $site"
    missing=$((missing + 1))
  fi
done < "$fp"

tp=$((sites - fps))
echo "candidate rows emitted : $rows"
echo "distinct sites         : $sites   (rows - $((rows - sites)) duplicate class matches)"
echo "hand-classified FPs    : $fps"
echo "true positives         : $tp"
echo "FP entries not in sweep: $missing"
awk -v t="$tp" -v s="$sites" 'BEGIN { printf "sweep precision        : %.1f%%  (%d/%d)\n", 100*t/s, t, s }'
