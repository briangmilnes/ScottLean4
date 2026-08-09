#!/usr/bin/env bash
# a7-audit.sh — split a7-sweep.sh's reported rows into the views the precision
# audit needs.
#
# Precision is claimed per SITE, and the two populations have very different
# base rates, so they are audited separately:
#   * .lean sites (docstrings and comments) — documentation of live code, the
#     severe class. Small enough to check exhaustively, and it is.
#   * prose sites (docs/, analyses/, plans/, reports/) — audited on a sample.
#
# Output: $SCRATCH/a7-lean-rows.tsv, $SCRATCH/a7-prose-rows.tsv,
#         $SCRATCH/a7-sample.tsv (every 7th prose row, a fixed stride so the
#         sample is reproducible rather than randomly reseeded per run)

set -uo pipefail
scratch=/tmp/claude-1000/-home-milnes-projects-ScottLean4/ab3f8bb9-d928-40ef-b45c-b2c8efc2bd0e/scratchpad
unres="$scratch/a7-unresolved.tsv"

# absence-claim rows are NOT defects — the name is cited to say it is absent,
# and non-resolution is the correct outcome. They are split off so precision is
# measured over the rows the instrument actually asserts are defects, and kept
# in their own file so the absence classifier can itself be audited.
grep -P '\tabsence-claim\t' "$unres" > "$scratch/a7-absence-rows.tsv"
grep -Pv '\tabsence-claim\t' "$unres" > "$scratch/a7-defect-rows.tsv"

grep -P '\tlean-(doc|comment)\t' "$scratch/a7-defect-rows.tsv" > "$scratch/a7-lean-rows.tsv"
grep -P '\tprose\t' "$scratch/a7-defect-rows.tsv" > "$scratch/a7-prose-rows.tsv"
awk 'NR % 7 == 1' "$scratch/a7-prose-rows.tsv" > "$scratch/a7-sample.tsv"
awk 'NR % 6 == 1' "$scratch/a7-absence-rows.tsv" > "$scratch/a7-absence-sample.tsv"

echo "defect sites  : $(wc -l < "$scratch/a7-defect-rows.tsv")"
echo "absence sites : $(wc -l < "$scratch/a7-absence-rows.tsv")"
echo "lean sites : $(wc -l < "$scratch/a7-lean-rows.tsv")"
echo "prose sites: $(wc -l < "$scratch/a7-prose-rows.tsv")"
echo "sample     : $(wc -l < "$scratch/a7-sample.tsv")"
echo
echo "by category:"
cut -f5 "$unres" | sort | uniq -c | sort -rn
echo
echo "lean sites by category:"
cut -f5 "$scratch/a7-lean-rows.tsv" | sort | uniq -c | sort -rn
