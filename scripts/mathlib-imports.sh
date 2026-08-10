#!/usr/bin/env bash
# mathlib-imports.sh — the size and Mathlib-dependency figures in
# ScottDomains/docs/Status.md tables 6 and 7.
#
# WHAT IT MEASURES. Table 6: files, modules, lines. Table 7: how many distinct
# Mathlib modules the package imports, and how those group by top-level theory.
#
# WHY IT EXISTS. Both tables were hand-counted once and would drift silently.
# The import figure in particular is the honest answer to "what does this
# development rest on" — 34 modules out of Mathlib's tens of thousands.
#
# Theorem, def, Prop-def, structure and constant counts are NOT here: they come
# from the elaborated environment, not the source text. Use scripts/counts.sh
# and scripts/a6-env-scan.sh + a6-summarize.py for those.
#
# USAGE: scripts/mathlib-imports.sh
set -u
SRC="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)/ScottDomains/ScottDomains"

echo "files:   $(find "$SRC" -name '*.lean' | wc -l)"
echo "lines:   $(find "$SRC" -name '*.lean' -exec cat {} + | wc -l)"
echo
echo "distinct Mathlib modules imported: $(grep -rhoE '^import Mathlib[A-Za-z0-9_.]*' "$SRC" --include=*.lean | sort -u | wc -l)"
echo
echo "by top-level theory:"
# Dedupe the FULL module name first, then truncate to the theory. Truncating
# before `sort -u` collapses every theory to one row.
grep -rhoE '^import Mathlib[A-Za-z0-9_.]*' "$SRC" --include=*.lean \
  | sort -u | sed 's/^import //' | cut -d. -f1-2 | sort | uniq -c | sort -rn
echo
echo "the modules:"
grep -rhoE '^import Mathlib[A-Za-z0-9_.]*' "$SRC" --include=*.lean | sort -u | sed 's/^import //'
