#!/usr/bin/env bash
# a1-build-figs.sh — recompile every standalone TikZ figure in
# ScottDomains/GunterScott90Images/ to a PDF beside its source.
#
# Why this exists: r0039's style contract is shared across three agents, so
# it changed twice after the first figures were written (the "solid" vertex
# size, then agent2's obj/arrow/darrow keys). Each change means recompiling
# the whole set, and one command per Bash call is the project rule, so the
# loop belongs in a script rather than in six separate calls.
#
# Delegates each file to a1-tikz2pdf.sh (lualatex; scripts/tex2pdf.sh's
# xelatex is not installed here). Exits non-zero if any figure fails, after
# attempting all of them, so one broken figure does not hide the rest.
#
# Usage: a1-build-figs.sh [dir]
set -uo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
dir="${1:-$here/../ScottDomains/GunterScott90Images}"
fail=0
for tex in "$dir"/*.tex; do
  [ -e "$tex" ] || { echo "no .tex files in $dir" >&2; exit 1; }
  if ! "$here/a1-tikz2pdf.sh" "$tex"; then
    echo "FAILED: $tex" >&2
    fail=1
  fi
done
exit "$fail"
