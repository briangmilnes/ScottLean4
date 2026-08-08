#!/usr/bin/env bash
# a2-build-figures.sh — compile every .tex in a directory with a1-tikz2pdf.sh.
#
# Why this exists: r0039 agent2 produced nine standalone TikZ sources in
# ScottDomains/GunterScott90Images/. Compiling them one at a time costs nine
# Bash calls and re-checks nothing; this loops over the directory so one call
# rebuilds the whole set and reports which sources failed. Loops, so it lives
# in scripts/ per the project's shell rule 3.
#
# Usage: a2-build-figures.sh <dir>
set -uo pipefail
dir="${1:?usage: a2-build-figures.sh <dir>}"
here="$(dirname "$(readlink -f "$0")")"
fail=0
for f in "$dir"/*.tex; do
  if "$here/a1-tikz2pdf.sh" "$f"; then :; else echo "FAILED: $f"; fail=$((fail+1)); fi
done
echo "--- failures: $fail ---"
exit 0
