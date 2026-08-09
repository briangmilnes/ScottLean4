#!/usr/bin/env bash
# a7-dump-env.sh — dump every constant in the elaborated ScottDomains
# environment to a TSV of "module<TAB>name".
#
# Why this is a script and not an inline command: it must `cd` into the lake
# package root (lake resolves its config from the working directory) and then run
# `lake env lean` on a file that lives outside the package. Two steps and a `cd`,
# which the project's shell discipline says belongs in scripts/.
#
# The dumped file is the name universe for scripts/a7-resolve.py. Taking it from
# the environment rather than from a source lexer is what makes the class-4
# sweep precise: projections, constructors and Mathlib names are all constants
# here, and all three were r0043's documented false-positive sources.
#
# Output: $SCRATCH/env-names.tsv  (~350k lines; not a project artifact)

set -uo pipefail

pkg=/home/milnes/projects/ScottLean4-agent7/ScottDomains
scratch=/tmp/claude-1000/-home-milnes-projects-ScottLean4/ab3f8bb9-d928-40ef-b45c-b2c8efc2bd0e/scratchpad
dump="$scratch/A7Dump.lean"
out="$scratch/env-names.tsv"

rm -f "$out"
python3 /home/milnes/projects/ScottLean4-agent7/scripts/a7-gen-dump.py \
  "$pkg/ScottDomains" "$dump" "$out" || exit 1
cd "$pkg" || exit 1
lake env lean "$dump"
rc=$?
if [ ! -s "$out" ]; then
  echo "a7-dump-env: FAILED — $out empty or missing (lean exit $rc)"
  exit 1
fi
echo "a7-dump-env: wrote $out"
wc -l "$out"
