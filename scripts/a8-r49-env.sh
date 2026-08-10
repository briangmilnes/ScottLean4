#!/usr/bin/env bash
# a8-r49-env.sh — dump every constant in the elaborated ScottDomains environment
# to a TSV of "module<TAB>name", for agent8's worktree.
#
# This is scripts/a7-dump-env.sh (r0044, agent7) with the worktree and scratch
# paths retargeted; a7's copy hard-codes ScottLean4-agent7 and that session's
# scratchpad, so it cannot run here. The generator (a7-gen-dump.py) and the
# resolver (a7-resolve.py) are reused unchanged — a second lexer or a second
# name universe would be a second thing to trust.
#
# Requires a completed `lake build` (scripts/compile.sh).
#
# Work: O(|environment|) constant emissions, ~350k lines; span: one elaboration.
#
# Usage: scripts/a8-r49-env.sh [outfile]
set -uo pipefail

wt=/home/milnes/projects/ScottLean4-agent8
pkg="$wt/ScottDomains"
scratch=/tmp/claude-1000/-home-milnes-projects-ScottLean4/98e1d10d-3eb9-440a-82f5-e930a0a93589/scratchpad
dump="$scratch/A8Dump.lean"
out="${1:-$scratch/env-names.tsv}"

mkdir -p "$scratch"
rm -f "$out"
# --no-mathlib: this worktree has the 973 Mathlib modules ScottDomains
# transitively imports, not the Mathlib root olean, so `import Mathlib` cannot
# elaborate here. Stated cost: Mathlib names cited from unimported files read as
# unresolved (a7 measured 15 such names tree-wide).
python3 "$wt/scripts/a7-gen-dump.py" "$pkg/ScottDomains" "$dump" "$out" --no-mathlib || exit 1
cd "$pkg" || exit 1
lake env lean "$dump"
rc=$?
if [ ! -s "$out" ]; then
  echo "a8-r49-env: FAILED — $out empty or missing (lean exit $rc)"
  exit 1
fi
echo "a8-r49-env: wrote $out"
wc -l "$out"
