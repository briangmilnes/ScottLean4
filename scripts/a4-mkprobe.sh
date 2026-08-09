#!/bin/zsh
# a4-mkprobe.sh — emit a standalone Lean probe that imports every module of the
# ScottDomains package plus Batteries' linter frontend.
#
# Usage: scripts/a4-mkprobe.sh <out.lean> [trailing-lean-command ...]
#
# Why it exists (r0044, Class 2): `#lint … in ScottDomains` filters the linter's
# declaration set by module-name prefix, but only over modules actually *loaded*
# into the environment. ScottDomains.lean (the root) imports only Mathlib
# foundations, so a probe importing it sees ~0 package declarations. This script
# derives the import list from the file tree, so the probe's coverage is the
# package's coverage by construction rather than by a hand-maintained list.
#
# Work: O(#modules) path-to-module-name rewrites; span: one `find`.
set -e
out="$1"
shift
root="${0:A:h}/.."
pkg="$root/ScottDomains/ScottDomains"
{
  print -- "import Batteries.Tactic.Lint"
  find "$pkg" -name '*.lean' | sort | while read -r f; do
    rel="${f#$pkg/}"
    rel="${rel%.lean}"
    print -- "import ScottDomains.${rel//\//.}"
  done
  print -- ""
  for line in "$@"; do
    print -- "$line"
  done
} > "$out"
print -- "wrote $out ($(grep -c '^import' "$out") imports)"
