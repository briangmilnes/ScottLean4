#!/usr/bin/env bash
# a8-categorical-claims.sh — r0044 Class 4 (reading half), agent8.
#
# Collects every line of documentation prose in the package that makes a
# CATEGORICAL claim — "not in Mathlib", "nothing proves", "there is no",
# "never", "the only", "does not exist", "no declaration", "not proved" —
# so each can be checked against the elaborated declarations.  These are the
# claims that age badly: the artifact stays put while the tree grows past it.
#
# Scope: every .lean file under ScottDomains/ScottDomains, plus docs/,
# analyses/, plans/ and reports/ markdown.  Read-only; writes one report to
# the path given as $1 (default: /tmp/claude-*/a8-categorical-claims.txt).
#
# Usage: scripts/a8-categorical-claims.sh <outfile>
set -u
ROOT=/home/milnes/projects/ScottLean4-agent8/ScottDomains
OUT=${1:-/dev/stdout}

PAT='not in Mathlib|not part of Mathlib|nothing proves|nothing in the|there is no |there are no |does not exist|do not exist|no declaration|never (stated|proved|instantiated|constructed|declared|used|bundled|fires)|the only |is not stated|is not proved|not yet (stated|proved|declared)|we do not|is absent|has no |have no |lacks |cannot be (stated|proved|expressed|written)|is impossible|no such |unproved|unstated'

{
  echo "=== .lean sources ==="
  grep -rnEi "$PAT" "$ROOT/ScottDomains" --include='*.lean'
  echo
  echo "=== ScottDomains.lean ==="
  grep -nEi "$PAT" "$ROOT/ScottDomains.lean"
  echo
  echo "=== docs/ ==="
  grep -rnEi "$PAT" "$ROOT/docs" --include='*.md'
} > "$OUT" 2>&1
