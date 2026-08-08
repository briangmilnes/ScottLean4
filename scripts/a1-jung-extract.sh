#!/usr/bin/env bash
# a1-jung-extract.sh — extract a page range of Jung 1989 as plain text.
#
# Why it exists: r0042 stream 1 must read Jung's Propositions 1.22, 1.34 and
# Corollary 1.36 from the source rather than from the round plan. pdftotext
# needs a first/last page pair and an output path; that is more than one
# command, so it lives here per the project's shell discipline.
#
# Usage: a1-jung-extract.sh <firstPage> <lastPage>
# Writes /tmp/claude-1000/.../scratchpad is not allowlisted, so it writes into
# the worktree's own scratch file ScottDomains/logs/a1-jung-<first>-<last>.txt
set -euo pipefail
root=/home/milnes/projects/ScottLean4-agent1
pdf="$root/ScottDomains/papers/Jung 1989 Cartesian Closed Categories of Domains.pdf"
first="$1"
last="$2"
out="$root/ScottDomains/logs/a1-jung-$first-$last.txt"
pdftotext -f "$first" -l "$last" -layout "$pdf" "$out"
echo "wrote $out"
