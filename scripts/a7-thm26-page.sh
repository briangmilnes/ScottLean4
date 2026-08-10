#!/usr/bin/env bash
# r0049, agent7 — extract the printed text of Gunter & Scott §7.2 around
# Theorem 26 and the signature example `(2,0,0,0,0,0)`.
#
# Why this exists: the round's evidence rule is "check the paper before
# convicting it". Theorem 26's `hs : ∀ i, 0 < s i` is either a defect of ours or
# a repair of a printed defect, and the question turns on two printed sentences —
# the statement of Theorem 26 (printed p. 39) and the paragraph one page earlier
# admitting arity 0 in a signature (printed p. 38). PDF page n is printed page
# n − 1 throughout this paper, so those are PDF pages 40 and 39.
#
# Output: plain text of the two pages, one command, no chaining.
set -euo pipefail
PDF="/home/milnes/projects/ScottLean4-agent7/ScottDomains/papers/Gunter Scott 1990.pdf"
OUT="${1:-/tmp/claude-1000/-home-milnes-projects-ScottLean4/98e1d10d-3eb9-440a-82f5-e930a0a93589/scratchpad/thm26-pages.txt}"
mkdir -p "$(dirname "$OUT")"
pdftotext -layout -f 39 -l 40 "$PDF" "$OUT"
cat "$OUT"
