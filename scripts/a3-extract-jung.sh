#!/usr/bin/env bash
# a3-extract-jung.sh — extract a PDF page range from Jung 1989 to a text file in
# the r0042 scratchpad, so agent3 can read Jung's proof of Theorem 1.37 (printed
# page 50) directly rather than through a second-hand paraphrase. Exists because
# `pdftotext -f N -l M file out` is a single command but the output path must be
# computed, and repeated invocations with different ranges are needed to locate
# the printed-page-to-PDF-page offset.
#
# usage: a3-extract-jung.sh <first-pdf-page> <last-pdf-page>
set -euo pipefail
PAPER="/home/milnes/projects/ScottLean4-agent3/ScottDomains/papers/Jung 1989 Cartesian Closed Categories of Domains.pdf"
OUT="/tmp/claude-1000/-home-milnes-projects-ScottLean4/ab3f8bb9-d928-40ef-b45c-b2c8efc2bd0e/scratchpad/jung-p$1-$2.txt"
mkdir -p "$(dirname "$OUT")"
pdftotext -f "$1" -l "$2" -layout "$PAPER" "$OUT"
echo "wrote $OUT"
wc -l "$OUT"
