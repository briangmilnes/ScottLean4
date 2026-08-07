#!/usr/bin/env bash
# extract-thm14-pages.sh — dump the raw text of the Gunter & Scott 1990 pages
# carrying §6's definition of *bifinite* and the statement of Theorem 14
# (PDF pages 30 and 31, printed pages 29 and 30) into the scratchpad so the
# agent can read the primary source rather than a paraphrase.
#
# Written for r0036 stream 1 (Theorem 14). Read-only with respect to the repo:
# the only output is a scratch file under $OUT.
set -euo pipefail

PDF="/home/milnes/projects/ScottLean4-agent1/ScottDomains/papers/Gunter Scott 1990.pdf"
OUT="${1:-/tmp/claude-1000/-home-milnes-projects-ScottLean4/ab3f8bb9-d928-40ef-b45c-b2c8efc2bd0e/scratchpad/gs1990-p30-31.txt}"

mkdir -p "$(dirname "$OUT")"
pdftotext -layout -f 30 -l 31 "$PDF" "$OUT"
wc -l "$OUT"
