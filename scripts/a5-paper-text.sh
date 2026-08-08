#!/bin/zsh
# a5-paper-text.sh — extract the text layer of a paper PDF into the scratchpad so
# the Theorem 18 statement audit (r0042, stream 5) can quote Gunter & Scott §6.2
# verbatim rather than paraphrase it. Read-only with respect to the repository:
# it writes only under $out.
#
# usage: a5-paper-text.sh <pdf-basename-substring> [out-file]
set -e
papers="${0:A:h}/../ScottDomains/papers"
pdf=$(ls "$papers"/*"$1"*.pdf | head -1)
out="${2:-/tmp/claude-1000/-home-milnes-projects-ScottLean4/a5-paper.txt}"
mkdir -p "$(dirname "$out")"
pdftotext -layout "$pdf" "$out"
echo "extracted: $pdf"
wc -l "$out"
