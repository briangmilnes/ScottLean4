#!/usr/bin/env bash
# pdf-find-page.sh — report which physical PDF page contains a given string.
#
# Why this exists: `pdftotext` over a whole file gives line numbers, not page
# numbers, and the printed folio in `Gunter Scott 1990.pdf` is offset from the
# physical page index. Rendering the right page as an image (the only reliable
# way to read this paper's Type 3 bitmap glyphs) needs the physical index.
# Runs as one allowlisted command, per the project's no-chaining rule.
#
# Usage: pdf-find-page.sh <pdf> <pattern>
set -euo pipefail
pdf="$1"; pat="$2"
n=$(pdfinfo "$pdf" | awk '/^Pages:/ {print $2}')
for ((i=1; i<=n; i++)); do
  if pdftotext -f "$i" -l "$i" -layout "$pdf" - | grep -q -- "$pat"; then
    echo "page $i"
  fi
done
