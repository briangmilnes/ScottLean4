#!/usr/bin/env bash
# pdf-section.sh — extract a page range of a PDF as plain text for reading
# in-context.
#
# Why this exists: `Gunter Scott 1990.pdf` uses Type 3 bitmap fonts whose glyph
# names do not map to Unicode, so `pdftotext` mangles the operator symbols
# (`♮`/`♯`/`♭` come out as `\`/`]`/`[`, and both `→` and `◦→` come out as `!`).
# Reading the raw extraction alone misreports Lemma 28's operator list, which is
# exactly the defect r0034 and r0036 were sent to fix — so a page window plus a
# layout-preserving extraction is the standard first step, and this script does
# it in one allowlisted command (the project forbids chained shell commands).
#
# r0036's agent4 and agent5 each wrote this file with a different interface;
# this version accepts both call shapes rather than breaking either.
#
# Usage:
#   pdf-section.sh <pdf> <first-page> <last-page> [out-file]
#
# <pdf> is either a path (anything containing `/`) or a bare basename, which is
# resolved under ScottDomains/papers/. With no <out-file> the text goes to the
# scratchpad and is printed; with one, it is written there and the line count is
# reported instead.
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

case "$1" in
  */*) pdf="$1" ;;
  *)   pdf="$root/ScottDomains/papers/$1" ;;
esac

if [ "$#" -ge 4 ]; then
  out="$4"
  mkdir -p "$(dirname "$out")"
  pdftotext -layout -f "$2" -l "$3" "$pdf" "$out"
  wc -l "$out"
else
  out="/tmp/claude-1000/-home-milnes-projects-ScottLean4/pdf-section.txt"
  mkdir -p "$(dirname "$out")"
  pdftotext -layout -f "$2" -l "$3" "$pdf" "$out"
  cat "$out"
fi
