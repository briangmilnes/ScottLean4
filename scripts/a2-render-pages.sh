#!/usr/bin/env bash
# a2-render-pages.sh — render a list of whole PDF pages to PNG at one dpi.
#
# Why this exists: r0039 asks agent2 to classify 27 candidate regions on 11
# pages of `Gunter Scott 1990.pdf` as diagram / displayed equation / other.
# Cropping each region separately costs 27 pdftoppm invocations, and one
# whole-page render at 150 dpi already separates a picture from an equation.
# Only the confirmed diagrams then need a 300 dpi crop for transcription.
# Loops, so it lives in scripts/ rather than inline (project shell rule 3).
#
# Usage: a2-render-pages.sh <pdf> <dpi> <out-dir> <page> [<page> ...]
set -euo pipefail
pdf="$1"; dpi="$2"; out="$3"; shift 3
mkdir -p "$out"
for p in "$@"; do
  pdftoppm -png -r "$dpi" -f "$p" -l "$p" "$pdf" "$out/page"
done
ls -la "$out"
