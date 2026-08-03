#!/bin/zsh
# tex2pdf.sh — compile a LaTeX file to a PDF in generated-latex/.
# Uses XeLaTeX so it handles BOTH pgfplots and Unicode (Lean symbols, fontspec).
# Builds in a temp dir so no .aux/.log clutter is left behind.
# Runs twice so pgfplots/labels/refs settle.
#
# Usage:  scripts/tex2pdf.sh <file.tex> [outdir]
set -e
export PATH="/Library/TeX/texbin:/opt/homebrew/bin:$PATH"
SRC="${1:?usage: tex2pdf.sh <file.tex> [outdir]}"
OUT="${2:-$HOME/projects/ScottLean4/generated-latex}"
[ -f "$SRC" ] || { echo "no such file: $SRC" >&2; exit 1; }
base="$(basename "$SRC" .tex)"
work="$(mktemp -d)"
cp "$SRC" "$work/$base.tex"
( cd "$work" && xelatex -interaction=nonstopmode "$base.tex" >build.log 2>&1 \
             && xelatex -interaction=nonstopmode "$base.tex" >>build.log 2>&1 ) \
  || { echo "xelatex failed; tail of log:" >&2; tail -25 "$work/build.log" >&2; exit 1; }
mkdir -p "$OUT"; cp "$work/$base.pdf" "$OUT/$base.pdf"; rm -rf "$work"
echo "$OUT/$base.pdf"
