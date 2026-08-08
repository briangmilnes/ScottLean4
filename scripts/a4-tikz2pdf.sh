#!/usr/bin/env bash
# a1-tikz2pdf.sh — compile one standalone TikZ .tex to a PDF beside it.
#
# Why this exists: scripts/tex2pdf.sh hardcodes `xelatex`, which is not
# installed on this machine — `which xelatex` returns nothing while
# /usr/bin/pdflatex, /usr/bin/lualatex and /usr/bin/latexmk are present. The
# r0039 figures are `standalone` + `tikz` documents with no fontspec and no
# Unicode outside math mode, so `lualatex` compiles them unchanged and also
# accepts the Unicode this project's sources tend to carry.
#
# Builds in a temp dir so no .aux/.log clutter lands in the repo, then copies
# the PDF next to the source (or into the given outdir). One run, one command,
# per the project's no-chaining rule.
#
# Usage: a1-tikz2pdf.sh <file.tex> [outdir]
set -euo pipefail
SRC="${1:?usage: a1-tikz2pdf.sh <file.tex> [outdir]}"
OUT="${2:-$(dirname "$SRC")}"
[ -f "$SRC" ] || { echo "no such file: $SRC" >&2; exit 1; }
base="$(basename "$SRC" .tex)"
work="$(mktemp -d)"
cp "$SRC" "$work/$base.tex"
if ! ( cd "$work" && lualatex -interaction=nonstopmode "$base.tex" >build.log 2>&1 ); then
  echo "lualatex failed; tail of log:" >&2
  tail -30 "$work/build.log" >&2
  exit 1
fi
mkdir -p "$OUT"
cp "$work/$base.pdf" "$OUT/$base.pdf"
rm -rf "$work"
echo "wrote $OUT/$base.pdf"
