#!/bin/zsh
# md2pdf.sh — convert a Markdown file to a PDF, for viewers that don't render
# `.md` (e.g. Safari). One command, so a reader (Dana) just opens the PDF.
#
# Uses pandoc + XeLaTeX with the STIX Two fonts, which cover the domain-theory /
# Lean Unicode (⊑ ⊔ ⨆ ⊥ ≪ β λ Γ ⊗ ∞ ω …) so nothing renders as tofu.
#
# Usage:
#   scripts/md2pdf.sh <file.md> [outdir]
#     outdir defaults to the .md file's own directory.
set -e
export PATH="/Library/TeX/texbin:/opt/homebrew/bin:$PATH"

SRC="${1:?usage: md2pdf.sh <file.md> [outdir]}"
[ -f "$SRC" ] || { echo "md2pdf: no such file: $SRC" >&2; exit 1; }

base="$(basename "$SRC" .md)"
dir="$(cd "$(dirname "$SRC")" && pwd)"
OUT="${2:-$dir}"; mkdir -p "$OUT"

pandoc "$SRC" -o "$OUT/$base.pdf" \
  --pdf-engine=lualatex \
  -H "${0:A:h}/md-pdf-header.tex" \
  -V geometry:margin=0.75in \
  -V fontsize=10pt \
  -V colorlinks=true -V linkcolor=blue -V urlcolor=blue

echo "$OUT/$base.pdf"
