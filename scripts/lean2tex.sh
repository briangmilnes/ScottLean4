#!/bin/zsh
# lean2tex.sh — render a Lean 4 source file to a PDF via XeLaTeX.
#
# Lean source uses Unicode (ℕ ℝ ∀ → ⊑ λ …); XeLaTeX + a Unicode monospace font
# (macOS Menlo) typesets it faithfully. fvextra's \VerbatimInput reads the file
# verbatim (no escaping) with line-wrapping + line numbers.
#
# Usage:  scripts/lean2tex.sh <path/to/File.lean> [outdir]
#         outdir defaults to generated-latex/ (a place for Dana to browse output).
set -e
export PATH="/Library/TeX/texbin:/opt/homebrew/bin:$PATH"

SRC="${1:?usage: lean2tex.sh <file.lean> [outdir]}"
OUT="${2:-$HOME/projects/ScottLean4/generated-latex}"
[ -f "$SRC" ] || { echo "no such file: $SRC" >&2; exit 1; }
base="$(basename "$SRC" .lean)"

work="$(mktemp -d)"
cp "$SRC" "$work/source.lean"
cat > "$work/doc.tex" <<'TEX'
\documentclass[11pt]{article}
\usepackage[margin=1in]{geometry}
\usepackage{fontspec}
\setmonofont{Menlo}[Scale=0.80]
\usepackage{fvextra}
\usepackage{xcolor}
\title{\texttt{@TITLE@}\\[2pt]\large Lean~4 formalization}
\author{ScottLean4 \textperiodcentered\ Dana Scott formalization project}
\date{}
\begin{document}
\maketitle
\VerbatimInput[breaklines=true,breakanywhere=true,fontsize=\footnotesize,%
  numbers=left,numbersep=6pt,frame=leftline,framerule=0.4pt]{source.lean}
\end{document}
TEX
sed -i '' "s/@TITLE@/$base/" "$work/doc.tex"

( cd "$work" && xelatex -interaction=nonstopmode doc.tex >build.log 2>&1 ) \
  || { echo "XeLaTeX failed; tail of log:" >&2; tail -25 "$work/build.log" >&2; exit 1; }

mkdir -p "$OUT"
cp "$work/doc.pdf" "$OUT/$base.pdf"
rm -rf "$work"
echo "$OUT/$base.pdf"
