# scripts/ — Lean → LaTeX → PDF, and plotting

Small, reproducible tools for turning Lean formalizations and figures into PDFs
Dana can read. All output lands in [`../generated-latex/`](../generated-latex/).

**Requirements** (already installed on `milnes`): MacTeX at `/Library/TeX/texbin`
(provides `xelatex`, `pdflatex`, `pgfplots`, `bussproofs`) and, for `lean2tex.sh`,
Lean/`lake` on `PATH`. The scripts prepend these paths themselves.

## Tools

| Script | Does | Engine |
|--------|------|--------|
| `lean2tex.sh <File.lean> [outdir]` | Typeset a Lean source file as a PDF (Unicode via Menlo font) | XeLaTeX |
| `tex2pdf.sh <File.tex> [outdir]` | Compile any `.tex` to a PDF (handles pgfplots + Unicode) | XeLaTeX |

Both default `outdir` to `../generated-latex/` and build in a temp dir (no
`.aux`/`.log` litter). Each prints the output PDF path.

## Templates to copy from

| File | Shows |
|------|-------|
| `plot-demo.tex` | 2D pgfplots curves |
| `plots.tex` | 2D functions **and** 3D `surf` surfaces (a plot gallery) |
| `mixed-example.tex` | interleaving **prose + math + Lean code** in one document |
| `Lean4ProofTrees.tex` | natural-deduction **proof trees** paired with Lean terms (`bussproofs`) |

## Examples

```bash
# a Lean formalization -> PDF
scripts/lean2tex.sh ScottLean/Scott/DataTypesAsLattices.lean

# any LaTeX document (plots, proof trees, mixed prose) -> PDF
scripts/tex2pdf.sh scripts/plots.tex
scripts/tex2pdf.sh scripts/Lean4ProofTrees.tex
scripts/tex2pdf.sh scripts/mixed-example.tex
```

## Notes for the next AI instance

- Lean source uses Unicode (ℕ ℝ ∀ → ⊑ λ …). Compile anything containing it with
  **XeLaTeX** + a Unicode monospace font (`\setmonofont{Menlo}`), not pdfLaTeX.
- Plotting is **pgfplots** (native LaTeX); no matplotlib/Wolfram needed for figures.
- `generated-latex/` is the browsable output area for Dana; view PDFs in Chrome
  (native PDF rendering) or Preview.
