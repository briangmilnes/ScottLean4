# Proofs & Text Inventory

Master index of everything downloaded/generated in this project. Detailed docs
are linked per section.

## Directory map

| Directory | Files | Size | What it is |
|-----------|------:|-----:|------------|
| `DanaScottPapers/` | 83 | 81M | 41 Dana Scott paper PDFs + 41 text extractions + `EXTRACTION_REPORT.md` |
| `ScottLean/Scott/` | 38 | 432K | **38 Lean 4 formalizations** of the extractible Scott papers (whole-project `lake build` passes) |
| `ScottClasses/` | 38 | 3.1M | 37 Dana Scott CMU Mathematica notebooks (Projective Geometry 15-491, Algebra 15-499) + `README.md` |
| `Beeson/` | 70 | 13M | Michael Beeson's **Lean 3** development (51 `.lean`: intuitionistic NF set theory `inf1`–`inf32`, Church numerals, Dedekind, intuitionistic logic) — to be ported to Lean 4 |
| `HarperBook/` | 4 | 1.3M | Harper *PFPL* abbreviated ed. (`PFPL.pdf`/`PFPL.txt` local-only), `OUTLINE.md`, Ch.4 pilot Lean |
| `papers/` | 1 | 1.7M | Coquand–Huet, *Calculus of Constructions* (HAL OA) |
| `tutorials/` | 2 | 308K | de Moura–Ullrich Lean 4 CADE 2021 (CC-BY) PDF + `.lean` code extraction |
| `FromGregoireRosu/` | 2 | 296K | Mesnard et al. LPTP (arXiv, CC-BY) PDF + `sqrt2.pl` |
| `cheatsheets/` | 1 | 176K | Lean community tactics cheatsheet |
| `MathTexts/ProjectiveGeometry/` | 1 | 8K | Top-10 projective-geometry texts survey (`README.md`) |
| `MathTexts/DimensionalizingPLandPOP/` | 0 | 0 | empty — source had no textbooks (blocked, awaiting clarification) |
| `docs/` | 3 | 44K | this file + the two detail docs below |
| `plans/`, `reports/` | — | — | placeholders |

## Detail docs

- [`docs/DanaScottPapers.md`](DanaScottPapers.md) — full 57-entry Scott bibliography + OA-PDF manifest.
- [`docs/PapersToLeanStatus.md`](PapersToLeanStatus.md) — per-module leanification table (lines, `sorry` proof-holes, status).
- [`ScottClasses/README.md`](../ScottClasses/README.md) — notebook provenance (Wayback URLs + timestamps).
- [`HarperBook/OUTLINE.md`](../HarperBook/OUTLINE.md) — PFPL 19-part / 49-chapter structure map.

## Headline metrics

| Metric | Value |
|--------|------:|
| Dana Scott papers downloaded | 41 (38 text-extractible, 3 scanned) |
| Scott papers formalized in Lean 4 | 38 (whole-project `lake build` PASS) |
| Total `sorry` proof-holes | 100 |
| Scott Mathematica notebooks | 37 |
| Other papers (Coquand, CADE, LPTP, PFPL) | 4 |
| Beeson Lean 3 files (to port) | 51 |

## Not text-extractible (need OCR before formalization)

- Scott–Strachey 1971, *Toward a Mathematical Semantics for Computer Languages*
- Scott 1973, *Models for Various Type-Free Calculi*
- Scott 1980, *The Presheaf Model for Set Theory*
