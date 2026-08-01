# Proofs & Text Inventory

Master index of everything downloaded/generated in this project. Detailed docs
are linked per section.

## Directory map

| Directory | Files | Size | What it is |
|-----------|------:|-----:|------------|
| `DanaScottPapers/` | 83 | 81M | 41 Dana Scott paper PDFs + 41 text extractions + `EXTRACTION_REPORT.md` |
| `ScottLean/Scott/` | 38 | 432K | **38 Lean 4 formalizations** of the extractible Scott papers (whole-project `lake build` passes) |
| `ScottClasses/` | 38 | 3.1M | 37 Dana Scott CMU Mathematica notebooks (Projective Geometry 15-491, Algebra 15-499) + `README.md` |
| `Beeson/` | 70 | 13M | Michael Beeson's **Lean 3** corpus (51 `.lean`: intuitionistic NF set theory `inf1`–`inf32`, Church numerals, Dedekind, logic) + `FailedProofs.md` (tagged dead paths) + `lean4/` Mathlib-enabled Lean 4 pilot |
| `HarperBook/` | 4 | 1.3M | Harper *PFPL* abbreviated ed. (`PFPL.pdf`/`PFPL.txt` local-only), `OUTLINE.md`, Ch.4 pilot Lean |
| `papers/` | 1 | 1.7M | Coquand–Huet, *Calculus of Constructions* (HAL OA) |
| `tutorials/` | 2 | 308K | de Moura–Ullrich Lean 4 CADE 2021 (CC-BY) PDF + `.lean` code extraction |
| `FromGregoireRosu/` | 2 | 296K | Mesnard et al. LPTP (arXiv, CC-BY) PDF + `sqrt2.pl` |
| `cheatsheets/` | 1 | 176K | Lean community tactics cheatsheet |
| `MathTexts/ProjectiveGeometry/` | 11 | 80M | 5 public-domain texts (Veblen & Young Vols 1–2, Cremona, Filon, Whitehead) as PDF + OCR text, plus `README.md` survey |
| `MathTexts/DifferentialGeometry/` | 12 | 32M | 4 freely-posted DG lecture notes (Robbin–Salamon, Sharipov, Shifrin, DiffGeomNotes) as PDF + text + 4 notebooks; do Carmo scan kept local (commercial, image-only) |
| `docs/` | 4 | — | this file + the detail docs below |
| `plans/`, `reports/` | — | — | placeholders |

## Repository structure

```
ScottLean4/
├── CLAUDE.md  README.md  lakefile.toml  lean-toolchain  lake-manifest.json
├── ScottLean.lean             root module — imports Basic + all 38 Scott modules
├── ScottLean/                 ◀ the Lean 4 library
│   ├── Basic.lean
│   └── Scott/                 38 paper formalizations (lake build passes, 100 sorry)
├── DanaScottPapers/           41 PDFs + 41 .txt + EXTRACTION_REPORT.md
├── docs/                      DanaScottPapers.md, PapersToLeanStatus.md,
│                              ProofsAndTextInventory.md, ForDana.md
├── ScottClasses/              Dana's CMU Mathematica notebooks (37) + README
│   ├── 15-491/                Computational Projective Geometry (StartUp 3, Lectures 18, Homework 13)
│   └── 15-499/                Computational Algebra (3)
├── Beeson/                    Beeson's Lean 3 corpus (51) + FailedProofs.md
│   └── lean4/                 Mathlib-enabled Lean 3→4 pilot (IntuitionisticLogic, MathlibSmoke)
├── MathTexts/ProjectiveGeometry/   5 PD PDFs + 5 .txt + README survey
├── HarperBook/                OUTLINE.md + pilot Lean  (PFPL.pdf/.txt local-only)
├── papers/                    Coquand–Huet CoC PDF
├── tutorials/                 CADE 2021 PDF + .lean extraction
├── FromGregoireRosu/          LPTP arXiv PDF + sqrt2.pl
├── cheatsheets/               lean-tactics.pdf
├── plans/  reports/           .gitkeep placeholders
├── ComputAItionalThinking/    imported ruleset repo   ⟨local, gitignored⟩
└── .claude/settings.local.json                        ⟨local, gitignored⟩
```

**Local-only (gitignored):** `ComputAItionalThinking/`, `.claude/settings.local.json`,
`HarperBook/PFPL.pdf`+`.txt` (CUP copyright), every `.lake/` (incl. the 7 GB Mathlib
checkout), and `*.olean`.

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
| Projective-geometry texts (public domain) | 5 (PDF + OCR text) |

## Not text-extractible (need OCR before formalization)

- Scott–Strachey 1971, *Toward a Mathematical Semantics for Computer Languages*
- Scott 1973, *Models for Various Type-Free Calculi*
- Scott 1980, *The Presheaf Model for Set Theory*
