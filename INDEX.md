# ScottLean4 — File Index

The hub for the working files. Jump to any of these by ⌘-click (VS Code),
`C-x C-f` on the path via `ffap` (Emacs), or `M-.` on an `import` (lean4-mode).
See `CLAUDE.md` → "Repository workflow and file index."

## Playground — Lean 4 (Mathlib-enabled) demos and developments

- [Playground/Playground.lean](Playground/Playground.lean) — root aggregator (imports the library modules)
- [Playground/Playground/LambdaSmallStep.lean](Playground/Playground/LambdaSmallStep.lean) — untyped λ-calculus, de Bruijn, **full-β** small-step relation (0 `sorry`)
- [Playground/Playground/LambdaTheorems.lean](Playground/Playground/LambdaTheorems.lean) — metatheory: congruence, normal forms, non-termination; Church–Rosser is the one `sorry`
- [Playground/Playground/LambdaNamed.lean](Playground/Playground/LambdaNamed.lean) — named-variable λ-calculus with α as an equivalence relation
- [Playground/Playground/CartesianClosed.lean](Playground/Playground/CartesianClosed.lean) — a `Category` class and a `CartesianClosed` class specializing it (0 `sorry`)
- [Playground/Playground/HomogeneousFactoring.lean](Playground/Playground/HomogeneousFactoring.lean) — `ring`-certified factorizations of homogeneous polynomials
- [Playground/SageFactor.lean](Playground/SageFactor.lean) — `#eval` calls Sage to factor ℚ[x,y,z] forms; `ring` certifies (standalone scratch)
- [Playground/SageFactorProved.lean](Playground/SageFactorProved.lean) — couples Sage's factoring to a `ring`-checked theorem
- [Playground/ComputabilityDemo.lean](Playground/ComputabilityDemo.lean) — ℚ computable vs ℝ noncomputable, shown via `#eval`

## ScottDomains — Dana Scott's domain theory (Lean 4, Mathlib-enabled)

Separate project from Playground; the domain-theory development lives here.

- [ScottDomains/ScottDomains.lean](ScottDomains/ScottDomains.lean) — root module: commented imports of ωCPOs, CPOs, Scott continuity, the Scott topology, and fixed points
- [ScottDomains/ScottDomains/ExistingTheories.lean](ScottDomains/ScottDomains/ExistingTheories.lean) — clickable `#check` catalog of the Mathlib domain-theory definitions we build on (jump with `M-.` / F12 / ⌘-click)
- [ScottDomains/lakefile.toml](ScottDomains/lakefile.toml) — project config (pinned Mathlib v4.32.2)
- [ScottDomains/README.md](ScottDomains/README.md) — what the project develops, and the source paper
- [ScottDomains/papers/Gunter Scott 1990.pdf](ScottDomains/papers/Gunter%20Scott%201990.pdf) — **Gunter & Scott, "Semantic Domains" (HTCS Vol. B, 1990)** — the source paper (copy from D. Scott)
- [ScottDomains/docs/PaperInventory.md](ScottDomains/docs/PaperInventory.md) — inventory of the paper's definitions & theorems (the work list)

## Notes (LaTeX source + compiled PDF)

- Category theory in Mathlib — [.tex](notes/CategoryTheoryInMathlib.tex) · [.pdf](notes/CategoryTheoryInMathlib.pdf)
- Scott domains in Lean/Mathlib — [.tex](notes/ScottDomainsInLean.tex) · [.pdf](notes/ScottDomainsInLean.pdf)
- Scott–Strachey criticisms — [.tex](notes/ScottStracheyCriticisms.tex) · [.pdf](notes/ScottStracheyCriticisms.pdf)
- Scott–Strachey criticisms — Gemini Deep Research report, re-typeset from a share link (prints empty in-browser) — [.tex](notes/ScottStracheyGeminiReport.tex) · [.pdf](notes/ScottStracheyGeminiReport.pdf)
- Dana Scott — biography — [.tex](notes/DanaScottBio.tex) · [.pdf](notes/DanaScottBio.pdf)
- Homogeneous factorization — [.tex](notes/HomogeneousFactorization.tex) · [.pdf](notes/HomogeneousFactorization.pdf)

## Polynomials

- Factoring: algorithms, representations, Mathlib — [.tex](polynomials/PolynomialFactoring.tex) · [.pdf](polynomials/PolynomialFactoring.pdf)
- Gemini's note — multivariate factorization over ℚ — [.tex](polynomials/Multivariate_Factorization_Notes.tex) · [.pdf](polynomials/Multivariate_Factorization_Notes.pdf)
- Kaltofen survey, *Polynomial Factorization 1987–1991* — [.pdf](polynomials/PolynomialFactorization.pdf)

## Docs

- [docs/Curriculum.md](docs/Curriculum.md)
- [docs/DanaScottPapers.md](docs/DanaScottPapers.md)
- [docs/ForDana.md](docs/ForDana.md)
- [docs/PapersToLeanStatus.md](docs/PapersToLeanStatus.md)
- [docs/ProofsAndTextInventory.md](docs/ProofsAndTextInventory.md)
- [docs/SoftwareInventory.md](docs/SoftwareInventory.md)

## Mathlib — category theory reading paths (pinned v4.32.2 snapshot)

- [mathlib/Mathlib/CategoryTheory/Category/Basic.lean](mathlib/Mathlib/CategoryTheory/Category/Basic.lean) — `Quiver` → `CategoryStruct` → `Category`
- [mathlib/Mathlib/CategoryTheory/Functor/Basic.lean](mathlib/Mathlib/CategoryTheory/Functor/Basic.lean) — functors
- [mathlib/Mathlib/CategoryTheory/NatTrans.lean](mathlib/Mathlib/CategoryTheory/NatTrans.lean) — natural transformations
- [mathlib/Mathlib/CategoryTheory/Monoidal/Closed/Cartesian.lean](mathlib/Mathlib/CategoryTheory/Monoidal/Closed/Cartesian.lean) — cartesian closed (CCC)

(For live goals / `M-.` into Mathlib, open the built copy under `Beeson/lean4/.lake/packages/mathlib/…`.)

## Scripts

- [scripts/gitcp.sh](scripts/gitcp.sh) — one-shot stage + commit + rebase + push (use this for all commits)
- [scripts/tex2pdf.sh](scripts/tex2pdf.sh) — compile a `.tex` to PDF (XeLaTeX, handles Unicode/Lean symbols)
- [scripts/lean2tex.sh](scripts/lean2tex.sh) — Lean → LaTeX helper
