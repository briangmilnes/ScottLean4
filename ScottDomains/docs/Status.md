# Status of the Gunter & Scott 1990 Development in Lean

`main` at `5f2ac51`. Build 1372 jobs, 0 errors, 3 `sorry` warnings, 0 other
warnings. 124 modules, 46,442 lines, 2,122 theorems.

## 1. Extractions — what the paper contains

| # | Kind | Count |
| -- | ---- | ----: |
| 1 | Definitions (unnumbered) | 11 |
| 2 | Numbered theorems | 16 |
| 3 | Numbered lemmas | 13 |
| 4 | Numbered propositions | 1 |
| 5 | — numbered results, total | **30** |
| 6 | — conjuncts those 30 decompose into | 93 |
| 7 | Prose statements | 146 |
| 8 | Examples | 1 |
| 9 | Figures | 4 |

## 2. Represented in Lean

| # | Kind | Represented | Of | Not stated |
| -- | ---- | ----------: | -: | ---------: |
| 1 | Definitions | 11 | 11 | 0 |
| 2 | Theorems | 16 | 16 | 0 |
| 3 | Lemmas | 13 | 13 | 0 |
| 4 | Propositions | 1 | 1 | 0 |
| 5 | Prose statements | 86 | 146 | 60 |
| 6 | Examples | 1 | 1 | 0 |

## 3. Corrected — could not be transcribed as printed

| # | Kind | Printing | Reading | Semantic | Corrected | — proven | — unproven |
| -- | ---- | -------: | ------: | -------: | --------: | -------: | ---------: |
| 1 | Definitions | 1 | 0 | 1 | 2 | 2 | 0 |
| 2 | Theorems | 1 | 1 | 2 | 4 | 2 | 2 |
| 3 | Lemmas | 1 | 2 | 0 | 3 | 2 | 1 |
| 4 | Propositions | 0 | 0 | 0 | 0 | 0 | 0 |
| 5 | Examples | 0 | 0 | 0 | 0 | 0 | 0 |
| 6 | — total | 3 | 3 | 3 | **9** | **6** | **3** |
| 7 | Prose statements | — | — | — | — | — | not classified |

### Printing error — the page is garbled; the mathematics is right

| # | Where | What | Corrected to | Proven |
| -- | ---- | ---- | ------------ | :----: |
| 1 | Lemma 9 | the PDF drops every `⊗` and every `⊥`, so which operators the laws range over is unreadable | `lem9_1`…`lem9_6`; items 3 and 5 also carry kernel-checked negations of the printed forms | **yes** |
| 2 | Theorem 14 | the list of characterizations is garbled | `thm14`, both directions | **yes** |
| 3 | §7.4 worked example | reverses the paper's own definition — printed `b ⊢ a` where both papers give `a ⊢ b` | read in the paper's direction; the paper's counts 1, 2, 5, 20 select it over the rival | **yes** |

### Reading error — ours; the paper is right

| # | Where | What | Corrected to | Proven |
| -- | ---- | ---- | ------------ | :----: |
| 1 | Theorem 29, sentence 2 | dropped "domain" from "any bifinite domain", making it false | `Thm29SecondAtDomains` | no |
| 2 | Lemma 28 | quantified over all `U`; the paper states it over its own `U` | `PRep.Lemma28AtU`, nine conjuncts, no hypotheses | **yes** |
| 3 | Lemma 30 | same shape — a universal closure the paper does not claim | `Lemma30AtV`, arity 1 | no |

### Semantic error — the mathematics is wrong as stated

| # | Where | Whose | What | Corrected to | Proven |
| -- | ---- | ----- | ---- | ------------ | :----: |
| 1 | Theorem 26 | **paper** | false for any signature with two or more 0-ary slots, including the paper's own `(2,0,0,0,0,0)` | `thm26` with `hs : ∀ i, 0 < s i` | **yes** |
| 2 | Theorem 7 | ours | guarded on compactness where the sentence is about boundedness; on the paper's index the join always exists, so it tests neither | `StepFunctionsDecidable` over `IsStepEnumeration`, existentially quantified | no |
| 3 | §7.4 order relation | **paper** | not reflexive — `b = (⊥,∅)` fails `b ⊢ b`; it is the strict part | reflexive closure; `Colimit.V` built on it, `isoPlus : V ≃o Plus V` | **yes** |

## 4. Proof state

| # | Kind | Proven | Unproven | Of |
| -- | ---- | -----: | -------: | -: |
| 1 | Theorems | 14 | 2 | 16 |
| 2 | Lemmas | 12 | 1 | 13 |
| 3 | Propositions | 1 | 0 | 1 |
| 4 | — numbered results | **27** | **3** | 30 |
| 5 | Prose statements | 70 | 16 | 86 stated |
| 6 | Examples | 1 | 0 | 1 |

| # | Unproven result | State |
| -- | -------------- | ----- |
| 1 | Theorem 7 | sentences 1 and 2 proven; the recursive forms are not |
| 2 | Theorem 29 | sentence 1 proven; sentence 2 is not |
| 3 | Lemma 30 | stated at `V`, arity 1 — one named input left |

All three reduce to **three** statements, each carried by Gunter & Scott in 1990.
Each is a Lean `theorem` ending in `sorry`, so the build reports it (r0052):

| # | The unproven statement | Lean theorem | Blocks |
| -- | --------------------- | ------------ | ------ |
| 1 | `RecursiveNormal` for `K(D → E)` — decide whether two basis elements are bounded, and compute their join's index | `R49.Agent3.scottHomCRecursive_unproven` | Theorem 7, arrow |
| 2 | the same over `K(D ⊸ E)` — no proved reduction carries recursiveness across `K(D ⊸ E) ↪ K(D → E)` | `R49.Agent3.strictHomCRecursive_unproven` | Theorem 7, strict |
| 3 | `Theorem29Normal` at infinite `K(E)` — realize the type over the tower's image, not the η-image; finite bases are proven | `LemThirty.theorem29Normal_unproven` | Theorem 29, Lemma 30 |

## 5. Proof work state

| # | Kind | Left with a `sorry` |
| -- | ---- | ------------------: |
| 1 | Definitions | 0 |
| 2 | Theorems | **3** |
| 3 | Lemmas | 0 |
| 4 | Propositions | 0 |
| 5 | Prose statements | 0 |
| 6 | Examples | 0 |

`sorry` **3**, `axiom` 0, since r0052; `sorry` was 0 from r0042 to r0051. Every
unproved result is a `theorem … := sorry`, so the unproven count **is** the
`sorry` count: the three of table 4's second table above. Exactly three package
constants depend on `sorryAx` — those three theorems — and no other declaration
does, because none applies them: every consumer still takes its claim as an
explicit hypothesis.

## 6. Size

| # | Quantity | Count |
| -- | ------- | ----: |
| 1 | Files | 124 |
| 2 | Modules | 124 |
| 3 | Lines | 46,442 |
| 4 | Theorems | 2,122 |
| 5 | `def`s | 829 |
| 6 | — of those, `Prop`-valued | 120 |
| 7 | Structures and classes | 25 |
| 8 | Constants in the environment | 4,393 |
| 9 | Build jobs | 1,372 |

## 7. Mathlib theories referenced

34 distinct Mathlib modules, across 8 top-level theories.

| # | Theory | Modules |
| -- | ----- | ------: |
| 1 | `Mathlib.Data` | 12 |
| 2 | `Mathlib.Order` | 11 |
| 3 | `Mathlib.SetTheory` | 3 |
| 4 | `Mathlib.Algebra` | 3 |
| 5 | `Mathlib.Logic` | 2 |
| 6 | `Mathlib.Computability` | 1 |
| 7 | `Mathlib.Combinatorics` | 1 |
| 8 | `Mathlib.Tactic` | 1 |

`Mathlib.Order.CompletePartialOrder` and `Mathlib.Order.ScottContinuity` are the
two the development is built on; `Mathlib.Computability.RE` is the only one §3.2
needs.

## Reproducing

    scripts/counts.sh                     # modules, lines, theorems, sorry
    scripts/numbered-status.sh            # declarations per numbered result
    scripts/a6-env-scan.sh <out>          # then a6-summarize.py
    scripts/a8-claim-check.sh             # prose staleness against the environment
    scripts/compile.sh -r <round>         # build
    scripts/mathlib-imports.sh            # tables 6 and 7

Tables 1 and 9 come from `pdftotext -layout` on the paper. The text layer drops
the `fi` ligature — `Definition` reads `De nition`, `bifinite` reads `bi nite` —
so a grep for `Definition` returns 0 and is wrong.
