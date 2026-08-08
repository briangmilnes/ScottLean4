---
round: r0039
from: agent4
to: orchestrator
subject: page-census
date: 2026-0808
started: 2026-0808-11:05
finished: 2026-0808-11:09
---

# r0039 stream 4 — the completeness sweep: a census of every page

## What this measures

`scripts/find-diagrams.py` requires a region at least 40 px tall at 100 dpi with
at least 25 sparse rows. A small inline picture is below that threshold and the
detector cannot see it. This census renders all 44 physical pages at 90 dpi,
reads each as an image, and records every drawn picture — Hasse diagram,
commutative diagram, labelled poset, anything drawn rather than typeset — and
whether a row of
`analyses/diagram-candidates.2026-0808-10:32.orchestrator.log` covers it.

Coordinate conversion used throughout: the 90 dpi render maps to the log's
100 dpi pixels by multiplying by 10/9.

Ownership follows the plan's partition: streams 1–3 own every region **in** the
candidate list (stream 1 = pages 1–16 and 32, stream 2 = pages 17–31 and 33,
stream 3 = pages 34–44); stream 4 owns every picture the detector never flagged.

## Census — one row per physical page

| # | Phys. page | Printed page | Pictures present | Candidate row covers it? | Owner |
| - | ---------- | ------------ | ---------------- | ------------------------ | ----- |
| 1 | 1 | title | none — title block only | rows 255–301, 324–402 fire on the title/affiliation lines (false positives) | — |
| 2 | 2 | contents | none | no rows | — |
| 3 | 3 | 2 | none — solid prose | no rows | — |
| 4 | 4 | 3 | none — solid prose | no rows | — |
| 5 | 5 | 4 | **Figure 1, "Examples of cpo's"** — three Hasse diagrams side by side (`T` a 3-element V; `N⊥` an infinite fan with `⋯`; `ω^T` a chain with `⋮` and a top) | yes — row `5 111–514` (h=403) | stream 1 |
| 6 | 6 | 5 | none — displayed equations only (`fact`, `F(f)(n)` case splits) | rows 537–618, 678–800 fire on those cases (false positives) | — |
| 7 | 7 | 6 | none — BNF grammar displays and a chain of set equations | five rows, all displayed math (false positives) | — |
| 8 | 8 | 7 | **one commutative diagram** — the uniformity square `D --f--> D`, `h` down both sides, `E --g--> E` | yes — row `8 688–849` (h=161) contains it | stream 1 |
| 9 | 9 | 8 | **one commutative diagram** — `D' --f'--> D'`, inclusion `i` down both sides, `D --f--> D` (the Theorem 3 proof) | yes — row `9 210–350` (h=140) contains it | stream 1 |
| 10 | 10 | 9 | none | row 751–884 is the Lemma 4 numbered list plus the `↓x` display (false positive) | — |
| 11 | 11 | 10 | none — displayed equations (`f∘g = id_D`, the `strict(f)(x)` case split, `p_N(x)`) | four rows, all displayed math (false positives) | — |
| 12 | 12 | 11 | none — the two numbered clauses of the effective-presentation definition | no rows | — |
| 13 | 13 | 12 | none — the `M =`, `N =` displays | rows 740–833, 901–969, both displayed math (false positives) | — |
| 14 | 14 | 13 | **one commutative diagram** — the universal property of `×`: `D` above `D×E` above `E` on the left with `fst`/`snd`, `F` on the right, arrows `f`, `g`, and the dashed unique `⟨f,g⟩` | yes — rows `14 681–788` and `14 789–904` together span it | stream 1 |
| 15 | 15 | 14 | **one commutative diagram** — the `curry`/`apply` triangle: `D×E --f--> F`, dashed `curry(f)×id` down to `(E→F)×E`, `apply` back up to `F` | yes — row `15 588–765` (h=177) contains it | stream 1 |
| 16 | 16 | 15 | **one commutative diagram** — the same triangle with `h×id` in place of `curry(f)×id`, for `f = apply∘(h×id_E)` | yes — row `16 106–342` (h=236) contains it | stream 1 |
| 17 | 17 | 16 | none — the λ-notation displays (`g = λy.λx.…`, `λf. f(3)`, `λf. f∘f`) | three rows, all displayed math (false positives) | — |
| 18 | 18 | 17 | none — the smash-product set display and the `smash(x,y)` case split | row 854–977, displayed math (false positive) | — |
| 19 | 19 | 18 | **three commutative diagrams**: (a) the `smash` triangle `D×E`, `smash` down to `D⊗E`, dashed `g` to `F`, `f` across; (b) the `smash` square `D×E --f×g--> D×E` over `D⊗E --f⊗g--> D⊗E`; (c) the `strict_apply`/`strict_curry` triangle | yes, one row each — `19 312–480`, `19 547–626`, `19 777–928` | stream 2 |
| 20 | 20 | 19 | **one commutative diagram** — the coalesced-sum universal property: `D`/`D⊕E`/`E` on the left with `inl`, `inr`, `F` on the right, `f`, `g`, dashed `[f,g]` | yes — row `20 415–641` (h=226) contains it | stream 2 |
| 21 | 21 | 20 | **two pictures**: **Figure 2, "The lift of a cpo"** — two triangles standing for `D` and `D⊥` with `up`/`down` arrows between them and a new bottom dot hung under the right one; and **one commutative diagram** — the `f†` triangle `D`, `up` down to `D⊥`, dashed `f†` to `E`, `f` across | yes — Figure 2 overlaps row `21 224–437` (the row starts below the triangle apexes, at about 90 dpi y=202 against the apexes' y=152, so the row clips the top); the `f†` triangle sits in row `21 782–959` | stream 2 |
| 22 | 22 | 21 | **one commutative diagram** — the separated-sum universal property: `D`/`D+E`/`E` with `inl∘up`, `inr∘up`, `F`, `f`, `g`, dashed `h` | yes — row `22 210–435` (h=225) contains it | stream 2 |
| 23 | 23 | 22 | none — Lemma 10, the powerdomain bullet list, section 5 prose | no rows | — |
| 24 | 24 | 23 | none — the bag-of-fruit prose, indented sentences only | no rows | — |

## Measured result

(filled in when the sweep completes)
