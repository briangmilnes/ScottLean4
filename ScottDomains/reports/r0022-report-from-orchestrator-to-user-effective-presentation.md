---
round: r0022
from: orchestrator
to: user
subject: effective-presentation
date: 2026-0806-16:00
started: 2026-0806-15:54
finished: 2026-0806-16:00
related:
  - reports/r0021-report-from-orchestrator-to-user-currying.md
---

# r0022 — §3.2's effective presentation; §3 complete

`ScottDomains/EffectivePresentation.lean`: 0 `sorry`, 0 warnings. Elapsed
6 minutes. **Eighth of ≈13 definitions.**

| # | Criterion | Measurement |
| -- | --------- | ----------- |
| 1 | Builds | 0 errors, 0 warnings |
| 2 | Nothing unproved | 0 `sorry`, no `sorryAx` |
| 3 | §3 complete | §3.1 (r0012–r0016) and §3.2's definition |
| 4 | Gaps recorded, not approximated | the paper's *computable function* is left out with the reason stated |

## Reading "effectively decidable"

A `Decidable` instance in Lean *is* a program that decides the proposition, so
`DecidablePred` is a faithful reading of the paper's "effectively decidable" for
both conditions. It is deliberately not Mathlib's `ComputablePred`, which
additionally ties the decision to a recursion-theoretic model — nothing in the
paper's use of conditions 1 and 2 needs that, and the weaker reading is what
makes the structure usable.

Both conditions are stated on `ℕ` and `Finset ℕ` — the *indices* — rather than on
the domain. That is the point of a presentation: it moves decidability questions
onto a countable index set, where they can be asked at all.

## One thing left out on purpose

The paper continues: a continuous `f` is **computable** when `{m | eₘ ⊑ f(dₙ)}`
is recursively enumerable for every `n`. Mathlib v4.32.2 has **no `RePred` or
equivalent** — a grep for `def RePred` across the library returns nothing.
Formalizing it means building r.e. predicates first, which is recursion theory
rather than domain theory. I left it out rather than approximate it with
`Decidable` (which would be strictly stronger and therefore wrong), and recorded
the gap in the inventory.

## Elaboration failure

One, and it is another instance of Lean's per-statement discipline you asked
about. `countable_compacts` states `(compacts α).Countable` — a conclusion that
never mentions the presentation `d`. Lean's automatic section-variable inclusion
therefore dropped `d`, and the proof could not refer to it. `include d in`
restores it, and must sit **before** the docstring rather than between it and the
declaration.

## Totals

Nineteen modules, 2820 lines, 125 live theorems (+6 commented out), 0 `sorry`,
0 warnings. Numbered results **7 of 29**. Prose claims **11**. Definitions
**8 of ≈13**.

**§2 and §3 are complete.** Remaining definitions: smash product, the three
powerdomains, bifinite/Plotkin order, and `D∞`.
