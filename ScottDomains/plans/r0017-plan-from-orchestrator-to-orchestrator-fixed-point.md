---
round: r0017
from: orchestrator
to: orchestrator
subject: fixed-point
date: 2026-0806-15:14
status: done
related:
  - reports/r0017-report-from-orchestrator-to-user-fixed-point.md
---

# r0017 — Theorem 1, and auditing the two "reuse from Mathlib" claims

Prompted by the question "what happened to Theorems 1, 2, 3?". The inventory
excluded Theorems 1 and 2 from the work list as Mathlib reuse, which is why the
outstanding count read 28 rather than 30. Neither claim had ever been checked by
building anything, and the inventory has been wrong three times before.

## What the audit found

| # | Result | Claim | Measurement |
| -- | ------ | ----- | ----------- |
| 1 | Thm 1 | `✓ OrderHom.lfp` | **Wrong.** `OrderHom.lfp` (`Order/FixedPoints.lean:49`) is Knaster–Tarski: complete lattice, monotone `f`, fixed point as an infimum of pre-fixed points. Theorem 1 is Kleene's: cpo with `⊥`, *continuous* `f`, fixed point as `⨆ₙ fⁿ(⊥)`. Neither implies the other |
| 2 | Thm 2 | `✓ Function.Embedding.schroederBernstein` | **Name wrong, theorem present.** It is `Function.schroeder_bernstein` (`SetTheory/Cardinal/SchroederBernstein.lean:90`) |
| 3 | Thm 3 | `✗ prove` | correctly marked; skipped so far because the work was ordered by dependency |

So the denominator was wrong: **29** numbered results need proof, not 28.

## Deliverable

`ScottDomains/FixedPoint.lean` — Theorem 1 in the paper's setting,
`[CompletePartialOrder α]` and `ScottContinuous f`.

| # | Step | Verify |
| -- | ---- | ------ |
| 1 | `kleeneChain f = {fⁿ(⊥)}`, nonempty | `⊥ = f^[0] ⊥` |
| 2 | `monotone_iterate_bot` | `monotone_nat_of_le_succ`, induction |
| 3 | `directedOn_kleeneChain` | a chain is directed, via `max` |
| 4 | `kleeneFix f = ⨆ chain` | — |
| 5 | `map_kleeneFix` — it is a fixed point | continuity, then the image chain has the same supremum since the dropped element is `⊥` |
| 6 | `iterate_bot_le`, `kleeneFix_le` | induction along the chain |
| 7 | `theorem1 : IsLeast {a \| f a = a} (kleeneFix f)` | steps 5–6 |

## Acceptance criteria

| # | Criterion | Measurement |
| -- | --------- | ----------- |
| 1 | Builds | 0 errors, 0 warnings |
| 2 | Nothing unproved | 0 `sorry`, no `sorryAx` |
| 3 | Stated in the paper's setting | `CompletePartialOrder` + `ScottContinuous`, not `CompleteLattice` + `Monotone` |
| 4 | Inventory corrected | Theorem 1 moves out of "reuse"; Theorem 2's name fixed; denominator 28 → 29 |
