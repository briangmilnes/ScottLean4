---
round: r0014
from: orchestrator
to: orchestrator
subject: lemma5
date: 2026-0806-14:55
status: done
related:
  - reports/r0014-report-from-orchestrator-to-user-lemma5.md
---

# r0014 — Lemma 5

> **Lemma 5** If `D` is a domain and `p : D → D` is a finitary projection, then
> the set of compact elements of `im(p)` is just `im(p) ∩ K(D)`. Moreover,
> `im(p) ∩ K(D) ◁ K(D)`.

Deliverable: `ScottDomains/FinitaryProjection.lean`.

## Steps

| # | Step | Verify |
| -- | ---- | ------ |
| 1 | `IsProjection.isLUB_val_image` — a least upper bound in `im(p)` is one in `D` | an upper bound `v` need not lie in `im(p)`, but `p v` does and still bounds; `p v ≤ v` closes it |
| 2 | First sentence, `⟸` | a directed set of the subtype has the same lub either way (step 1) |
| 3 | First sentence, `⟹` | push `s ⊆ D` into `im(p)` by `p`; `p x ≤ x` converts the witness back |
| 4 | `IsFinitaryProjection.domain` | `Exists.choose_spec` |
| 5 | Second sentence | algebraicity of `im(p)` applied to `p x`, then step 2/3 to move compactness across |
| 6 | Build, axioms, docs, PDF, commit | 0 errors, 0 warnings, 0 `sorry` |

## Acceptance criteria

| # | Criterion | Measurement |
| -- | --------- | ----------- |
| 1 | Builds | 0 errors, 0 warnings |
| 2 | Nothing unproved | 0 `sorry`, no `sorryAx` |
| 3 | Lemma 5 complete | both sentences |
| 4 | Hypotheses attributed | the first sentence stated for `IsProjection`, not `IsFinitaryProjection` |
