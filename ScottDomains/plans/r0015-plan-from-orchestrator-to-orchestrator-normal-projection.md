---
round: r0015
from: orchestrator
to: orchestrator
subject: normal-projection
date: 2026-0806-15:00
status: done
related:
  - reports/r0015-report-from-orchestrator-to-user-normal-projection.md
---

# r0015 — `p_N`, the projection determined by a normal subposet

> Suppose, on the other hand, that `N ◁ K(D)`. Then it is easy to check that the
> function `p_N : D → D` given by `p_N(x) = ⨆{y ∈ N | y ⊑ x}` is a finitary
> projection. Indeed, the correspondence `N ↦ p_N` is inverse to the
> correspondence `p ↦ im(p) ∩ K(D)` …

Deliverable: `ScottDomains/NormalProjection.lean` — the construction, its
continuity, that it is a projection, and the first half of the inverse
correspondence.

## The step the paper's "easy to check" hides

`N ◁ K(D)` gives directedness of `N ∩ ↓x` only for `x ∈ K(D)`. Defining `p_N`
needs it for **every** `x ∈ D`. That is where algebraicity of `D` is spent: given
`a, b ∈ N` below an arbitrary `x`, the compacts below `x` are directed, so some
compact `k ≤ x` dominates both; `N ∩ ↓k` is directed because `k ∈ K(D)`, and its
witness is below `k ≤ x`. It is the only use of algebraicity in the construction.

## Steps

| # | Step | Verify |
| -- | ---- | ------ |
| 1 | `IsNormalIn.nonempty_inter_Iic` | `⊥ ∈ N` by Lemma 4.3 |
| 2 | `IsNormalIn.directedOn_inter_Iic` for every `x` | the argument above |
| 3 | `normalFun`, `normalFun_le`, `le_normalFun`, `monotone_normalFun` | `DirectedOn.sSup_le` / `le_sSup` |
| 4 | `scottContinuous_normalFun` | a `y ∈ N` below `⨆s` is compact, so already below some `x ∈ s` |
| 5 | `normalHom`, `isProjection_normalHom` | idempotence `≥` is the only step with content |
| 6 | `range_normalHom_inter_compacts : im(p_N) ∩ K(D) = N` | `⊇` fixes members of `N`; `⊆` uses compactness to pull the supremum back |
| 7 | `normalHom_mono`, `IsProjection.range_mono` | both directions of order preservation |
| 8 | Build, docs, PDF, commit | 0 errors, 0 warnings, 0 `sorry` |

## Acceptance criteria

| # | Criterion | Measurement |
| -- | --------- | ----------- |
| 1 | Builds | 0 errors, 0 warnings |
| 2 | Nothing unproved | 0 `sorry`, no `sorryAx` |
| 3 | Half the correspondence | `im(p_N) ∩ K(D) = N` proved |
| 4 | Order preservation both ways | `normalHom_mono` and `IsProjection.range_mono` |

## Out of scope

That `p_N` is **finitary** (`im(p_N)` a domain), the reverse identity
`p_{im(p) ∩ K(D)} = p`, and Theorem 6 assembled as an order isomorphism.
