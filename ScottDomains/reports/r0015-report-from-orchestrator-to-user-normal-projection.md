---
round: r0015
from: orchestrator
to: user
subject: normal-projection
date: 2026-0806-15:03
started: 2026-0806-15:00
finished: 2026-0806-15:03
related:
  - plans/r0015-plan-from-orchestrator-to-orchestrator-normal-projection.md
  - reports/r0014-report-from-orchestrator-to-user-lemma5.md
---

# r0015 — `p_N` built, and half of Theorem 6's correspondence

`ScottDomains/NormalProjection.lean`: 144 lines, 0 `sorry`, 0 warnings. Elapsed
3 minutes.

| # | Criterion | Measurement |
| -- | --------- | ----------- |
| 1 | Builds | 0 errors, 0 warnings |
| 2 | Nothing unproved | 0 `sorry`, no `sorryAx` |
| 3 | Half the correspondence | `range_normalHom_inter_compacts : im(p_N) ∩ K(D) = N` |
| 4 | Order preservation both ways | `normalHom_mono` and `IsProjection.range_mono` |

## What the paper's "easy to check" hides

The paper defines `p_N(x) = ⨆{y ∈ N | y ⊑ x}` and says it is "easy to check" that
this is a finitary projection. The first thing to check is not stated at all:
**`N ◁ K(D)` gives directedness of `N ∩ ↓x` only for compact `x`**, while the
definition of `p_N` needs it for every `x ∈ D`.

That is where algebraicity of `D` is spent, and it is the only place the
construction uses it. Given `a, b ∈ N` below an arbitrary `x`, the compacts below
`x` are directed, so some compact `k ≤ x` dominates both; then `N ∩ ↓k` *is*
directed, because `k ∈ K(D)`, and its witness lies below `k ≤ x`.

Continuity has a similar shape: the least-upper-bound half works because a
`y ∈ N` below `⨆s` is **compact** — `N ⊆ K(D)` — so it is already below some
`x ∈ s`, hence below `p_N x`.

## Half the correspondence

`im(p_N) ∩ K(D) = N`. The `⊇` inclusion is that `p_N` fixes every member of `N`,
since such a `y` is the greatest element of `N ∩ ↓y`. The `⊆` inclusion is the
interesting one: a compact `z` in the image satisfies `z = ⨆(N ∩ ↓z)`, and
compactness pulls the supremum back into the set — some `y ∈ N` has `z ≤ y ≤ z`.

Order preservation holds in both directions, which the isomorphism will need:
a larger normal subposet gives a pointwise larger projection, and if `p ≤ q` are
projections then `im(p) ⊆ im(q)` — because `p y = y` forces `y ≤ q y ≤ y`.

## Elaboration failures

Two. `rw [← hfix]` rewrote *both* occurrences of `z`, turning the goal into a
statement about `N ∩ ↓(p_N z)`; replacing it with a targeted
`rwa [show sSup (N ∩ Set.Iic z) = z from hfix] at h` fixed it — the `show` works
because `normalFun N z` is definitionally that supremum. And
`IsProjection.range_mono` needed `omit [IsAlgebraic α] in`, since it holds for any
projections at all.

## Where Theorem 6 stands

| # | Component | Status |
| -- | --------- | ------ |
| 1 | `p_N` is well defined and continuous | done |
| 2 | `p_N` is a projection | done |
| 3 | `im(p_N) ∩ K(D) = N` | done |
| 4 | both maps are monotone | done |
| 5 | `p_N` is **finitary** — `im(p_N)` is a domain | remaining |
| 6 | `p_{im(p) ∩ K(D)} = p` | remaining |
| 7 | assembled as an order isomorphism | remaining |

Thirteen modules, 1918 lines, 0 `sorry`, 0 warnings. Numbered results **3 of 28**;
definitions **7 of ≈13**.
