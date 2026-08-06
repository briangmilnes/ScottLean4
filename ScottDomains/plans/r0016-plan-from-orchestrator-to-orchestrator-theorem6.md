---
round: r0016
from: orchestrator
to: orchestrator
subject: theorem6
date: 2026-0806-15:06
status: done
related:
  - reports/r0016-report-from-orchestrator-to-user-theorem6.md
---

# r0016 — Theorem 6

> **Theorem 6** For any domain `D` there is an isomorphism between the cpo of
> normal substructures of `K(D)` and the poset `Fp(D)` of finitary projections
> on `D`.

r0014 gave `p ↦ im(p) ∩ K(D)` landing in the normal substructures (Lemma 5);
r0015 built `p_N`, showed it is a projection, and proved `im(p_N) ∩ K(D) = N`.

Deliverable: `ScottDomains/Theorem6.lean` — that `p_N` is **finitary**, the
reverse identity `p_{im(p) ∩ K(D)} = p`, and the assembled statement.

## Steps

| # | Step | Verify |
| -- | ---- | ------ |
| 1 | `isLUB_of_isLUB_val_image` — converse of r0014's transfer | direct |
| 2 | `val_image_compactsBelow : val '' compactsBelow y = N ∩ ↓y` | Lemma 5 identifies the compacts, r0015 identifies which elements |
| 3 | `isAlgebraic_range_normalHom` | via steps 1–2 and `p_N y = y` on the image |
| 4 | `countable_compacts_range_normalHom` | the basis is `N ⊆ K(D)`, countable |
| 5 | `isFinitaryProjection_normalHom` | steps 3–4 |
| 6 | `normalFun_range_inter_compacts : p_{im(p) ∩ K(D)} = p` | `≤` from `y = p y`; `≥` from algebraicity of `im(p)` |
| 7 | `theorem6` | the five constituent facts |

## Acceptance criteria

| # | Criterion | Measurement |
| -- | --------- | ----------- |
| 1 | Builds | 0 errors, 0 warnings |
| 2 | Nothing unproved | 0 `sorry`, no `sorryAx` |
| 3 | Theorem 6 complete | both round trips and both monotonicity directions |
