---
round: r0021
from: orchestrator
to: user
subject: currying
date: 2026-0806-15:50
started: 2026-0806-15:42
finished: 2026-0806-15:50
related:
  - reports/r0019-report-from-orchestrator-to-user-product.md
---

# r0021 — Currying, and Lemma 8 complete

**Seventh of the 29 numbered results.** `ScottDomains/Currying.lean`: 150 lines,
0 `sorry`, 0 warnings. Elapsed 8 minutes.

| # | Criterion | Measurement |
| -- | --------- | ----------- |
| 1 | Builds | 0 errors, 0 warnings |
| 2 | Nothing unproved | 0 `sorry`, no `sorryAx` |
| 3 | Lemma 8 complete | all four parts; `scottHomCurry : ScottHom α (ScottHom β γ) ≃o ScottHom (α × β) γ` |

## The asymmetry between the two directions

Currying is easy. Fixing `x`, the map `y ↦ f (x, y)` is continuous because
`y ↦ (x, y)` carries a directed set to a directed set whose least upper bound is
`(x, ⨆s)` — the first coordinate image is the singleton `{x}` and the second is
`s`, so `isLUB_prod` splits it into `isLUB_singleton` and the hypothesis.

Uncurrying is where the work is. The goal is `g (⨆ fst s) (⨆ snd s) ⊑ u` from
`u` bounding `{g q.1 q.2 | q ∈ s}`, and the two suprema run over *different
projections of the same directed set*. The argument peels them one at a time —
continuity of `g` into the function space, then continuity of `g x` — which
leaves a goal about `g x y` where `x` and `y` came from **different members** of
`s`. Directedness of `s` in the **product** is what supplies a single member
above both, and that is the step that has no analogue in the easy direction.

`isLUB_eval_image_of_isLUB` — a least upper bound in `D → E` is a least upper
bound pointwise — is the bridge that makes the first peel possible. It was
already proved inline inside `isCompactElement_step` (r0008); with a second
caller it moved into `ScottHom.lean` as a named lemma.

## Four elaboration failures, one of them instructive about Lean's ordering

**Placement.** `isLUB_eval_image_of_isLUB` was first written directly after
`coe_sSup_of_directed`, which is *before* the `CompletePartialOrder (ScottHom α β)`
instance in the same file. `DirectedOn.isLUB_sSup` could not elaborate, because
Lean processes a file strictly per statement and an instance is in scope only
below the point it is registered. Moving the lemma after the instance fixed it.

**`rintro rfl` chose the wrong substitution.** Proving
`Prod.fst '' ((fun y => (x, y)) '' s) = {x}` by `ext z` then `rintro rfl` on
`z = x` eliminated `x` — the theorem's own parameter — rather than `z`, leaving
"unknown identifier `x`". `Set.eq_singleton_iff_unique_mem` avoids the choice
entirely and is shorter.

**Anonymous constructor with an undetermined type.** Passing
`⟨(x₀, y), ⟨x₀, hx₀, rfl⟩⟩` directly as the nonemptiness argument of
`f.scottContinuous` failed, because the implicit set was not yet fixed; naming it
in a `have` with an explicit type determines it.

**Wrong membership.** `hu hx y` supplied `x ∈ s` where an element of the *image*
was wanted — `hu ⟨x, hx, rfl⟩ y`.

## Totals

Eighteen modules, 2672 lines, 129 live theorems (+6 commented out), 0 `sorry`,
0 warnings. Numbered results **7 of 29**. Prose claims **11**. Definitions
**7 of ≈13**.

Next: the smash product `D ⊗ E`, sum and lift, then Lemma 9 — the strict
analogues of Lemma 8 — and Lemma 10.
