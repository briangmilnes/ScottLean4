---
round: r0006
from: orchestrator
to: orchestrator
subject: function-space
date: 2026-0806-13:52
status: pending
related:
  - plans/r0005-plan-from-orchestrator-to-orchestrator-powerset-domain.md
---

# r0006 — The continuous function space `D → E` as a cpo

Theorem 7's proof opens with the sentence this round formalizes:

> Proof: (Sketch) It is not hard to see that `D → E` is a bounded complete cpo
> whenever `E` is. To prove that `D → E` is a domain we must demonstrate its
> basis. Suppose `N ⊆ K(D)` is finite and `s : N → K(E)` is monotone. Then the
> function `step(s)` … These are called step functions …

The paper splits the theorem exactly where this round stops. r0006 delivers the
first sentence's cpo structure; the step-function basis, bounded completeness of
the function space, and Theorem 7 itself are r0007.

Deliverable: `ScottDomains/ScottHom.lean` — the type of Scott-continuous
functions, its pointwise order, and a `CompletePartialOrder` instance.

Everything downstream needs this: Theorem 7, Lemmas 8, 9, 10, 17, 23, Theorem 18,
and the `D∞` construction of §7 all quantify over the function space.

## What Mathlib supplies and what it does not (measured)

`CompletePartialOrder` occurs in 19 Mathlib files; none of them is a function
space. Mathlib's bundled continuous-function type is
`OmegaCompletePartialOrder.ContinuousHom` (`α →𝒄 β`), which is **ω**-continuous —
built on chains, not directed sets. The paper is directed throughout, and r0004's
classes are stated over `CompletePartialOrder`, so the ω-type is the wrong object
here. `ScottContinuous` (`Order/ScottContinuity.lean:148`) is a predicate with
composition and constant lemmas but no bundled type and no closure results for
suprema.

## The crux, and why it is not a double-supremum exchange

The one real proof is that the pointwise supremum of a directed set `d` of
Scott-continuous functions is Scott-continuous. The obvious route — expand both
sides into iterated suprema and exchange them — needs a directedness argument for
each intermediate set. It is avoidable. Write `F x := sSup ((· x) '' d)` and let
`s` be nonempty directed with `IsLUB s a`:

1. The evaluation image `(· x) '' d` is directed, because `d` is directed in the
   pointwise order.
2. `F` is monotone: for `x ≤ y`, every `f x` with `f ∈ d` satisfies `f x ≤ f y ≤ F y`,
   so `DirectedOn.sSup_le` gives `F x ≤ F y`.
3. `F a` is an upper bound of `F '' s`, from 2 and `x ≤ a`.
4. `F a` is the least such: let `u` bound `F '' s`. By `DirectedOn.sSup_le` it
   suffices that `f a ≤ u` for each `f ∈ d`. Continuity of `f` gives
   `IsLUB (f '' s) (f a)`, so it suffices that `f x ≤ u` for each `x ∈ s` — and
   `f x ≤ F x ≤ u` because `F x ∈ F '' s`.

No exchange, no auxiliary directedness beyond step 1. The argument also goes
through for `d = ∅`, where every appeal to `DirectedOn.sSup_le` is vacuous.

## The one structural obstacle: `SupSet` is total, continuity is not

`CompletePartialOrder` extends `SupSet`, so `sSup` must return a `ScottHom` for
*every* set of functions. But the pointwise supremum of a non-directed set need
not be continuous — step 2 above fails without directedness, and in a dcpo the
supremum of a non-directed set is unconstrained anyway.

Resolution: define `sSup d` by `dite (DirectedOn (· ≤ ·) d)`, returning the
pointwise supremum when the hypothesis holds and `⊥` (the constant-`⊥` function,
continuous by `ScottContinuous.const`) otherwise. `CompletePartialOrder` only
ever constrains `sSup` on directed sets, so the junk value is invisible to every
consumer. The cost is that the instance depends on `Classical.choice`; that is
reported, not hidden.

This forces a construction order: `PartialOrder`, then `OrderBot`, then `SupSet`,
then `CompletePartialOrder`.

## Steps, each with its verification

| # | Step | Verify |
| -- | ---- | ------ |
| 1 | `structure ScottHom (α β) [Preorder α] [Preorder β]` — `toFun`, `scottContinuous'` | elaborates |
| 2 | `FunLike` instance, `@[ext]`, coercion `@[simp]` lemmas | `ext` closes a pointwise goal |
| 3 | `instance : PartialOrder (ScottHom α β)` — pointwise | antisymmetry via `ext` |
| 4 | `instance [OrderBot β] : OrderBot (ScottHom α β)` — constant `⊥`, continuous by `ScottContinuous.const` | elaborates |
| 5 | `theorem directedOn_eval_image` — `d` directed ⟹ `(· x) '' d` directed | unfold the pointwise order |
| 6 | `theorem scottContinuous_pointwiseSup` — the crux, steps 1–4 of the argument above | the four-step argument; no `sorry` |
| 7 | `instance : SupSet (ScottHom α β)` via `dite` on directedness | elaborates |
| 8 | `instance : CompletePartialOrder (ScottHom α β)` — `lubOfDirected` | upper bound from `DirectedOn.le_sSup`; least from `DirectedOn.sSup_le`; the `d = ∅` case is the same proof |
| 9 | `theorem coe_sSup_of_directed` — `sSup d x = sSup ((· x) '' d)` when `d` is directed | strips the `dite` for downstream use |
| 10 | `lake build`; `#print axioms` on every declaration | 0 errors, 0 warnings, 0 `sorry` |
| 11 | Update `docs/PaperInventory.md`, `INDEX.md` | function space recorded as infrastructure, not as a numbered result |

Steps 5 → 6 → 7 → 8 → 9 are a chain; 1–4 precede all of them. Span is 8
sequential elaborations, the longest of any round so far.

## Design decisions

1. **A bundled structure, not the bare predicate.** The order, the supremum, and
   every later result are structure on the *type* of continuous functions. Using
   `{f // ScottContinuous f}` would work but gives no `FunLike` and no `ext`.

2. **No notation in this round.** `→𝒄` already means ω-continuous in Mathlib's
   `OmegaCompletePartialOrder` scope; introducing a second `→𝒄` for a different
   notion invites exactly the confusion r0003 avoided with `≪`. If a symbol is
   wanted, it is a one-line addition once the type has users.

3. **`α` needs only `[Preorder α]`.** Scott continuity of `f : α → β` constrains
   `f`'s behavior on directed subsets of `α` that *have* suprema; it does not
   require `α` to be complete. Asking for `[CompletePartialOrder α]` here would
   narrow every downstream statement for nothing.

## Acceptance criteria

| # | Criterion | Measurement |
| -- | --------- | ----------- |
| 1 | Builds | `lake build` exits 0, 0 errors, 0 warnings |
| 2 | Nothing unproved | `grep -c sorry` = 0; no `sorryAx` |
| 3 | The instance is usable | `coe_sSup_of_directed` (step 9) is stated and proved, so downstream proofs never see the `dite` |
| 4 | The classical dependency is confined and reported | `#print axioms` distinguishes step 6 (should be `propext` only) from steps 7–8 (`Classical.choice`, from the `dite`) |

## Out of scope

`BoundedComplete (ScottHom α β)`, step functions, algebraicity of the function
space, and Theorem 7. The paper's own proof sketch separates them, and bounded
completeness of the function space needs suprema of *bounded* rather than
directed families, whose continuity argument is not the one above.

## Revision point

This plan is written before r0005 runs. Re-read it after r0005's report: if
`Set X` exposes a difficulty in the r0004 class shapes — most plausibly in how
`IsAlgebraic` interacts with a `CompleteLattice`-derived `CompletePartialOrder`
instance — steps 7 and 8 here are where the same difficulty would recur, and the
plan should be revised before execution rather than during.
