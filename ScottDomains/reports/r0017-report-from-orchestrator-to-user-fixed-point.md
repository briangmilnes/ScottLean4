---
round: r0017
from: orchestrator
to: user
subject: fixed-point
date: 2026-0806-15:18
started: 2026-0806-15:14
finished: 2026-0806-15:18
related:
  - plans/r0017-plan-from-orchestrator-to-orchestrator-fixed-point.md
  - reports/r0016-report-from-orchestrator-to-user-theorem6.md
---

# r0017 — Theorem 1 proved; the "reuse from Mathlib" claims audited

**Fifth numbered result, and a correction to the denominator.**
`ScottDomains/FixedPoint.lean`: 117 lines, 0 `sorry`, 0 warnings. Elapsed
4 minutes.

| # | Criterion | Measurement |
| -- | --------- | ----------- |
| 1 | Builds | 0 errors, 0 warnings |
| 2 | Nothing unproved | 0 `sorry`, no `sorryAx` |
| 3 | Stated in the paper's setting | `[CompletePartialOrder α]` + `ScottContinuous f` |
| 4 | Inventory corrected | Theorem 1 out of "reuse", Theorem 2's name fixed, denominator 28 → 29 |

## The audit, which the question forced

Theorems 1 and 2 were excluded from the work list as Mathlib reuse. Neither claim
had ever been checked by building anything.

**Theorem 1's claim was wrong.** `OrderHom.lfp` is Knaster–Tarski: it needs a
**complete lattice** and only **monotonicity**, and produces the fixed point as an
infimum of pre-fixed points. Theorem 1 is Kleene's: it needs only a **cpo** with
`⊥` and a **continuous** `f`, and produces the fixed point as `⨆ₙ fⁿ(⊥)`. Neither
implies the other — a cpo need not be a lattice, and Knaster–Tarski does not
exhibit the fixed point as a limit of finite approximations, which is the entire
point in a semantics of recursion. Mathlib's nearest cpo-side result,
`ωSup_iterate_mem_fixedPoint`, is ω-based, while the paper is directed throughout.

**Theorem 2's theorem is present but under a different name.** It is
`Function.schroeder_bernstein` (`SetTheory/Cardinal/SchroederBernstein.lean:90`);
the inventory's `Function.Embedding.schroederBernstein` does not exist.

**Theorem 3 was correctly marked outstanding.** I had skipped it because I ordered
the work by dependency — definitions first, then the §3.1 results resting on them —
rather than by paper order. That is a defensible order but it should have been
stated; it is now.

So the denominator was wrong: **29** numbered results need proof, not 28. Five are
done.

## The proof

`kleeneChain f = {fⁿ(⊥) | n}` is nonempty and directed because it is an ascending
chain. `kleeneFix f` is its supremum. Continuity gives
`f (⨆ chain) = ⨆ (f '' chain)`, and the image has the same supremum as the chain
itself — it is the chain minus its first element, and that element is `⊥`, so it
contributes nothing to a supremum. Leastness is an induction along the chain: every
iterate is below any pre-fixed point.

Both forms are stated: least among fixed points (the paper's Theorem 1) and least
among pre-fixed points, which is what recursion arguments usually want.

## Elaboration failures

Two, both about rewriting `Function.iterate`. `rw [iterate_succ_apply' f (k+1), iterate_succ_apply' f k]`
rewrote inside the right-hand side as well as the left, leaving the induction
hypothesis in the wrong shape; naming both equations and rewriting the hypothesis
too fixed it. And `rintro _ ⟨n, rfl⟩` left the goal as an unreduced lambda
application, so the induction was over the wrong form — extracting the induction
into a standalone `iterate_bot_le` avoided it entirely.

## Totals

Fifteen modules, 2228 lines, 116 theorems, 0 `sorry`, 0 warnings.
Numbered results **5 of 29** — Theorems 1, 6, 7 and Lemmas 4, 5. Prose claims
**11**. Definitions **7 of ≈13**.

§2 is complete apart from Theorem 3; §3.1 apart from §3.2's effective
presentations.

## Next, and a design question it raises

**Theorem 3**: `fix` is the unique *uniform* fixed-point operator. The paper's
definition quantifies over a class:

> A fixed point operator `F` is a class of continuous functions
> `F_D : (D → D) → D` such that, for each cpo `D` and continuous `f : D → D`,
> `F_D(f) = f(F_D(f))`.

An operator indexed by **all** cpos is not a function in Lean — it is a family
over a universe of types, so the statement needs a structure carrying a field for
every `CompletePartialOrder` type in a universe, and uniformity quantifies over
pairs of them with a strict continuous map between. That is a formalization
decision, not a proof step, and it is the first thing r0018 has to settle.
