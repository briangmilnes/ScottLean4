---
round: r0011
from: orchestrator
to: user
subject: countable-basis
date: 2026-0806-14:35
started: 2026-0806-14:32
finished: 2026-0806-14:35
related:
  - plans/r0011-plan-from-orchestrator-to-orchestrator-countable-basis.md
  - reports/r0010-report-from-orchestrator-to-user-compact-functions.md
---

# r0011 — Theorem 7 is proved

**The first of the paper's 28 outstanding numbered results is formally verified.**

`ScottDomains/FunctionSpaceCountable.lean`: 142 lines, 3 definitions, 4 theorems,
1 instance, 0 `sorry`, 0 warnings. Elapsed 3 minutes.

| # | Criterion | Measurement |
| -- | --------- | ----------- |
| 1 | Builds | 0 errors, 0 warnings |
| 2 | Nothing unproved | 0 `sorry`, no `sorryAx` |
| 3 | Theorem 7 stated and proved | `ScottHom.isBoundedCompleteDomain_scottHom` |
| 4 | Applies to the paper's own example | `Domain (ScottHom (Set ℕ) (Set ℕ))` by `inferInstance` — and iterated, `(P N → P N) → P N` also resolves |

## Theorem 7

> If `D` and `E` are bounded complete domains, then `D → E` is also a bounded
> complete domain.

Assembled from six rounds: cpo (r0006), bounded complete (r0007), step functions
(r0008), algebraic (r0009), finite joins (r0010), countable basis (r0011).

Criterion 4 is the check that matters: Theorem 7 applied to `P N` gives that
`P N → P N` is a bounded complete domain, and applying it again gives the same
for `(P N → P N) → P N`. Both resolve by `inferInstance`, so the theorem composes
with itself and with r0005's example rather than being provable only in the
abstract.

## Proved under weaker hypotheses than the paper states

**Bounded completeness of `D` is never used.** Tracing where each hypothesis is
spent across the six rounds:

| # | Conjunct of the conclusion | Needs of `D` | Needs of `E` |
| -- | -------------------------- | ------------ | ------------ |
| 1 | `D → E` is a cpo | a preorder | cpo |
| 2 | `D → E` is bounded complete | a preorder | bounded complete |
| 3 | `D → E` is algebraic | algebraic | algebraic + bounded complete |
| 4 | `K(D → E)` countable | countable basis | countable basis |

So `D` need only be a **domain** — algebraic with a countable basis — while `E`
must be a bounded complete domain. The formalization states it that way, and the
inventory records the difference. This is the kind of thing the paper's block
hypotheses hide and a proof assistant makes visible: nothing forced the extra
assumption, so nothing carries it.

## Two design points that made countability work

**`IsStepPair` is stated through the coercion, not through `step`.**
`IsStepPair g (k, e)` says `k`, `e` are compact and `⇑g = stepFun k e` — a
proposition with no proof term inside it. That is what lets a *set of pairs* name
a *set of step functions*; the original `stepsBelow`, phrased with `step` and its
embedded compactness proof, could not be mapped over. `CompactFunction.lean` was
refactored onto it.

**Choosing one pair per step function is not cosmetic.** The set of *all* pairs
naming a given step function can be infinite — every compact `k` names the
constant-`⊥` function — so taking all of them would lose the finiteness that the
whole argument turns on. `stepPairOf` picks one, and `stepsOf_image_stepPairOf`
shows naming and reading back is the identity, using injectivity of the
coercion.

## Elaboration failures

Three, all mechanical. `rw` on a definition produced a recovered `sorry` rather
than an error message pointing at the cause — the informative signal was the
follow-on warning "this tactic is never executed". `Classical.epsilon` needed a
`Nonempty (α × β)` that `[PartialOrder α]` could not supply, resolved by
strengthening the section to `[CompletePartialOrder α]`, which every caller
already had. And `open Classical in` placed *between* a docstring and its
declaration is a parse error; it must precede the docstring.

The overlapping-instance linter also flagged `[IsAlgebraic α]` sitting alongside
`[Domain α]`, which implies it — the same class of diagnostic that caught the
instance diamond in r0004, and fixed the same way, by splitting the section.

## Totals

Eight modules, 1273 lines, 58 theorems, 18 definitions, 13 instances, 0 `sorry`,
0 warnings. Numbered results: **1 of 28**. Definitions: 4 of ≈13.

## Next

The remaining §3.1 results — Lemmas 4 and 5, Theorem 6 — need definitions that do
not yet exist: embedding–projection pairs, projections and finitary projections,
and normal subposets. That is a definitions round before it is a theorems round.
