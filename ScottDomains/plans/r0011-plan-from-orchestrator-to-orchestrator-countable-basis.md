---
round: r0011
from: orchestrator
to: orchestrator
subject: countable-basis
date: 2026-0806-14:32
status: done
related:
  - plans/r0010-plan-from-orchestrator-to-orchestrator-compact-functions.md
  - reports/r0011-report-from-orchestrator-to-user-countable-basis.md
---

# r0011 — `K(D → E)` countable, and Theorem 7

The last conjunct. `Domain` carries the paper's countable-basis condition, so
Theorem 7 needs `K(D → E)` countable as well as algebraic.

Deliverable: `ScottDomains/FunctionSpaceCountable.lean`, and Theorem 7 as a
named result.

## The naming map

r0010 gives: a compact `g` is the least upper bound of a **finite** set `S` of
step functions below it. Each step function is named by a pair in `K(D) × K(E)`.
So `g` is named by a finite subset of a countable set, and those form a countable
family — `Set.countable_setOf_finite_subset`, the lemma `P N` already used.

Two design points make this go through:

1. **`IsStepPair` is stated through the coercion, not through `step`.**
   `IsStepPair g (k, e)` says `k` and `e` are compact and `⇑g = stepFun k e`. It
   carries no compactness proof inside a term, which is what lets a *set of
   pairs* name a *set of step functions*. `stepsBelow` in `CompactFunction.lean`
   is refactored onto it.

2. **`ofPairs` is total and `stepPairOf` chooses.** `ofPairs P` is the join of
   the step functions named by `P`, defined for every `P` because `sSup` on
   `ScottHom` is total; junk values are harmless since the argument needs only
   `K(D → E) ⊆ range ofPairs`. Choosing one pair per step function is not
   cosmetic: the set of *all* pairs naming a step function can be infinite —
   every `k` names the constant-`⊥` function — and finiteness would be lost.

## Steps

| # | Step | Verify |
| -- | ---- | ------ |
| 1 | Refactor `stepsBelow` onto a non-dependent `IsStepPair` | `CompactFunction.lean` still builds |
| 2 | `stepsOf`, `ofPairs`, `stepPairOf` | elaborate |
| 3 | `stepsOf_image_stepPairOf` — naming and reading back is the identity | injectivity of the coercion |
| 4 | `exists_ofPairs_of_isCompactElement` | r0010 plus `isLUB_sSup_of_bddAbove` |
| 5 | `countable_compacts_scottHom` | `Set.Countable.prod`, `Set.countable_setOf_finite_subset`, `Set.Countable.mono` |
| 6 | `instance : Domain (ScottHom α β)` | parent spliced from `IsAlgebraic` |
| 7 | `isBoundedCompleteDomain_scottHom` — **Theorem 7** | both instances |
| 8 | `lake build`, `#print axioms`, concrete instantiation | 0 errors, 0 warnings, 0 `sorry` |

## Acceptance criteria

| # | Criterion | Measurement |
| -- | --------- | ----------- |
| 1 | Builds | 0 errors, 0 warnings |
| 2 | Nothing unproved | 0 `sorry`, no `sorryAx` |
| 3 | Theorem 7 is stated and proved | `isBoundedCompleteDomain_scottHom` |
| 4 | It applies to the paper's own example | `Domain (ScottHom (Set ℕ) (Set ℕ))` by `inferInstance`, and iterated once more |
