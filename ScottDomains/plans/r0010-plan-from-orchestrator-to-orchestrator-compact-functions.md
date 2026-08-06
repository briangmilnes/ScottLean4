---
round: r0010
from: orchestrator
to: orchestrator
subject: compact-functions
date: 2026-0806-14:24
status: done
related:
  - plans/r0009-plan-from-orchestrator-to-orchestrator-function-space-algebraic.md
  - reports/r0009-report-from-orchestrator-to-user-function-space-algebraic.md
---

# r0010 — Every compact function is a finite join of step functions

The structure theorem that Theorem 7's remaining conjunct rests on. Countability
of `K(D → E)` follows from it because a finite join is named by a finite subset
of `K(D) × K(E)`, and finite subsets of a countable set are countable
(`Set.countable_setOf_finite_subset`, already used in r0005).

Deliverable: `ScottDomains/CompactFunction.lean`.

## The argument

Let `stepsBelow f` be the step functions with compact value lying below `f`, and
`finiteJoinsBelow f` the elements that are a least upper bound of some **finite**
subset of `stepsBelow f`.

1. Every member of `finiteJoinsBelow f` is `≤ f`, since `f` bounds the finite set
   it is the least upper bound of.
2. `finiteJoinsBelow f` is **nonempty**: `⊥` is the least upper bound of `∅`.
3. `finiteJoinsBelow f` is **directed**: for joins of `S₁` and `S₂`, the union is
   finite and bounded by `f`, so `sSup (S₁ ∪ S₂)` exists by r0007's
   `BoundedComplete (ScottHom α β)` and dominates both.
4. `IsLUB (finiteJoinsBelow f) f`: this is r0009's argument with singletons —
   each `step k e` below `f` is the join of the finite set `{step k e}`, so it
   lies in `finiteJoinsBelow f`, and r0009 shows those alone already force
   `f ≤ u` for any upper bound `u`.
5. **Therefore** if `g` is compact, applying compactness to `finiteJoinsBelow g`
   — nonempty by 2, directed by 3, with least upper bound `g` by 4 — yields
   `J ∈ finiteJoinsBelow g` with `g ≤ J`; and `J ≤ g` by 1, so `g = J`.

Note what step 5 does **not** need: that a finite join of compacts is compact.
That would require an induction over the finite set using
`isCompactElement_of_isLUB_pair`; the argument above avoids it, because `J` is
already known to equal `g`.

## Steps

| # | Step | Verify |
| -- | ---- | ------ |
| 1 | `def stepsBelow`, `def finiteJoinsBelow` | elaborate |
| 2 | `le_of_mem_finiteJoinsBelow` | `IsLUB.2` against `f` as upper bound |
| 3 | `bot_mem_finiteJoinsBelow` | `isLUB_empty`, `Set.finite_empty` |
| 4 | `directedOn_finiteJoinsBelow` | union of the two finite sets; `isLUB_sSup_of_bddAbove` |
| 5 | `isLUB_finiteJoinsBelow` | r0009's script with `{step k e}` as the finite set |
| 6 | `exists_finite_isLUB_of_isCompactElement` — the structure theorem | steps 2–5 and antisymmetry |
| 7 | `lake build`; `#print axioms` | 0 errors, 0 warnings, 0 `sorry` |
| 8 | Docs, INDEX, PDF | recorded |

## Acceptance criteria

| # | Criterion | Measurement |
| -- | --------- | ----------- |
| 1 | Builds | 0 errors, 0 warnings |
| 2 | Nothing unproved | 0 `sorry`, no `sorryAx` |
| 3 | The theorem is stated as the paper needs it | for compact `g`, a *finite* `S ⊆ stepsBelow g` with `IsLUB S g` |
| 4 | No unnecessary induction | step 6 does not prove that finite joins of compacts are compact |

## Out of scope

Countability of `K(D → E)` and Theorem 7 itself: r0011. The remaining work there
is the injection of `K(D → E)` into the finite subsets of `K(D) × K(E)` and the
countability plumbing, not further order theory.
