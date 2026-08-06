---
round: r0005
from: orchestrator
to: user
subject: powerset-domain
date: 2026-0806-13:57
started: 2026-0806-13:53
finished: 2026-0806-13:57
related:
  - plans/r0005-plan-from-orchestrator-to-orchestrator-powerset-domain.md
  - plans/r0006-plan-from-orchestrator-to-orchestrator-function-space.md
---

# r0005 — `P N` as a domain: result

`ScottDomains/Powerset.lean`: 110 lines, 2 theorems, 3 instances, 4 examples,
0 `sorry`, 0 warnings. All four acceptance criteria met. Elapsed 4 minutes.

| # | Criterion | Measurement |
| -- | --------- | ----------- |
| 1 | Builds | `lake build` exits 0, 0 errors, 0 warnings, 1.2 s |
| 2 | Nothing unproved | `grep -c sorry` = 0; no `sorryAx` in any `#print axioms` |
| 3 | The example is the paper's | `example : Domain (Set ℕ) := inferInstance` typechecks — `P N` falls out of instance resolution, with no bespoke construction |
| 4 | The witness is nondegenerate | `{0}` is compact, `Set.univ` is not; both proved in the file |

## The theorem

`isCompactElement_iff_finite {s : Set X} : IsCompactElement s ↔ s.Finite` — the
paper's "whose compact elements are just the finite subsets of `N`", stated for
an arbitrary `Set X` because nothing in it needs `ℕ`.

The forward direction applies compactness to the directed set of finite subsets
of `s`, which has `s` as its least upper bound; compactness returns a finite `t`
with `s ⊆ t ⊆ s`. The reverse is an induction on `s.Finite`: the base case takes
any member of the nonempty directed set, and the insert case merges the induction
hypothesis's witness for `s'` with the witness for the new point, using
directedness of `d`. Turning `IsLUB d u` into `u = ⋃₀ d` is where
`Set.sSup_eq_sUnion` and `IsLUB.unique` come in.

`IsAlgebraic (Set X)` then holds for every `X`, `BoundedComplete (Set X)` holds
because a powerset is a complete lattice (a stronger reason than the definition
asks for — *every* subset has a supremum, not only the bounded ones), and
`Domain (Set X)` holds for countable `X` via `Set.Countable.setOf_finite`.

## Why the round was worth spending before any numbered result

After r0004 the three classes had exactly one witness, `Prop`, in which every
element is compact. That makes the directedness conjunct of `IsAlgebraic`
trivially true, so `Prop` could not have detected an error in it. `Set X` can:
its basis is the finite subsets, directedness is `∪`, and the file proves the
basis is a proper part of the order —

```
example : IsCompactElement ({0} : Set ℕ)
example : ¬ IsCompactElement (Set.univ : Set ℕ)
```

Both went through against the r0004 definitions unchanged. That is the evidence
that the class shapes are right, and it is what the `Prop` witness could not
supply.

## Axioms

Every declaration in this file depends on `propext`, `Classical.choice`, and
`Quot.sound`. This was predicted in the plan and is not a defect: `Set.Finite` is
classical in Mathlib, as is `Set.Countable.setOf_finite`. The constructive core
remains `WayBelow.lean` and the first two sections of `Domain.lean`.

## Two elaboration failures

**`Set.Finite.induction_on` takes the set as a major premise.** Its signature
(`Data/Set/Finite/Basic.lean:716`) is
`{motive : ∀ s : Set α, s.Finite → Prop} (s : Set α) (hs : s.Finite)`, so the
tactic form is `induction s, hs using Set.Finite.induction_on` — inducting on
`hs` alone fails with a sort mismatch, since `hs : s.Finite` is a `Prop` where a
`Set` was expected.

**The subset hypothesis had to be reverted.** `hsu : s ⊆ ⋃₀ d` mentions the very
`s` being inducted on, so it must move into the motive with `revert hsu` before
the induction; otherwise the induction hypothesis is about the wrong statement.
This is the usual generalization step, and the error message for skipping it is
not obvious.

## Effect on the work list

No numbered result and no inventory definition changes state — the counts stay at
**9 definitions and 28 results remaining**. What changed is confidence in the four
definitions already written. `docs/PaperInventory.md` and `INDEX.md` record the
example.

The paper names a second example on the same page: the compact elements of
`N⊥ → N⊥` are the functions with finite domain of definition. That one needs the
continuous function space, which is r0006.
