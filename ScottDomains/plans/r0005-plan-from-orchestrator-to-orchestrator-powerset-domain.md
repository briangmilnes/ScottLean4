---
round: r0005
from: orchestrator
to: orchestrator
subject: powerset-domain
date: 2026-0806-13:52
status: done
related:
  - plans/r0004-plan-from-orchestrator-to-orchestrator-algebraic-domain.md
  - reports/r0004-report-from-orchestrator-to-user-algebraic-domain.md
---

# r0005 — `P N`: the powerset as a domain

The paper's own first example, and the nondegenerate test of r0004's three
classes. From p. 9:

> As another example, the collection `P N` of subsets of `N`, ordered by subset
> inclusion is a domain whose compact elements are just the finite subsets of `N`.

Deliverable: `ScottDomains/Powerset.lean` — the compactness characterization,
plus `IsAlgebraic (Set X)`, `BoundedComplete (Set X)`, and `Domain (Set X)` for
countable `X`, which gives `Domain (Set ℕ)` by instance resolution.

Why this before any numbered result: after r0004 the three classes are witnessed
only by `Prop`, in which every element is compact. That witness cannot detect an
error in the directedness conjunct of `IsAlgebraic`, because directedness is
trivial there. `Set X` has a nontrivial basis, so it can.

## What Mathlib supplies and what it does not (measured)

| # | Query | Result |
| -- | ----- | ------ |
| 1 | `IsCompactElement` for `Set X` / powersets | absent. The analogues exist elsewhere — `Submodule.fg_iff_compact` (`RingTheory/Finiteness/Basic.lean:194`), `Opens.isCompactElement_iff` (`Topology/Sets/Opens.lean:419`) — but not for `Set` |
| 2 | countability of the finite subsets | `Set.Countable.setOf_finite [Countable α] : {s : Set α \| s.Finite}.Countable` (`Data/Set/Countable.lean:283`). Exactly the countability condition of `Domain` |
| 3 | `CompleteLattice (Set X)` → `CompletePartialOrder (Set X)` | by instance resolution, as `Prop` was in r0004 |
| 4 | `sSup` on `Set X` | `Set.sSup_eq_sUnion` — needed to turn `IsLUB d u` into `u = ⋃₀ d` |

## Steps, each with its verification

| # | Step | Verify |
| -- | ---- | ------ |
| 1 | `theorem isCompactElement_iff_finite {s : Set X} : IsCompactElement s ↔ s.Finite` | see the two directions below |
| 2 | ⇐ of step 1 | induction on `s.Finite`. Base `∅`: any member of the nonempty directed set works. Step `insert a s'`: the induction hypothesis gives `t' ∈ d` with `s' ⊆ t'`; `a ∈ u = ⋃₀ d` gives `t'' ∈ d` with `a ∈ t''`; directedness merges them |
| 3 | ⇒ of step 1 | apply compactness to `d := {t \| t ⊆ s ∧ t.Finite}`, which is nonempty, directed under `∪`, and has `s` as least upper bound; it returns a finite `t` with `s ⊆ t ⊆ s` |
| 4 | `theorem compacts_eq_setOf_finite : compacts (Set X) = {s \| s.Finite}` | `Set.ext` on step 1 |
| 5 | `instance : IsAlgebraic (Set X)` | `compactsBelow s` = the finite subsets of `s`; directed by `∪`; least upper bound `s` because every `x ∈ s` lies in the finite subset `{x}` |
| 6 | `instance : BoundedComplete (Set X)` | `Set X` is a complete lattice, so `isLUB_sSup` discharges it for every `s`, bounded or not |
| 7 | `instance [Countable X] : Domain (Set X)` | step 4 rewrites the countability obligation into `Set.Countable.setOf_finite` |
| 8 | `example : Domain (Set ℕ) := inferInstance` | the paper's `P N`, obtained without a bespoke instance |
| 9 | `lake build`; `#print axioms` on every new declaration | 0 errors, 0 warnings, 0 `sorry` |
| 10 | Update `docs/PaperInventory.md` and `INDEX.md` | the `P N` example recorded as formalized |

Steps 2 and 3 are independent; 4 depends on 1; 5–7 on 4. Span is 3 sequential
elaborations.

## Design decisions

1. **State it for `Set X`, not `Set ℕ`.** Only the countability condition of
   `Domain` needs anything of `X`, and `[Countable X]` isolates it to step 7.
   `Set ℕ` then costs nothing (step 8). Proving the paper's example directly
   would discard a general result that comes free.

2. **Do not add `Set.isCompactElement_iff_finite` to the `Set` namespace.**
   The theorem belongs in `ScottDomains`; putting it in `Set` would claim
   namespace territory in a way an eventual Mathlib pull request should decide,
   not this file.

3. **Expect `Classical.choice` here, unlike r0003 and r0004.** `Set.Finite` and
   the countability lemma are classical in Mathlib. Report the axiom set rather
   than contorting the proofs to avoid it.

## Acceptance criteria

| # | Criterion | Measurement |
| -- | --------- | ----------- |
| 1 | Builds | `lake build` exits 0, 0 errors, 0 warnings |
| 2 | Nothing unproved | `grep -c sorry` = 0; no `sorryAx` in any `#print axioms` |
| 3 | The example is the paper's | `Domain (Set ℕ)` holds by instance resolution, with compacts characterized as the finite subsets |
| 4 | The witness is nondegenerate | `Set ℕ` has compact elements that are not the whole space and not `⊥`; unlike `Prop`, its directedness conjunct has content |

## Out of scope

Every numbered result. The other example the paper names on the same page —
the compact elements of `N⊥ → N⊥` being the finite-domain functions — needs the
function space, which is r0006.
