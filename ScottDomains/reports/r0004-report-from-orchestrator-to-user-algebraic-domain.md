---
round: r0004
from: orchestrator
to: user
subject: algebraic-domain
date: 2026-0806-13:43
started: 2026-0806-13:33
finished: 2026-0806-13:43
related:
  - plans/r0004-plan-from-orchestrator-to-orchestrator-algebraic-domain.md
  - reports/r0003-report-from-orchestrator-to-user-way-below.md
  - docs/PaperInventory.md
---

# r0004 — Algebraic cpo, domain, bounded complete: result

`ScottDomains/Domain.lean` exists: 193 lines, 3 classes, 2 definitions,
10 theorems, 2 instances, 0 `sorry`. The kernel accepted all 19 declarations.
Elapsed 10 minutes.

| # | Criterion | Measurement |
| -- | --------- | ----------- |
| 1 | The module builds | `lake build` exits 0, 0 errors, 0 warnings, 1.2 s for this module |
| 2 | Nothing asserted unproved | `grep -c sorry` = 0; `#print axioms` on all 19 declarations shows no `sorryAx` |
| 3 | The ⇐ direction uses no algebraicity | `wayBelow_of_isCompactElement` is proved in the `[PartialOrder α]` section, before `IsAlgebraic` is declared. Its proof is one term built from three r0003 lemmas |
| 4 | The paper's definitions are the ones formalized | `Domain` carries countability; `BoundedComplete` is separate; both quoted from the extracted text in the module docstring |
| 5 | Mathlib unchanged | no edit under `.lake/` |

## Reading the paper instead of the paraphrase

The plan's first act was to run `pdftotext` over `papers/Gunter Scott 1990.pdf`
rather than trust `docs/PaperInventory.md`. That found two errors in the
inventory, one of them consequential.

**The inventory dropped a condition from the definition of *domain*.** The paper
(p. 9): "If `D` is algebraic **and `K(D)` is countable**, then we will say that
`D` is a domain." The inventory said "domain = algebraic cpo". The condition is
load-bearing later: §3.2's effective presentation is a surjection `ℕ → K(D)`, and
Theorem 11 concerns the ideal completion of a *countable* pre-order. Had r0004
formalized the paraphrase, both would have failed to typecheck against their own
statements several rounds from now, with the cause buried here.

**The name `ScottDomain` was reserved for the wrong notion.** The inventory
assigned it to the bare algebraic cpo. The paper defines *bounded complete* as a
separate predicate on posets and then writes the compound "bounded complete
domain" — Theorem 7, Lemmas 10 and 13, Theorem 14. Naming the bare notion
`ScottDomain` would render that compound as "bounded complete `ScottDomain`",
and the literature's *Scott domain* is precisely the compound. Resolved by using
`Domain` for the paper's notion, `BoundedComplete` for the predicate, and
writing the compound as the two instance arguments `[Domain α] [BoundedComplete α]`
rather than inventing a third name for it.

## What the file contains

| # | Declaration | Statement |
| -- | ----------- | --------- |
| 1 | `compacts α` | `K(D)`, the set of compact elements |
| 2 | `compactsBelow x` | `{x' ∈ K(D) | x' ⊑ x}` |
| 3 | `mem_compacts`, `mem_compactsBelow` | membership, by `Iff.rfl` |
| 4 | `wayBelow_of_isCompactElement` | compact `k` with `x ≤ k ≤ y` gives `x ≪ y` |
| 5 | `isCompactElement_bot` | `IsCompactElement (⊥ : α)` |
| 6 | `bot_mem_compactsBelow`, `compactsBelow_nonempty` | the approximants are nonempty |
| 7 | `IsAlgebraic` | class: `compactsBelow x` is directed with least upper bound `x` |
| 8 | `Domain` | class: `IsAlgebraic` + `Set.Countable (compacts α)` |
| 9 | `sSup_compactsBelow` | `sSup (compactsBelow x) = x` |
| 10 | `wayBelow_iff_exists_compact` | `x ≪ y ↔ ∃ k, IsCompactElement k ∧ x ≤ k ∧ k ≤ y` |
| 11 | `BoundedComplete` | class: `∀ s, BddAbove s → IsLUB s (sSup s)` |
| 12 | `isLUB_sSup_of_bddAbove`, `exists_isLUB_of_bddAbove` | accessors, the second in the paper's existential phrasing |
| 13 | `isAlgebraic_of_forall_isCompactElement` | a cpo whose elements are all compact is algebraic |
| 14 | `isCompactElement_prop` | every proposition is a compact element of `Prop` |
| 15 | `instance : Domain Prop`, `instance : BoundedComplete Prop` | satisfiability witnesses |

Declaration 5 is the one that pays r0003 back. `⊥` is compact *because*
`bot_wayBelow` gives `⊥ ≪ ⊥` and `wayBelow_self_iff_isCompactElement` is an
`Iff.rfl` — so the proof is a rewrite along a definitional identity, with no
induction and no directed-set argument. It is what makes `compactsBelow x`
nonempty, which the paper leaves implicit and which `IsLUB` needs.

Declaration 10 is the round's substantive theorem. The reverse direction needs no
algebraicity at all: it is `LE.le.trans_wayBelow` composed with `WayBelow.trans_le`
around the compact element's `k ≪ k`. Algebraicity is spent only in the forward
direction, by applying `x ≪ y` to the directed set `compactsBelow y`, whose least
upper bound is `y` itself. Splitting the two directions this way is what makes
criterion 3 checkable rather than a matter of opinion.

## Axioms

18 of 19 declarations are axiom-free or use `propext` alone. The exception is the
`Prop` witness: `isCompactElement_prop` and the `Domain Prop` instance depend on
`propext`, `Classical.choice`, and `Quot.sound`. The cause is `by_cases hp : p`
on an arbitrary proposition — that *is* excluded middle, and it is not removable:
to produce a member of `s` above `p` one must know whether `p` holds. The
development proper — everything in the first two sections of the file, and all of
`WayBelow.lean` — remains free of `Classical.choice`.

## Two deviations from the plan

**Added, not planned: the satisfiability witnesses (declarations 13–15).** Three
`Prop`-valued classes with no instance cannot be falsified — an error in either
conjunct of `IsAlgebraic` would have gone undetected by the build, by the axiom
check, and by review. `Prop` is the cheapest witness that closes that hole. It is
also a *degenerate* one: every element is compact, so it exercises the definition
weakly. The nondegenerate check is the paper's own first example, `P N`
(`Set ℕ` under inclusion, p. 9), and it costs a real proof that the compact
elements of a powerset are exactly the finite subsets. That is worth a round of
its own.

**Dropped, though planned: `isLUB_sSup_pair`.** Step 9 of the plan asked for the
two-element case of bounded completeness. Written out, it is
`isLUB_sSup_of_bddAbove` with `s := {x, y}` and nothing else — a specialization
that adds a name without adding content. Omitted rather than shipped.

## Three elaboration failures

**Unused section variable.** `wayBelow_of_isCompactElement` sat below
`variable [OrderBot α]` but does not use it; the `unusedSectionVars` linter
flagged it. Fixed by moving the theorem above that `variable` line rather than by
`omit` — placement is the real statement of what a theorem depends on.

**Structure-extends syntax moved.** `class Domain … extends IsAlgebraic α : Prop where`
is the old form; Lean 4.32 wants `class Domain … : Prop extends IsAlgebraic α`.
The warning names the reason: the new form leaves room for
`extends toP : P` to name parent projections.

**`Set.Countable` is not dot-notation-reachable through `Set α`.**
`(compacts α).Countable` failed with "the environment does not contain
`Function.Countable`" — `Set α` had already unfolded to `α → Prop`, so dot
notation looked in the wrong namespace. Written out as `Set.Countable (compacts α)`,
with `import Mathlib.Data.Set.Countable` added. This is the same failure mode as
r0003's second one: dot notation resolves against the head constant of the type
as elaborated, not as written.

## Inventory and index

`docs/PaperInventory.md`: the three §3.1 rows move `✗ → ✓`; the *domain* row now
carries the countability condition and notes it was missing; the
*bounded complete* row records that the paper composes the two predicates.
Counts: **9 definitions and 28 results remain** of ≈13 and 28, and the closing
tally goes from 43 to 40 remaining. `INDEX.md` lists the new module.

## Open, for the user

1. **Next target.** Two candidates. Lemmas 4 and 5 (§3.1) need
   embedding–projection pairs and finitary projections defined first. Theorem 7
   (`D → E` is a bounded complete domain) needs the continuous function space
   built as a cpo, which is the larger piece of infrastructure but is used by
   Lem 10, Lem 17, Thm 18, and Lem 23 as well. I would take the function space.
2. **`P N` as a nondegenerate witness.** A round proving that the compact
   elements of `Set X` are the finite subsets, giving `Domain (Set ℕ)` and
   `BoundedComplete (Set ℕ)` — the paper's own example, and a real test of the
   definitions.
3. **`Scott domain` as a name.** Currently the compound is written as two
   instance arguments. If you would rather have `class ScottDomain` for
   bounded-complete algebraic cpos, say so before Thm 7 is stated, since its
   signature is where the choice becomes visible.
