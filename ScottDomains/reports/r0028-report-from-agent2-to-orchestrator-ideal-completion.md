---
round: r0028
from: agent2
to: orchestrator
subject: ideal-completion
date: 2026-0806-19:00
started: 2026-0806-18:47
finished: 2026-0806-19:00
related:
  - plans/r0028-plan-from-orchestrator-to-orchestrator-five-fold-parallel.md
---

# r0028 stream 2 — Theorem 11, the ideal completion

## Measurement

| # | Quantity | Value |
| -- | -------- | ----- |
| 1 | Final build line | `Build completed successfully (966 jobs).` |
| 2 | Errors | 0 |
| 3 | Warnings from `IdealCompletion.lean` | 0 |
| 4 | `sorry` in `IdealCompletion.lean` | **0** |
| 5 | `sorry` repo-wide | 1 — `Skeleton/Section6.lean:197`, `thm18`, agent4's, untouched |
| 6 | New file | `ScottDomains/IdealCompletion.lean`, 491 lines, 45 top-level declarations |
| 7 | Files changed outside it | none |

## What is proved and kernel-accepted

Both halves of Theorem 11, plus the cpo structure they rest on.

| # | Declaration | Statement |
| -- | ----------- | --------- |
| 1 | `IdealCompletion.instCompletePartialOrder` | `CompletePartialOrder (IdealCompletion A)` for `[Preorder A] [OrderBot A]` |
| 2 | `IdealCompletion.isCompactElement_iff_exists_eq_principal` | `IsCompactElement I ↔ ∃ a, I = principal a` |
| 3 | `IdealCompletion.compacts_eq_range_principal` | `compacts (IdealCompletion A) = Set.range principal` |
| 4 | `IdealCompletion.instIsAlgebraic` | `IsAlgebraic (IdealCompletion A)` |
| 5 | `IdealCompletion.instDomain` | `Domain (IdealCompletion A)` for `[Countable A]` |
| 6 | `IdealCompletion.thm11` | the paper's sentence: `Domain (IdealCompletion A) ∧ compacts (IdealCompletion A) = Set.range principal` |
| 7 | `IdealCompletion.orderIsoIdealCompletionCompacts` | `D ≃o IdealCompletion ↥(compacts D)` for `[IsAlgebraic D]` |
| 8 | `OrderIso.map_sSup_of_directedOn` | an `OrderIso` between cpos preserves directed suprema |
| 9 | `IdealCompletion.thm11_converse` | see below |

`#print axioms`, all nine:

    thm11                                    [propext, Classical.choice, Quot.sound]
    thm11_converse                           [propext, Classical.choice, Quot.sound]
    compacts_eq_range_principal              [propext, Classical.choice, Quot.sound]
    isCompactElement_iff_exists_eq_principal [propext, Classical.choice, Quot.sound]
    instCompletePartialOrder                 [propext, Classical.choice, Quot.sound]
    instIsAlgebraic                          [propext, Classical.choice, Quot.sound]
    instDomain                               [propext, Classical.choice, Quot.sound]
    orderIsoIdealCompletionCompacts          [propext, Quot.sound]
    OrderIso.map_sSup_of_directedOn          [propext, Quot.sound]

No `sorryAx`. `Classical.choice` enters at exactly one point — the `dite` in
`idealSup` branches on `Order.IsIdeal (⋃₀ …)`, which is not decidable. The
converse half uses none of it. The audit is transcribed into a trailing comment
in the file and the `#print axioms` commands removed, following
`Skeleton/Lemma10.lean`.

## The converse, stated precisely

    theorem thm11_converse (D : Type u) [CompletePartialOrder D] [Domain D] :
        ∃ e : D ≃o IdealCompletion ↥(compacts D),
          (∀ s : Set D, DirectedOn (· ≤ ·) s → e (sSup s) = sSup (e '' s)) ∧
            Domain (IdealCompletion ↥(compacts D))

"Isomorphic" is the three conjuncts, not a word:

1. **Order isomorphism** — `D ≃o IdealCompletion ↥(compacts D)`, i.e. an
   equivalence with `e a ≤ e b ↔ a ≤ b`. The map is `x ↦ {k ∈ K(D) | k ⊑ x}`
   (`idealOfElem`) with inverse `I ↦ ⨆ I` (`elemOfIdeal`); both round trips are
   proved (`elemOfIdeal_idealOfElem`, `idealOfElem_elemOfIdeal`).
2. **Cpo isomorphism** — the second conjunct says `e` commutes with `sSup` on
   every directed set, which is what an order isomorphism has to satisfy to be an
   isomorphism in the category of cpos and Scott-continuous maps. It is not extra
   hypothesis: `OrderIso.map_sSup_of_directedOn` derives it for any `OrderIso`
   between cpos, from `OrderIso.isLUB_image'` and `IsLUB.unique`. `e ⊥ = ⊥`
   follows from Mathlib's `OrderIso.map_bot` and is not restated.
3. **The codomain is again a `Domain`** — this is where `Domain D`'s countability
   half is spent, and only there: the order isomorphism itself needs only
   `[IsAlgebraic D]`.

## Mathlib reuse versus new construction

Reused from `Mathlib/Order/Ideal.lean` verbatim:

| # | Mathlib API | Use |
| -- | ----------- | --- |
| 1 | `Order.Ideal` | *is* the paper's definition — `LowerSet` + `nonempty'` + `directed'`. Not restated |
| 2 | its `SetLike` instance and `PartialOrder.ofSetLike` | membership, coercion, and inclusion order |
| 3 | `Order.Ideal.principal` | the paper's `↓x` |
| 4 | `Order.Ideal.bot_mem`, `Order.Ideal.lower/nonempty/directed/isIdeal` | the accessors |
| 5 | `Order.IsIdeal`, `Order.IsIdeal.toIdeal` | the set-level predicate the `sSup` branches on |
| 6 | `Order.isIdeal_sUnion_of_directedOn` | the whole first paragraph of the paper's proof — a directed union of ideals is an ideal |
| 7 | `IsCompactElement`, `Set.countable_range`, `Set.Countable.to_subtype`, `OrderIso.isLUB_image'` | elsewhere in Mathlib |

Built here, because Mathlib has none of it:

| # | New | Why Mathlib does not have it |
| -- | --- | --- |
| 1 | `SupSet` / `CompletePartialOrder (IdealCompletion A)` | Mathlib gives `Order.Ideal P` a `CompleteLattice` **only** when `P` is a `SemilatticeSup` with a bottom. Over a bare pre-order there is no order structure beyond the poset |
| 2 | the characterization of `K(IdealCompletion A)` | nothing in Mathlib identifies compact elements of an ideal poset |
| 3 | `IsAlgebraic`, `Domain` instances | those classes are this project's |
| 4 | the whole converse half | Mathlib has no ideal-completion/domain correspondence |
| 5 | `OrderIso.map_sSup_of_directedOn` | Mathlib has `OrderIso.map_sSup` for complete lattices only |

## Two design decisions worth the orchestrator's attention

**`IdealCompletion A` is a type synonym for `Order.Ideal A`, not `Order.Ideal A`
itself.** Declaring `instance : SupSet (Order.Ideal A)` at `[Preorder A]
[OrderBot A]` would collide with Mathlib's `CompleteLattice (Order.Ideal P)`
whenever `A` is a `SemilatticeSup` with a bottom — for instance `A = Set ℕ` — and
the two `sSup`s genuinely disagree: Mathlib's is the ideal *generated by* the
union, this one is the union itself (and `⊥` when that is not an ideal). Two
non-defeq `SupSet` instances on one type is a latent incoherence that would
surface as an unelaborable goal somewhere in §5, so the synonym keeps them apart.
The cost is about 20 lines transferring `SetLike`, `PartialOrder`, and the three
accessors; every set-level fact then works through Mathlib's `SetLike` API
unchanged.

**The `sSup` branches on `Order.IsIdeal (⋃₀ …)`, not on directedness of the
family.** This is the plan's §"defect that must not recur": the branch condition
is exactly the proposition the constructor consumes, which is what makes
`lubOfDirected` hold on the nose for the empty family too (`⋃₀ ∅ = ∅` is not an
ideal because it is empty, so `sSup ∅ = ⊥`, which is what
`CompletePartialOrder` demands of its `OrderBot`).

## Hypotheses the paper leaves implicit — none added silently

The paper's Theorem 11 hypothesis "*there is an element `⊥ ∈ A` such that `x ⊢ ⊥`
for each `x ∈ A`*" is `[OrderBot A]`: the same statement with the least element
named as data rather than asserted to exist. That is the only difference, and it
is stated in `thm11`'s docstring. The countability hypothesis is `[Countable A]`,
which is the paper's "countable pre-order" exactly. Nothing else was assumed.

One orientation point, recorded in the module docstring because it inverts every
formula: the paper writes `a ⊢ b` for "*`a` is larger than `b`*", so its `↓x =
{y | x ⊢ y}` is Mathlib's `Set.Iic x` and its `⊥` is Mathlib's `OrderBot`. All
statements here use Mathlib's orientation.

## Nondegeneracy

Three `example`s at the end of the file check that the basis is a proper part of
the order rather than everything, in the style `Powerset.lean` set: `Domain
(IdealCompletion ℕ)` resolves by instance search; `principal 3` is compact; and
`univIdealNat` — all of `ℕ`, directed by `max` — is not compact, because it is not
principal.

## `ScottDomains.lean` was not edited

The plan permits adding the import line, but `ScottDomains.lean` imports **zero**
project modules today (only six Mathlib modules) — none of the 27 existing
modules is listed there. The build reaches every module through the lakefile's
`globs = ["ScottDomains", "ScottDomains.+"]`, which is why `lake build` reports
966 jobs and builds `ScottDomains.IdealCompletion`. Adding one import line would
break that file's convention and make it a four-way merge conflict for this
round. Left alone; say the word and I will add it.

## Nothing unproved

No obstacle to report. Both halves of Theorem 11 are kernel-accepted. §5's
powerdomains are unblocked: `D♮`, `D♯`, `D♭` are `IdealCompletion` of
`Pf(K(D))` under `⊢♮`, `⊢♯`, `⊢♭`, and each needs only a `Preorder` and an
`OrderBot` instance on that pre-order to inherit `Domain` from `instDomain`.
