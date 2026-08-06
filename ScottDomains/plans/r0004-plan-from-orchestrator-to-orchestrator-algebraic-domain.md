---
round: r0004
from: orchestrator
to: orchestrator
subject: algebraic-domain
date: 2026-0806-13:35
status: done
related:
  - reports/r0004-report-from-orchestrator-to-user-algebraic-domain.md
  - plans/r0003-plan-from-orchestrator-to-orchestrator-way-below.md
  - reports/r0003-report-from-orchestrator-to-user-way-below.md
  - docs/PaperInventory.md
---

# r0004 — Algebraic cpo, domain, bounded complete

The three definitions that sit directly on `≪` (r0003). Deliverable: one new
module, `ScottDomains/Domain.lean` — 3 definitions and 7 theorems, no `sorry`.

## The paper's text, read rather than paraphrased

`docs/PaperInventory.md` is a de-garbled paraphrase and is wrong on one point
that matters. `pdftotext` over `papers/Gunter Scott 1990.pdf` gives the two
definitions verbatim (p. 9 and §4):

> The cpo `D` is said to be **algebraic** if, for every `x ∈ D`, the set
> `M = {x' ∈ K(D) | x' ⊑ x}` is directed and `⨆M = x`. … If `D` is algebraic
> **and `K(D)` is countable**, then we will say that `D` is a **domain**.

> A poset `A` is said to be **bounded complete** if `A` has a least element and
> every bounded subset of `A` has a least upper bound.

Two consequences the inventory misses:

1. **Countability of the basis is part of *domain*.** The inventory's row reads
   "domain = algebraic cpo", dropping `K(D)` countable. The condition is not
   decorative: §3.2's effective presentation is a surjection `d : ℕ → K(D)`, and
   Thm 11 is stated for the ideal completion of a *countable* pre-order.
2. **Bounded complete is a separate predicate, and the paper composes them.**
   It writes "bounded complete domain" as a compound — Thm 7, Lem 10, Lem 13,
   Thm 14. So the Lean name `ScottDomain` must not denote the bare algebraic
   cpo, or the compound becomes "bounded complete `ScottDomain`". This round
   uses `Domain` for the paper's notion and `BoundedComplete` for the predicate;
   the literature's *Scott domain* is the conjunction `[Domain α] [BoundedComplete α]`,
   written as two instance arguments rather than given a third name.

## Design decisions, with the reason for each

1. **`IsAlgebraic` is a `Prop` class over `[CompletePartialOrder α]`, carrying
   both conjuncts.** Mathlib's nearest analogue, `IsCompactlyGenerated`
   (`CompactlyGenerated/Basic.lean:349`), is a `Prop` class over
   `[CompleteLattice α]` asserting `∃ s, (∀ x ∈ s, IsCompactElement x) ∧ sSup s = x`.
   That shape does not transfer: in a dcpo `sSup` is constrained only on directed
   sets, so directedness of the approximant set must be asserted, not inferred.
   The paper asserts it explicitly, and so does the class.

2. **`compactsBelow` is a named definition, not an inline set-builder.** It
   appears in both conjuncts of `IsAlgebraic`, in `Domain`'s countability
   condition, and in every proof that uses algebraicity. One name, one set of
   lemmas.

3. **`⊥` is compact, and that is r0003's dividend, not a new proof.**
   `bot_wayBelow ⊥ : ⊥ ≪ ⊥`, and `wayBelow_self_iff_isCompactElement` turns it
   into `IsCompactElement ⊥` — a rewrite along an `Iff.rfl`. It is what makes
   `compactsBelow x` nonempty, which `IsLUB` needs to be usable and which the
   paper leaves implicit.

4. **`BoundedComplete` ties the condition to the ambient `sSup`.** The class
   asserts `∀ s, BddAbove s → IsLUB s (sSup s)`, following
   `ConditionallyCompletePartialOrderSup.isLUB_csSup_of_directed`
   (`ConditionallyCompletePartialOrder/Defs.lean`). The alternative, an
   existential `∀ s, BddAbove s → ∃ u, IsLUB s u`, is faithful to the English but
   yields no usable operation downstream. The paper's "has a least element" is
   already discharged: `CompletePartialOrder extends OrderBot`.

5. **The countability condition is `Set.Countable (compacts α)`, not a chosen
   enumeration.** An enumeration is §3.2's *effective presentation*, a later and
   stronger notion; conflating them here would force every domain to carry data
   it does not need.

## Steps, each with its verification

| # | Step | Verify |
| -- | ---- | ------ |
| 1 | `def compacts` and `def compactsBelow` at `[PartialOrder α]` | elaborates |
| 2 | `theorem isCompactElement_bot [OrderBot α] : IsCompactElement (⊥ : α)` | via `bot_wayBelow` and the r0003 bridge; no new induction |
| 3 | `theorem compactsBelow_nonempty [OrderBot α] (x : α) : (compactsBelow x).Nonempty` | `⊥ ∈ compactsBelow x` from step 2 and `bot_le` |
| 4 | `class IsAlgebraic [CompletePartialOrder α] : Prop` — `directedOn_compactsBelow`, `isLUB_compactsBelow` | elaborates |
| 5 | `class Domain [CompletePartialOrder α] extends IsAlgebraic α : Prop` — `countable_compacts` | elaborates; `Domain → IsAlgebraic` instance is automatic |
| 6 | `theorem sSup_compactsBelow [IsAlgebraic α] (x : α) : sSup (compactsBelow x) = x` | `IsLUB.unique` against `DirectedOn.isLUB_sSup` |
| 7 | `theorem wayBelow_iff_exists_compact [IsAlgebraic α] : x ≪ y ↔ ∃ k, IsCompactElement k ∧ x ≤ k ∧ k ≤ y` | ⇐ uses only r0003 (`trans_wayBelow`, `trans_le`, the bridge) and needs no algebraicity; ⇒ applies `x ≪ y` to `compactsBelow y`, whose LUB is `y` |
| 8 | `class BoundedComplete [CompletePartialOrder α] : Prop` — `isLUB_sSup_of_bddAbove` | elaborates |
| 9 | `theorem isLUB_sSup_pair [BoundedComplete α] (h : BddAbove {x, y}) : IsLUB {x, y} (sSup {x, y})` | the binary case the later results use |
| 10 | `theorem exists_isLUB_of_bddAbove [BoundedComplete α]` | the existential form, for readers checking the class against the paper's English |
| 11 | `lake build` | 0 errors, 0 warnings, 0 `sorry`; `#print axioms` on every new declaration |
| 12 | Update `docs/PaperInventory.md` §3.1 rows and counts; `INDEX.md` | 3 definitions move `✗ → ✓`; the *domain* row gains the countability condition |

Steps 6, 7 depend on 4; 9, 10 on 8; 3 on 2. Nothing else is ordered, so span is
3 sequential elaborations over 10 declarations.

## Acceptance criteria

| # | Criterion | Measurement |
| -- | --------- | ----------- |
| 1 | The module builds | `lake build` exits 0, 0 errors, 0 warnings. Job count is not an acceptance measure — r0003 showed it counts import closure, not work |
| 2 | Nothing asserted unproved | `grep -c sorry` = 0; `#print axioms` shows no `sorryAx` on any of the 10 declarations |
| 3 | Step 7 ⇐ uses no algebraicity | the reverse direction is proved before the `[IsAlgebraic α]` section opens, from r0003's API alone |
| 4 | The paper's definitions are the ones formalized | `Domain` carries countability; `BoundedComplete` is separate; both cited to the extracted text above |
| 5 | Mathlib unchanged | no edit under `.lake/` |

## Explicitly out of scope

Every numbered result: Thm 7 (`D → E` bounded complete), Lem 10, Lem 13, Thm 14,
and the §3.1 results on projections and normal substructures (Lem 4, Lem 5,
Thm 6). This round delivers the three definitions those results quantify over.
Also out of scope: effective presentation (§3.2), which needs an enumeration
rather than mere countability.

After this round: **≈9 definitions and 28 results** remain of the inventory's
≈13 and 28.

## Open question, deferred to the report

Whether `IsAlgebraic` should also be stated for `OmegaCompletePartialOrder`
(chains rather than directed sets). The paper is directed throughout, so the
dcpo form is the faithful one; the ω-form matters only if the development later
needs Mathlib's `LawfulFix`/`ContinuousHom` machinery, which is ω-based.
