import ScottDomains.WayBelow
-- `Set.Countable`, for the countability of `K(D)` in the definition of a domain.
import Mathlib.Data.Set.Countable

/-!
# Algebraic cpos, domains, and bounded completeness

Gunter & Scott, *Semantic Domains* (Handbook of Theoretical Computer Science
Vol. B, 1990), §3.1 and §4, quoted from the source PDF rather than paraphrased:

> The cpo `D` is said to be **algebraic** if, for every `x ∈ D`, the set
> `M = {x' ∈ K(D) | x' ⊑ x}` is directed and `⨆M = x`. … If `D` is algebraic
> and `K(D)` is countable, then we will say that `D` is a **domain**.

> A poset `A` is said to be **bounded complete** if `A` has a least element and
> every bounded subset of `A` has a least upper bound.

Three points of fidelity, each of which the project's earlier paraphrase in
`docs/PaperInventory.md` lost:

* Countability of the basis `K(D)` is part of *domain*, not an afterthought:
  §3.2's effective presentation is a surjection `ℕ → K(D)`, and Theorem 11 is
  stated for the ideal completion of a *countable* pre-order.
* *Bounded complete* is a separate predicate. The paper composes the two and
  says "bounded complete domain" (Theorem 7, Lemmas 10 and 13, Theorem 14),
  which is what the literature calls a *Scott domain*. Here that is the pair of
  instance arguments `[Domain α] [BoundedComplete α]`; no third name is
  introduced for it.
* "Has a least element" is already discharged by Mathlib:
  `CompletePartialOrder extends OrderBot`.

## Design

`IsAlgebraic` carries both conjuncts — directedness of the approximants *and*
the least upper bound. Mathlib's nearest analogue, `IsCompactlyGenerated`, gets
away with `sSup s = x` alone because it lives over a `CompleteLattice`, where
`sSup` is total. In a dcpo `sSup` is pinned down only on directed sets, so
directedness has to be asserted rather than inferred.

`BoundedComplete` states the condition against the ambient `sSup`, following
`ConditionallyCompletePartialOrderSup.isLUB_csSup_of_directed`. The existential
form is recovered as `exists_isLUB_of_bddAbove` for readers checking the class
against the paper's English.
-/

namespace ScottDomains

variable {α : Type*}

section PartialOrder

variable [PartialOrder α]

/-- `K(D)`, the set of compact elements. -/
def compacts (α : Type*) [PartialOrder α] : Set α := {k | IsCompactElement k}

/-- `{x' ∈ K(D) | x' ⊑ x}`, the compact approximants of `x`. Algebraicity is the
statement that this set is directed with least upper bound `x`. -/
def compactsBelow (x : α) : Set α := {k | IsCompactElement k ∧ k ≤ x}

@[simp] theorem mem_compacts {k : α} : k ∈ compacts α ↔ IsCompactElement k := Iff.rfl

@[simp] theorem mem_compactsBelow {k x : α} :
    k ∈ compactsBelow x ↔ IsCompactElement k ∧ k ≤ x := Iff.rfl

/-- If a compact `k` sits between `x` and `y`, then `x ≪ y`. This direction of
`wayBelow_iff_exists_compact` needs no algebraicity — only the r0003 API and the
fact that a compact element is way below itself. -/
theorem wayBelow_of_isCompactElement {x k y : α} (hk : IsCompactElement k)
    (hxk : x ≤ k) (hky : k ≤ y) : x ≪ y :=
  LE.le.trans_wayBelow hxk
    (WayBelow.trans_le ((wayBelow_self_iff_isCompactElement k).mpr hk) hky)

/-- A least upper bound of two compact elements is compact. Stated for a bare
`[PartialOrder α]` with the least upper bound as a hypothesis, because that is
all the argument uses — no completeness, no bottom, and no lattice structure.

This is what makes `compactsBelow` directed in a bounded complete cpo, where such
a least upper bound exists for every bounded pair. -/
theorem isCompactElement_of_isLUB_pair {k₁ k₂ c : α} (h₁ : IsCompactElement k₁)
    (h₂ : IsCompactElement k₂) (hc : IsLUB ({k₁, k₂} : Set α) c) : IsCompactElement c := by
  intro s u hne hd hlub hcu
  obtain ⟨x₁, hx₁, h1x⟩ :=
    h₁ s u hne hd hlub ((hc.1 (Set.mem_insert _ _)).trans hcu)
  obtain ⟨x₂, hx₂, h2x⟩ :=
    h₂ s u hne hd hlub ((hc.1 (Set.mem_insert_of_mem _ rfl)).trans hcu)
  obtain ⟨y, hy, hxy₁, hxy₂⟩ := hd x₁ hx₁ x₂ hx₂
  refine ⟨y, hy, hc.2 ?_⟩
  rintro z (rfl | rfl)
  · exact h1x.trans hxy₁
  · exact h2x.trans hxy₂

variable [OrderBot α]

/-- `⊥` is compact. This is r0003's dividend rather than a new argument:
`bot_wayBelow` gives `⊥ ≪ ⊥`, and on the diagonal `≪` *is* `IsCompactElement`. -/
theorem isCompactElement_bot : IsCompactElement (⊥ : α) :=
  (wayBelow_self_iff_isCompactElement ⊥).mp (bot_wayBelow ⊥)

theorem bot_mem_compactsBelow (x : α) : (⊥ : α) ∈ compactsBelow x :=
  ⟨isCompactElement_bot, bot_le⟩

/-- The compact approximants of any element form a nonempty set. The paper leaves
this implicit; `IsLUB` and `DirectedOn.isLUB_sSup` both need it. -/
theorem compactsBelow_nonempty (x : α) : (compactsBelow x).Nonempty :=
  ⟨⊥, bot_mem_compactsBelow x⟩

end PartialOrder

/-- An **algebraic** cpo: every element is the least upper bound of its directed
set of compact approximants. Gunter & Scott §3.1. -/
class IsAlgebraic (α : Type*) [CompletePartialOrder α] : Prop where
  /-- The compact approximants of each element are directed. -/
  directedOn_compactsBelow : ∀ x : α, DirectedOn (· ≤ ·) (compactsBelow x)
  /-- Each element is the least upper bound of its compact approximants. -/
  isLUB_compactsBelow : ∀ x : α, IsLUB (compactsBelow x) x

/-- A **domain** in the sense of Gunter & Scott: an algebraic cpo whose basis
`K(D)` is countable. The countability condition is part of the paper's
definition, and is what §3.2's effective presentations enumerate. -/
class Domain (α : Type*) [CompletePartialOrder α] : Prop extends IsAlgebraic α where
  /-- The set of compact elements is countable. -/
  countable_compacts : Set.Countable (compacts α)

section IsAlgebraic

variable [CompletePartialOrder α] [IsAlgebraic α]

/-- The `sSup` form of algebraicity. -/
theorem sSup_compactsBelow (x : α) : sSup (compactsBelow x) = x :=
  ((IsAlgebraic.directedOn_compactsBelow x).isLUB_sSup).unique
    (IsAlgebraic.isLUB_compactsBelow x)

/-- In an algebraic cpo, `≪` is exactly factorization through a compact element.
The forward direction is where algebraicity is spent: apply `x ≪ y` to the
directed set `compactsBelow y`, whose least upper bound is `y` itself. -/
theorem wayBelow_iff_exists_compact {x y : α} :
    x ≪ y ↔ ∃ k, IsCompactElement k ∧ x ≤ k ∧ k ≤ y := by
  constructor
  · intro h
    obtain ⟨k, hk, hxk⟩ := h (compactsBelow y) y (compactsBelow_nonempty y)
      (IsAlgebraic.directedOn_compactsBelow y) (IsAlgebraic.isLUB_compactsBelow y) le_rfl
    rw [mem_compactsBelow] at hk
    exact ⟨k, hk.1, hxk, hk.2⟩
  · rintro ⟨k, hk, hxk, hky⟩
    exact wayBelow_of_isCompactElement hk hxk hky

end IsAlgebraic

/-- **Bounded complete**: every subset with an upper bound has a least upper
bound. The paper's second requirement, a least element, is already carried by
`CompletePartialOrder`, which extends `OrderBot`. -/
class BoundedComplete (α : Type*) [CompletePartialOrder α] : Prop where
  /-- For each set `s` bounded above, `sSup s` is its least upper bound. -/
  isLUB_sSup_of_bddAbove : ∀ s : Set α, BddAbove s → IsLUB s (sSup s)

section BoundedComplete

variable [CompletePartialOrder α] [BoundedComplete α] {s : Set α}

theorem isLUB_sSup_of_bddAbove (h : BddAbove s) : IsLUB s (sSup s) :=
  BoundedComplete.isLUB_sSup_of_bddAbove s h

/-- The paper's English form of bounded completeness: every bounded subset *has*
a least upper bound. -/
theorem exists_isLUB_of_bddAbove (h : BddAbove s) : ∃ u, IsLUB s u :=
  ⟨sSup s, isLUB_sSup_of_bddAbove h⟩

end BoundedComplete

/-!
## A witness that the three classes are satisfiable

Three `Prop`-valued classes with no instance are unfalsifiable: an error in
either conjunct of `IsAlgebraic` would go undetected. `Prop` is the cheapest
witness — it is a `CompleteLattice`, hence a `CompletePartialOrder`, and every
one of its elements is compact.

`Prop` is a *degenerate* witness, so it tests satisfiability and not much else.
The paper's own first example, `P N` (`Set ℕ`, ordered by inclusion, with the
finite subsets as basis), is the nondegenerate check, and it costs a real proof
that the compact elements of a powerset are exactly the finite subsets.
-/

/-- A cpo in which every element is compact is algebraic: each `x` is itself the
greatest member of `compactsBelow x`, which makes the set trivially directed and
`x` its least upper bound. Covers flat cpos and finite lattices. -/
theorem isAlgebraic_of_forall_isCompactElement [CompletePartialOrder α]
    (h : ∀ x : α, IsCompactElement x) : IsAlgebraic α where
  directedOn_compactsBelow x _ hq _ hr := ⟨x, ⟨h x, le_rfl⟩, hq.2, hr.2⟩
  isLUB_compactsBelow x := ⟨fun _ hq => hq.2, fun _ hu => hu ⟨h x, le_rfl⟩⟩

/-- Every proposition is a compact element of `Prop`. If `p` holds, then the
proposition `∃ q ∈ s, q` is an upper bound of `s`, so the least upper bound
implies it, and that produces the required member of `s`. -/
theorem isCompactElement_prop (p : Prop) : IsCompactElement p := by
  intro s u hs _ hlub hpu
  by_cases hp : p
  · have hub : (∃ q, q ∈ s ∧ q) ∈ upperBounds s := fun q hq hqt => ⟨q, hq, hqt⟩
    obtain ⟨q, hqs, hqt⟩ := hlub.2 hub (hpu hp)
    exact ⟨q, hqs, fun _ => hqt⟩
  · obtain ⟨q, hqs⟩ := hs
    exact ⟨q, hqs, fun h => absurd h hp⟩

instance : Domain Prop where
  __ := isAlgebraic_of_forall_isCompactElement isCompactElement_prop
  countable_compacts := (compacts Prop).to_countable

instance : BoundedComplete Prop where
  isLUB_sSup_of_bddAbove s _ := isLUB_sSup s

end ScottDomains
