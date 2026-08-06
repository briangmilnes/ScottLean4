import ScottDomains.Domain
import Mathlib.Data.Set.Countable

/-!
# `P N`: the powerset as a domain

Gunter & Scott, *Semantic Domains*, p. 9:

> As another example, the collection `P N` of subsets of `N`, ordered by subset
> inclusion is a domain whose compact elements are just the finite subsets of `N`.

This file proves that characterization for an arbitrary `Set X`, and derives
`IsAlgebraic (Set X)`, `BoundedComplete (Set X)`, and — when `X` is countable —
`Domain (Set X)`. The paper's `P N` is then `Domain (Set ℕ)` by instance
resolution.

Mathlib proves the analogous statements for other lattices (`Submodule.fg_iff_compact`,
`Opens.isCompactElement_iff`) but not for `Set`.

## Why this example

After `Domain.lean` the three classes were witnessed only by `Prop`, in which
every element is compact, so the directedness conjunct of `IsAlgebraic` is
trivially satisfied there and an error in it would go undetected. `Set X` has a
nontrivial basis — the finite subsets — so it exercises that conjunct.
-/

namespace ScottDomains

variable {X : Type*}

/-- The compact elements of a powerset are exactly the finite subsets.

The forward direction applies compactness to the directed set of finite subsets
of `s`; the reverse is an induction on `s.Finite`, where directedness of `d`
merges the witness for `s'` with the witness for the newly inserted point. -/
theorem isCompactElement_iff_finite {s : Set X} : IsCompactElement s ↔ s.Finite := by
  constructor
  · intro hs
    obtain ⟨t, ht, hst⟩ :=
      hs {t | t ⊆ s ∧ t.Finite} s ⟨∅, Set.empty_subset s, Set.finite_empty⟩
        (fun a ha b hb => ⟨a ∪ b, ⟨Set.union_subset ha.1 hb.1, ha.2.union hb.2⟩,
          Set.subset_union_left, Set.subset_union_right⟩)
        ⟨fun _ ht => ht.1, fun u hu x hx => hu ⟨Set.singleton_subset_iff.mpr hx,
          Set.finite_singleton x⟩ rfl⟩
        le_rfl
    exact ht.2.subset hst
  · intro hs d u hd hdir hlub hsu
    have hu : u = ⋃₀ d := by
      rw [← Set.sSup_eq_sUnion]
      exact hlub.unique (isLUB_sSup d)
    subst hu
    revert hsu
    induction s, hs using Set.Finite.induction_on with
    | empty => exact fun _ => hd.imp fun t ht => ⟨ht, Set.empty_subset t⟩
    | @insert a s' _ _ ih =>
      intro hsu
      obtain ⟨t', ht', hs't'⟩ := ih fun x hx => hsu (Set.mem_insert_of_mem a hx)
      obtain ⟨t'', ht'', hat''⟩ := hsu (Set.mem_insert a s')
      obtain ⟨w, hw, ht'w, ht''w⟩ := hdir t' ht' t'' ht''
      exact ⟨w, hw, Set.insert_subset (ht''w hat'') (hs't'.trans ht'w)⟩

@[simp] theorem compacts_set_eq : compacts (Set X) = {s : Set X | s.Finite} :=
  Set.ext fun _ => isCompactElement_iff_finite

/-- `P X` is algebraic: every set is the directed union of its finite subsets.
Directedness is by `∪`, and the least upper bound holds because each `x ∈ s`
lies in the finite subset `{x} ⊆ s`. -/
instance : IsAlgebraic (Set X) where
  directedOn_compactsBelow _ a ha b hb :=
    ⟨a ∪ b, ⟨isCompactElement_iff_finite.mpr
        ((isCompactElement_iff_finite.mp ha.1).union (isCompactElement_iff_finite.mp hb.1)),
      Set.union_subset ha.2 hb.2⟩, Set.subset_union_left, Set.subset_union_right⟩
  isLUB_compactsBelow _ :=
    ⟨fun _ ht => ht.2, fun _ hu x hx =>
      hu ⟨isCompactElement_iff_finite.mpr (Set.finite_singleton x),
        Set.singleton_subset_iff.mpr hx⟩ rfl⟩

/-- `P X` is bounded complete, and for a reason stronger than the definition
asks: it is a complete lattice, so *every* subset has a least upper bound, not
only the bounded ones. -/
instance : BoundedComplete (Set X) where
  isLUB_sSup_of_bddAbove s _ := isLUB_sSup s

/-- `P X` is a domain when `X` is countable, since its basis is then the
countable set of finite subsets. The paper's `P N` is the case `X = ℕ`. -/
instance [Countable X] : Domain (Set X) where
  countable_compacts := by
    rw [compacts_set_eq]
    exact Set.Countable.setOf_finite

/-- `P N`, the paper's example, with no bespoke instance. -/
example : Domain (Set ℕ) := inferInstance

example : BoundedComplete (Set ℕ) := inferInstance

/-! ### The witness is nondegenerate

In `Prop` every element is compact, so it cannot distinguish a correct
`IsAlgebraic` from one whose directedness conjunct is wrong. In `P N` the compact
elements are a proper, nonempty, non-full part of the order: `{0}` is compact and
`univ` is not. -/

example : IsCompactElement ({0} : Set ℕ) :=
  isCompactElement_iff_finite.mpr (Set.finite_singleton 0)

example : ¬ IsCompactElement (Set.univ : Set ℕ) := fun h =>
  Set.infinite_univ (isCompactElement_iff_finite.mp h)

end ScottDomains
