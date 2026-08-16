import ScottDomains.EquilogicalSpaces.ALat
import ScottDomains.Product

/-!
# The product of algebraic lattices is algebraic

The missing prerequisite for binary products in `ALat`. `ScottDomains.Product`
supplies `CompletePartialOrder (α × β)` but not `IsAlgebraic (α × β)`, so before
this module `A × B` could not even be an *object* of `ALat`, let alone a limit
cone.

## The shape of the argument

Algebraicity has two halves, and in the lattice setting they need different
amounts of work.

**Directedness of `compactsBelow (x, y)` is free.** For `p, q` compact and below
`(x, y)`, the join `p ⊔ q` exists, is below `(x, y)`, and is compact by the
package's `isCompactElement_of_isLUB_pair` — "a least upper bound of two compact
elements is compact", which is stated for a bare `PartialOrder` with the least
upper bound as a hypothesis. No product reasoning enters.

That is why this module is stated for **complete lattices** rather than for
arbitrary algebraic cpos. Over a general cpo the join need not exist, and
directedness would instead require the *projection* direction of compactness —
that `(a, b)` compact implies `a` and `b` compact — which needs a separate
argument through `(fun x => (x, b)) '' s`. Not needed for `ALat`, so not proved
here; noted in case the general case is ever wanted.

**The least-upper-bound half needs the pairing direction**,
`isCompactElement_prod`: a pair of compacts is compact. It is used with `⊥` in
one coordinate, to push an upper bound of `compactsBelow (x, y)` down to an upper
bound of `compactsBelow x` in the first factor.
-/

universe u

namespace ScottDomains.EquilogicalSpaces

open ScottDomains

section ProductAlgebraic

variable {α β : Type u} [CompleteLattice α] [CompleteLattice β]

/-- **A pair of compact elements is compact.**

    Given a directed `s ⊆ α × β` with least upper bound `u` and `(a, b) ≤ u`,
    compactness of `a` against the first-projection image produces `p₁ ∈ s` with
    `a ≤ p₁.1`, compactness of `b` against the second produces `p₂ ∈ s` with
    `b ≤ p₂.2`, and directedness of `s` merges them into a single `p₃ ∈ s` above
    both. The two coordinates are found in *different* members of `s`, which is
    exactly what directedness is for — the same move `Currying.lean` makes when
    it uncurries. -/
theorem isCompactElement_prod {a : α} {b : β}
    (ha : IsCompactElement a) (hb : IsCompactElement b) :
    IsCompactElement ((a, b) : α × β) := by
  intro s u hne hd hlub hle
  rw [isLUB_prod] at hlub
  obtain ⟨hfst, hsnd⟩ := hlub
  obtain ⟨_, ⟨p₁, hp₁, rfl⟩, hap₁⟩ :=
    ha (Prod.fst '' s) u.1 (hne.image _) (directedOn_fst_image hd) hfst hle.1
  obtain ⟨_, ⟨p₂, hp₂, rfl⟩, hbp₂⟩ :=
    hb (Prod.snd '' s) u.2 (hne.image _) (directedOn_snd_image hd) hsnd hle.2
  obtain ⟨p₃, hp₃, h₁₃, h₂₃⟩ := hd p₁ hp₁ p₂ hp₂
  exact ⟨p₃, hp₃, ⟨hap₁.trans h₁₃.1, hbp₂.trans h₂₃.2⟩⟩

/-- `(a, ⊥)` is compact whenever `a` is — the instance of `isCompactElement_prod`
    the least-upper-bound half uses to isolate the first factor. -/
theorem isCompactElement_prod_bot {a : α} (ha : IsCompactElement a) :
    IsCompactElement ((a, ⊥) : α × β) :=
  isCompactElement_prod ha isCompactElement_bot

/-- `(⊥, b)` is compact whenever `b` is. -/
theorem isCompactElement_bot_prod {b : β} (hb : IsCompactElement b) :
    IsCompactElement ((⊥, b) : α × β) :=
  isCompactElement_prod isCompactElement_bot hb

variable [ScottDomains.IsAlgebraic α] [ScottDomains.IsAlgebraic β]

/-- **The product of two algebraic lattices is algebraic.**

    Directedness: the join of two compacts below `(x, y)` is compact
    (`isCompactElement_of_isLUB_pair`) and still below `(x, y)`.

    Least upper bound: `(x, y)` bounds `compactsBelow (x, y)` by definition. For
    leastness, let `(u, v)` be any upper bound. Every `a ∈ compactsBelow x` gives
    a compact `(a, ⊥) ≤ (x, y)`, so `(a, ⊥) ≤ (u, v)` and hence `a ≤ u`; thus `u`
    bounds `compactsBelow x` and `x ≤ u` by algebraicity of `α`. Symmetrically
    `y ≤ v`. -/
instance isAlgebraic_prod : ScottDomains.IsAlgebraic (α × β) where
  directedOn_compactsBelow := by
    rintro ⟨x, y⟩ p ⟨hpc, hple⟩ q ⟨hqc, hqle⟩
    refine ⟨p ⊔ q, ⟨?_, sup_le hple hqle⟩, le_sup_left, le_sup_right⟩
    exact isCompactElement_of_isLUB_pair hpc hqc isLUB_pair
  isLUB_compactsBelow := by
    rintro ⟨x, y⟩
    constructor
    · rintro p ⟨-, hple⟩
      exact hple
    · rintro ⟨u, v⟩ huv
      refine ⟨?_, ?_⟩
      · refine (ScottDomains.IsAlgebraic.isLUB_compactsBelow x).2 ?_
        rintro a ⟨hac, hax⟩
        exact (huv ⟨isCompactElement_prod_bot hac, ⟨hax, bot_le⟩⟩).1
      · refine (ScottDomains.IsAlgebraic.isLUB_compactsBelow y).2 ?_
        rintro b ⟨hbc, hby⟩
        exact (huv ⟨isCompactElement_bot_prod hbc, ⟨bot_le, hby⟩⟩).2

end ProductAlgebraic

/-- The binary product of two objects of `ALat` is an object of `ALat`. The
    carrier is the product lattice; `isAlgebraic_prod` is what makes it an
    object at all. -/
def AlgebraicLattice.prod (A B : AlgebraicLattice.{u}) : AlgebraicLattice.{u} where
  carrier := A.carrier × B.carrier

end ScottDomains.EquilogicalSpaces
