import ScottDomains.EquilogicalSpaces.Basic
import Mathlib.Topology.Order.ScottTopology

/-!
# Definition 3.4 and Theorem 3.5: the Σ-topology

A. Bauer, L. Birkedal and D. S. Scott, *Equilogical Spaces*, TCS **315**(1):35–59,
2004, §3, `ScottDomains/papers/Bauer Birkedal Scott 2004 Equilogical Spaces.pdf`.

> **Definition 3.4** Let `ℒ` be a complete lattice. The **Σ-topology** on the
> lattice is defined as the collection of all upward closed subsets `U ⊆ |ℒ|`
> such that whenever `S ⊆ |ℒ|` and `⋁ S ∈ U`, then `⋁ S₀ ∈ U` for some finite
> subset `S₀ ⊆ S`.

> **Theorem 3.5** Given a complete lattice `ℒ`, the structure `⟨|ℒ|, Σ_ℒ⟩` is a
> `T₀`-space whose specialization ordering is exactly `≤_ℒ`.

Theorem 3.5 is what makes an algebraic lattice an *object* of `Equ` at all: the
objects of `Equ` are `T₀`-spaces, so without it Definition 3.11's `PEqu` has
nothing to be a category of. It is the first link in the chain
3.5 → 3.6 → 3.7 → 3.12 → 3.13 by which the paper reaches cartesian closure.

## One encoding gap, stated rather than hidden

Mathlib's Scott topology (`Topology.IsScott α Set.univ`) is defined as the join
of the upper-set topology with the Scott–Hausdorff topology, which unfolds to
"upper, and inaccessible by suprema of **directed** sets". Definition 3.4 instead
quantifies over **arbitrary** subsets `S` and asks for a **finite** `S₀ ⊆ S`.

On a complete lattice the two agree — the finite suprema of an arbitrary `S` form
a directed set with the same supremum — but that identification is a real step,
not a definitional unfolding. It is written out below as `IsSigmaOpen` together
with `sigmaOpen_iff_isOpen`, which is **an obligation carrying `sorry`**.
Everything proved in this file is proved for Mathlib's Scott topology; the
bridge to Definition 3.4's literal wording is the outstanding piece.
-/

universe u

namespace ScottDomains.EquilogicalSpaces

open Set Topology

/-! ## Definition 3.4, verbatim -/

/-- **Definition 3.4**: `U` is Σ-open when it is upward closed and, whenever the
    supremum of a set `S` lies in `U`, already the supremum of some *finite*
    subset of `S` does.

    Transcribed with the paper's arbitrary `S` and finite `S₀`, not silently
    replaced by the directed-set formulation Mathlib uses. -/
def IsSigmaOpen {L : Type u} [CompleteLattice L] (U : Set L) : Prop :=
  IsUpperSet U ∧ ∀ S : Set L, sSup S ∈ U → ∃ S₀ ⊆ S, S₀.Finite ∧ sSup S₀ ∈ U

/-- Definition 3.4 and Mathlib's Scott topology agree on a complete lattice.

    Obligation. The forward direction is immediate; the reverse needs that the
    finite suprema of an arbitrary `S` form a directed set whose supremum is
    `⋁ S`, which is where completeness is spent. Until this is discharged, the
    results below are theorems about `Topology.IsScott`, and only this lemma ties
    them to the paper's literal Definition 3.4. -/
theorem sigmaOpen_iff_isOpen {L : Type u} [CompleteLattice L] [TopologicalSpace L]
    [IsScott L univ] (U : Set L) : IsSigmaOpen U ↔ IsOpen U := by
  sorry

/-! ## Theorem 3.5 -/

section Theorem35

variable {L : Type u} [CompleteLattice L] [TopologicalSpace L] [IsScott L univ]

/-- **Theorem 3.5**, first half: the Σ-topology on a complete lattice is `T₀`.

    Proved, and proved by *citation*: Mathlib already establishes that the Scott
    topology on a partial order is `T₀` (`Topology.IsScott.instT0Space`, which
    goes through `IsScott.closure_singleton : closure {a} = Iic a` and injectivity
    of `a ↦ Iic a`). A complete lattice is a partial order, so the instance
    applies with nothing added. Restated here under the paper's number so the
    dependency is visible rather than implicit. -/
theorem bauerBirkedalScott04_theorem_3_5_t0 : T0Space L := inferInstance

/-- **Theorem 3.5**, second half: the specialization ordering of the Σ-topology
    is exactly `≤_ℒ`.

    The left-hand side is Definition 3.3 written out — `𝒯(x) ⊆ 𝒯(y)`, i.e. every
    open set containing `x` contains `y`. Note the direction: this is the paper's
    convention, which is the *opposite* of Mathlib's `x ⤳ y`.

    Both directions are one step. Forward: instantiate at the open set
    `(Iic y)ᶜ`, which is open because `Iic y` is closed in the Scott topology
    (`ClosedIicTopology`), and `y ∉ (Iic y)ᶜ` forces `x ≤ y`. Backward: Scott
    opens are upper sets (`IsScott.isUpperSet_of_isOpen`), which is precisely the
    implication wanted. -/
theorem bauerBirkedalScott04_theorem_3_5_specialization (x y : L) :
    (∀ s : Set L, IsOpen s → x ∈ s → y ∈ s) ↔ x ≤ y := by
  constructor
  · intro h
    by_contra hxy
    exact absurd (h (Iic y)ᶜ isClosed_Iic.isOpen_compl hxy) (by simp)
  · intro hxy s hs hx
    exact (IsScott.isUpperSet_of_isOpen (D := univ) hs) hxy hx

end Theorem35

/-! ## The payoff: a complete lattice is an object of `Equ` -/

/-- Any complete lattice under its Σ-topology, paired with an equivalence
    relation, is an equilogical space.

    This is what Theorem 3.5 is *for*: objects of `Equ` must be `T₀`, and
    `bauerBirkedalScott04_theorem_3_5_t0` is exactly that hypothesis. The
    `t0Space` field below is filled by instance resolution from Mathlib's
    `IsScott.instT0Space` — no `sorry`, and no appeal to the outstanding
    `sigmaOpen_iff_isOpen`, since nothing here needs Definition 3.4's wording.

    Definition 3.11's `PEqu` will restrict the lattices to the *algebraic* ones
    and weaken the relation to a partial equivalence relation; this constructor
    is the total, unrestricted case. -/
def EquilogicalSpace.ofScottLattice (L : Type u) [CompleteLattice L]
    [TopologicalSpace L] [IsScott L univ] (r : Setoid L) : EquilogicalSpace.{u} where
  carrier := L
  setoid := r

@[simp] theorem EquilogicalSpace.carrier_ofScottLattice (L : Type u) [CompleteLattice L]
    [TopologicalSpace L] [IsScott L univ] (r : Setoid L) :
    (EquilogicalSpace.ofScottLattice L r).carrier = L := rfl

end ScottDomains.EquilogicalSpaces
