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

/-- A finite subset of a directed set has an upper bound **inside that set**.

    Proved here by induction on the finite subset because neither Mathlib nor
    this package carries it: searched `Mathlib/Order/Directed.lean`,
    `Mathlib/Order/Bounds/Basic.lean`, `ScottDomains/Domain.lean` and
    `ScottDomains/IdealCompletion.lean`. Mathlib's `Finset.exists_le` is the
    statement for a directed *order*, not for a directed *subset*, and it is the
    subset form that Definition 3.4 needs.

    The empty case is where `d.Nonempty` is spent, and it is why no separate
    `S.Nonempty` hypothesis is required downstream: for `S = ∅` any element of
    `d` serves. -/
theorem DirectedOn.exists_upperBound_of_finite {α : Type u} [Preorder α]
    {d : Set α} (hd : DirectedOn (· ≤ ·) d) (hdne : d.Nonempty)
    {S : Set α} (hS : S.Finite) : S ⊆ d → ∃ b ∈ d, ∀ x ∈ S, x ≤ b := by
  induction S, hS using Set.Finite.induction_on with
  | empty =>
      intro _
      obtain ⟨b, hb⟩ := hdne
      exact ⟨b, hb, by simp⟩
  | @insert a s ha hs ih =>
      intro hsub
      have had : a ∈ d := hsub (Set.mem_insert a s)
      obtain ⟨b, hbd, hb⟩ := ih fun x hx => hsub (Set.mem_insert_of_mem a hx)
      obtain ⟨c, hcd, hac, hbc⟩ := hd a had b hbd
      refine ⟨c, hcd, fun x hx => ?_⟩
      rcases Set.mem_insert_iff.mp hx with rfl | hxs
      · exact hac
      · exact le_trans (hb x hxs) hbc

/-- Definition 3.4 and Mathlib's Scott topology agree on a complete lattice.

    **Proved.** This is the lemma that ties every result in this file to the
    paper's literal wording rather than to Mathlib's directed-set formulation.

    Forward: given a directed `d` with `IsLUB d a` and `a ∈ U`, Definition 3.4
    applied to `d` yields a finite `S₀ ⊆ d` with `⋁ S₀ ∈ U`, and
    `DirectedOn.exists_upperBound_of_finite` promotes `⋁ S₀` to an actual member
    of `d` above it, which lies in `U` because `U` is upper.

    Backward: the set `d` of suprema of finite subsets of `S` is nonempty
    (take `∅`), directed (take unions), and has `⋁ S` as least upper bound —
    least because each singleton `{x}`, `x ∈ S`, is one of the finite subsets.
    Inaccessibility then meets `d` inside `U`, and any such member *is* the
    supremum of a finite subset of `S`. Completeness is spent exactly at
    `IsLUB d (sSup S)`. -/
theorem sigmaOpen_iff_isOpen {L : Type u} [CompleteLattice L] [TopologicalSpace L]
    [IsScott L univ] (U : Set L) : IsSigmaOpen U ↔ IsOpen U := by
  rw [IsScott.isOpen_iff_isUpperSet_and_dirSupInaccOn (D := univ), dirSupInaccOn_univ]
  constructor
  · rintro ⟨hup, hfin⟩
    refine ⟨hup, fun d hne hdir a hlub ha => ?_⟩
    have hsup : sSup d = a := (isLUB_sSup d).unique hlub
    obtain ⟨S₀, hS₀d, hS₀fin, hS₀U⟩ := hfin d (by rw [hsup]; exact ha)
    obtain ⟨b, hbd, hb⟩ :=
      DirectedOn.exists_upperBound_of_finite hdir hne hS₀fin hS₀d
    exact ⟨b, hbd, hup (sSup_le hb) hS₀U⟩
  · rintro ⟨hup, hinacc⟩
    refine ⟨hup, fun S hS => ?_⟩
    set d : Set L := { x | ∃ F, F ⊆ S ∧ F.Finite ∧ sSup F = x } with hd
    have hdne : d.Nonempty := ⟨sSup ∅, ∅, Set.empty_subset S, Set.finite_empty, rfl⟩
    have hdir : DirectedOn (· ≤ ·) d := by
      rintro _ ⟨F₁, hF₁S, hF₁fin, rfl⟩ _ ⟨F₂, hF₂S, hF₂fin, rfl⟩
      exact ⟨sSup (F₁ ∪ F₂), ⟨F₁ ∪ F₂, Set.union_subset hF₁S hF₂S, hF₁fin.union hF₂fin, rfl⟩,
        sSup_le_sSup Set.subset_union_left, sSup_le_sSup Set.subset_union_right⟩
    have hlub : IsLUB d (sSup S) := by
      constructor
      · rintro _ ⟨F, hFS, -, rfl⟩
        exact sSup_le_sSup hFS
      · intro c hc
        refine sSup_le fun x hx => ?_
        have : sSup {x} ≤ c := hc ⟨{x}, Set.singleton_subset_iff.mpr hx, Set.finite_singleton x, rfl⟩
        simpa using this
    obtain ⟨y, hyd, hyU⟩ := hinacc hdne hdir hlub hS
    obtain ⟨F, hFS, hFfin, rfl⟩ := hyd
    exact ⟨F, hFS, hFfin, hyU⟩

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
