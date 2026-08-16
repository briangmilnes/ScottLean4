import ScottDomains.EquilogicalSpaces.SigmaTopology

/-!
# Theorem 3.7: the Extension Theorem

> **Theorem 3.7 (The Extension Theorem)** If `𝒴` is a subspace of a topological
> space `𝒳`, and if `f : |𝒴| → 𝒫 A` is continuous, then the function `f` has a
> continuous extension to all the points of `𝒳`.

This is the second of the three facts of Scott's from 1970/71 that carry §3, and
it is what makes Theorem 3.12's restriction functor **full**.

## The construction

Powerset spaces are injective in `Top₀`, and the witness is explicit. For each
`a ∈ A` the set `mem a = { S | a ∈ S }` is Σ-open in `𝒫 A` — upward closed, and
of finite character because `{a}` is a finite witness. So `f ⁻¹' (mem a)` is open
in the subspace `𝒴`, hence of the form `V a ∩ 𝒴` for some open `V a ⊆ 𝒳`.
Setting

    g x = { a | x ∈ V a }

extends `f`, because for `y ∈ 𝒴` membership `y ∈ V a` is exactly `a ∈ f y`.

## Why continuity is the finite-character property

`g` is continuous because the Σ-open sets of `𝒫 A` are exactly those the paper
describes as "of finite character": `U` is Σ-open iff a set lies in `U` as soon
as one of its finite subsets does. Concretely, for Σ-open `U`,

    U = ⋃_{T ∈ U} { S | F T ⊆ S }

where `F T` is a finite subset of `T` already in `U` — the inclusion `⊇` is
upward closure, and `⊆` holds because `T` contains its own `F T`. Then

    g ⁻¹' { S | F ⊆ S } = ⋂_{a ∈ F} V a

is a *finite* intersection of opens. That is the whole argument, and the finite
subset `F T` comes from `sigmaOpen_iff_isOpen`, proved in `SigmaTopology.lean`:
Definition 3.4's literal wording, with its arbitrary `S` and finite `S₀`, is
exactly what is needed here. Mathlib's directed-set formulation would not have
handed it over.
-/

universe u

namespace ScottDomains.EquilogicalSpaces

open Set Topology

section Powerset

variable {A : Type u} [TopologicalSpace (Set A)] [IsScott (Set A) univ]

/-- The subbasic Σ-open set `{ S | a ∈ S }`. -/
def memSet (a : A) : Set (Set A) := { S | a ∈ S }

/-- Each `memSet a` is Σ-open: it is upward closed, and inaccessible by directed
    suprema because a point of a union of a directed family already lies in one
    member. -/
theorem isOpen_memSet (a : A) : IsOpen (memSet a) := by
  rw [IsScott.isOpen_iff_isUpperSet_and_dirSupInaccOn (D := univ), dirSupInaccOn_univ]
  refine ⟨fun S T hST haS => hST haS, ?_⟩
  rintro d hne hdir T hlub haT
  have hsup : sSup d = T := (isLUB_sSup d).unique hlub
  rw [Set.sSup_eq_sUnion] at hsup
  obtain ⟨S, hSd, haS⟩ := Set.mem_sUnion.mp (hsup ▸ haT)
  exact ⟨S, hSd, haS⟩

/-- **Finite character.** If `U` is Σ-open and `T ∈ U`, then some *finite* subset
    of `T` is already in `U`.

    This is Definition 3.4 read at the powerset lattice: writing `T` as the
    supremum of its singletons, `sigmaOpen_iff_isOpen` produces a finite
    subfamily whose supremum lies in `U`, and that supremum is a finite subset
    of `T`. -/
theorem exists_finite_subset_mem_of_isOpen {U : Set (Set A)} (hU : IsOpen U)
    {T : Set A} (hT : T ∈ U) : ∃ F ⊆ T, F.Finite ∧ F ∈ U := by
  obtain ⟨-, hfin⟩ := (sigmaOpen_iff_isOpen U).mpr hU
  have hsing : sSup ((fun a => ({a} : Set A)) '' T) = T := by
    rw [Set.sSup_eq_sUnion]
    ext b
    simp only [Set.mem_sUnion, Set.mem_image]
    constructor
    · rintro ⟨_, ⟨c, hc, rfl⟩, rfl⟩; exact hc
    · intro hb; exact ⟨{b}, ⟨b, hb, rfl⟩, rfl⟩
  obtain ⟨S₀, hS₀sub, hS₀fin, hS₀U⟩ := hfin _ (hsing ▸ hT)
  refine ⟨sSup S₀, ?_, ?_, hS₀U⟩
  · rw [Set.sSup_eq_sUnion]
    rintro b ⟨S, hS, hbS⟩
    obtain ⟨c, hc, rfl⟩ := hS₀sub hS
    rw [Set.mem_singleton_iff] at hbS
    exact hbS ▸ hc
  · rw [Set.sSup_eq_sUnion]
    refine hS₀fin.sUnion fun S hS => ?_
    obtain ⟨c, -, rfl⟩ := hS₀sub hS
    exact Set.finite_singleton c

end Powerset

/-! ## The Extension Theorem -/

section Extension

variable {X : Type u} [TopologicalSpace X] {A : Type u}
  [TopologicalSpace (Set A)] [IsScott (Set A) univ]

/-- **Theorem 3.7 (The Extension Theorem).** A continuous map into a powerset
    space, defined on a subspace, extends continuously to the whole space.

    The extension is `g x = { a | x ∈ V a }`, where `V a` is any open set of `X`
    cutting out `f ⁻¹' (memSet a)` on the subspace — supplied by
    `isOpen_induced_iff` and chosen with `Classical.choice`.

    The paper notes the result holds for every continuous retract of a powerset,
    i.e. for all the continuous lattices, but that the powerset case suffices for
    §3. Only the powerset case is proved here. -/
theorem bauerBirkedalScott04_theorem_3_7 (s : Set X) (f : s → Set A)
    (hf : Continuous f) :
    ∃ g : X → Set A, Continuous g ∧ ∀ y : s, g y = f y := by
  classical
  -- For each `a`, cut out the preimage of `memSet a` by an open set of `X`.
  have hpre : ∀ a : A, ∃ V : Set X, IsOpen V ∧ f ⁻¹' (memSet a) = Subtype.val ⁻¹' V := by
    intro a
    have : IsOpen (f ⁻¹' (memSet a)) := (isOpen_memSet a).preimage hf
    obtain ⟨V, hV, hVeq⟩ := isOpen_induced_iff.mp this
    exact ⟨V, hV, hVeq.symm⟩
  choose V hVopen hVeq using hpre
  refine ⟨fun x => { a | x ∈ V a }, ?_, ?_⟩
  · -- Continuity, via finite character.
    rw [continuous_def]
    intro U hU
    have key : (fun x => { a | x ∈ V a }) ⁻¹' U
        = ⋃₀ { W | ∃ F : Set A, F.Finite ∧ F ∈ U ∧ W = ⋂ a ∈ F, V a } := by
      ext x
      simp only [Set.mem_preimage, Set.mem_sUnion, Set.mem_setOf_eq]
      constructor
      · intro hx
        obtain ⟨F, hFsub, hFfin, hFU⟩ := exists_finite_subset_mem_of_isOpen hU hx
        exact ⟨⋂ a ∈ F, V a, ⟨F, hFfin, hFU, rfl⟩,
          Set.mem_iInter₂.mpr fun a ha => hFsub ha⟩
      · rintro ⟨W, ⟨F, -, hFU, rfl⟩, hxW⟩
        exact (IsScott.isUpperSet_of_isOpen (D := univ) hU)
          (fun a ha => Set.mem_iInter₂.mp hxW a ha) hFU
    rw [key]
    refine isOpen_sUnion ?_
    rintro W ⟨F, hFfin, -, rfl⟩
    exact hFfin.isOpen_biInter fun a _ => hVopen a
  · intro y
    ext a
    show (y : X) ∈ V a ↔ a ∈ f y
    constructor
    · intro h
      have hy : y ∈ Subtype.val ⁻¹' (V a) := h
      rw [← hVeq a] at hy
      exact hy
    · intro h
      have hy : y ∈ f ⁻¹' (memSet a) := h
      rw [hVeq a] at hy
      exact hy

end Extension

end ScottDomains.EquilogicalSpaces
