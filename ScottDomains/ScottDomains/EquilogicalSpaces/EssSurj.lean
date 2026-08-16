import ScottDomains.EquilogicalSpaces.Restriction

/-!
# `R` is essentially surjective

The last of Theorem 3.12's four pieces.

> Finally, the functor `R` is essentially surjective on objects by virtue of The
> Embedding Theorem (and note that the equivalence relation on the `T₀`-space
> does not have to be extended but remains partial).

Given an equilogical space `ℰ`, the witness is the powerset `𝒫 (𝒫 |ℰ|)` under its
Σ-topology — an algebraic lattice by `ScottDomains.Powerset` — carrying the
*partial* equivalence relation transported along `nbhdFilter`:

    S ≈ T  ⟺  ∃ x y, x ≡_ℰ y ∧ S = 𝒯(x) ∧ T = 𝒯(y)

The parenthesis in the paper is the whole design: this relation is reflexive
exactly on `range nbhdFilter` and nowhere else, so it is genuinely partial, and
its total part is the image of the embedding — homeomorphic to `ℰ` by Theorem
3.6.

Transitivity is the only clause that needs an argument, and it is where `T₀` is
spent a second time: from `S ≈ T` and `T ≈ U` the two middle witnesses `y`, `y'`
satisfy `𝒯(y) = 𝒯(y')`, and only injectivity of `nbhdFilter` makes them equal so
that `≡_ℰ` can be composed.
-/

universe u

namespace ScottDomains.EquilogicalSpaces

open Topology

variable (E : EquilogicalSpace.{u})

/-- The Σ-topology on `𝒫 (𝒫 |ℰ|)`, introduced locally: no object of `Equ` carries
    one, and it is needed to state the witness at all. -/
local instance scottOnPowerset : TopologicalSpace (Set (Set E.carrier)) :=
  Topology.scott (Set (Set E.carrier)) Set.univ

local instance isScottOnPowerset : IsScott (Set (Set E.carrier)) Set.univ := ⟨rfl⟩

/-- The partial equivalence relation transported along `nbhdFilter`. -/
def witnessRel (S T : Set (Set E.carrier)) : Prop :=
  ∃ x y : E.carrier, E.Rel x y ∧ S = nbhdFilter x ∧ T = nbhdFilter y

theorem witnessRel_symm {S T : Set (Set E.carrier)} (h : witnessRel E S T) :
    witnessRel E T S := by
  obtain ⟨x, y, hxy, hS, hT⟩ := h
  exact ⟨y, x, E.setoid.symm hxy, hT, hS⟩

/-- Transitivity, and the second place `T₀` is spent: the two middle witnesses
    have equal neighbourhood filters, so `nbhdFilter_injective` identifies them
    and `≡_ℰ` composes. -/
theorem witnessRel_trans {S T U : Set (Set E.carrier)}
    (h₁ : witnessRel E S T) (h₂ : witnessRel E T U) : witnessRel E S U := by
  obtain ⟨x, y, hxy, hS, hT⟩ := h₁
  obtain ⟨y', z, hyz, hT', hU⟩ := h₂
  have : y = y' := nbhdFilter_injective (by rw [← hT, hT'])
  subst this
  exact ⟨x, z, E.setoid.trans hxy hyz, hS, hU⟩

/-- **The witness object.** The powerset lattice with the transported partial
    equivalence relation. -/
def witness : PartialEquilogicalSpace.{u} where
  carrier := Set (Set E.carrier)
  Rel := witnessRel E
  rel_symm := witnessRel_symm E
  rel_trans := witnessRel_trans E

/-- **The total part of the witness is exactly the image of the embedding.**

    `⊇` is reflexivity of `≡_ℰ`, taking both witnesses to be the same point;
    `⊆` reads the first witness off. This is what the paper's parenthesis
    asserts — the relation stays partial, reflexive on the image and nowhere
    else. -/
theorem witness_total : (witness E).Total = Set.range (nbhdFilter : E.carrier → _) := by
  ext S
  constructor
  · rintro ⟨x, -, -, hS, -⟩
    exact ⟨x, hS.symm⟩
  · rintro ⟨x, rfl⟩
    exact ⟨x, x, E.setoid.refl x, rfl, rfl⟩

/-- **The forward half of the isomorphism `ℰ ≅ R (witness ℰ)`**: the embedding,
    corestricted to the total part.

    Equivariance is immediate — the transported relation was *defined* to make
    `𝒯(x) ≈ 𝒯(y)` hold exactly when `x ≡_ℰ y`, so the witnesses are `x` and `y`
    themselves. Continuity is `continuous_nbhdFilter` from Theorem 3.6, followed
    by `Continuous.subtype_mk`. -/
def witnessEmbed : Equivariant E (witness E).restrict where
  toFun := fun x => ⟨nbhdFilter x, ⟨x, x, E.setoid.refl x, rfl, rfl⟩⟩
  continuous_toFun := by
    exact Continuous.subtype_mk
      (continuous_nbhdFilter (X := E.carrier)) _
  equivariant := fun {x y} h => ⟨x, y, h, rfl, rfl⟩

/-- The forward map is injective on points, by `T₀`. Together with
    `witness_total` this says it is a bijection onto the total part — the
    content the isomorphism still to be built will package. -/
theorem witnessEmbed_injective : Function.Injective (witnessEmbed E).toFun := by
  intro x y h
  exact nbhdFilter_injective (congrArg Subtype.val h)

/-! ## The inverse -/

/-- The backward map: a total element of the witness *is* a neighbourhood filter,
    by `witness_total`, so it has a point. Chosen with `Exists.choose`; the choice
    is harmless because `T₀` makes the point unique. -/
noncomputable def witnessInv (p : ↥(witness E).Total) : E.carrier := p.2.choose

theorem witnessInv_spec (p : ↥(witness E).Total) :
    p.1 = nbhdFilter (witnessInv E p) :=
  p.2.choose_spec.choose_spec.2.1

/-- The chosen point is *the* point: any other with the same filter equals it. -/
theorem witnessInv_eq {p : ↥(witness E).Total} {x : E.carrier}
    (h : p.1 = nbhdFilter x) : witnessInv E p = x :=
  nbhdFilter_injective (by rw [← witnessInv_spec E p, h])

/-- **The inverse is continuous** — directly from `IsInducing`, with no
    homeomorphism transport. An open `U` of `ℰ` is `nbhdFilter ⁻¹' V` for some
    Σ-open `V` by Theorem 3.6, and then `witnessInv ⁻¹' U` is just
    `Subtype.val ⁻¹' V`, open in the subspace. -/
theorem continuous_witnessInv : Continuous (witnessInv E) := by
  rw [continuous_def]
  intro U hU
  obtain ⟨V, hV, hVU⟩ :=
    (bauerBirkedalScott04_theorem_3_6_embedding
      (X := E.carrier)).toIsInducing.isOpen_iff.mp hU
  have hpre : witnessInv E ⁻¹' U = Subtype.val ⁻¹' V := by
    ext p
    show witnessInv E p ∈ U ↔ p.1 ∈ V
    rw [← hVU, Set.mem_preimage, witnessInv_spec E p]
    rfl
  rw [hpre]
  exact hV.preimage continuous_subtype_val

/-- The backward equivariant map. -/
noncomputable def witnessProject : Equivariant (witness E).restrict E where
  toFun := witnessInv E
  continuous_toFun := continuous_witnessInv E
  equivariant := by
    rintro p q ⟨x, y, hxy, hp, hq⟩
    rw [witnessInv_eq E hp, witnessInv_eq E hq]
    exact hxy

/-! ## The isomorphism -/

theorem witnessProject_comp_witnessEmbed :
    Equivariant.MapEquiv (Equivariant.comp (witnessProject E) (witnessEmbed E))
      (Equivariant.id E) := by
  intro x y hxy
  have h : witnessInv E ((witnessEmbed E).toFun x) = x := witnessInv_eq E rfl
  show E.Rel (witnessInv E ((witnessEmbed E).toFun x)) y
  rw [h]
  exact hxy

theorem witnessEmbed_comp_witnessProject :
    Equivariant.MapEquiv (Equivariant.comp (witnessEmbed E) (witnessProject E))
      (Equivariant.id (witness E).restrict) := by
  rintro p q ⟨x, y, hxy, hp, hq⟩
  refine ⟨x, y, hxy, ?_, hq⟩
  show nbhdFilter (witnessInv E p) = nbhdFilter x
  rw [witnessInv_eq E hp]

/-- **The isomorphism `R (witness ℰ) ≅ ℰ`.** Both composites are identities *as
    classes*, which is what the two lemmas above establish. -/
noncomputable def witnessIso : restrictFunctor.obj (witness E) ≅ E where
  hom := by exact Quotient.mk _ (witnessProject E)
  inv := by exact Quotient.mk _ (witnessEmbed E)
  hom_inv_id := Quotient.sound (witnessEmbed_comp_witnessProject E)
  inv_hom_id := Quotient.sound (witnessProject_comp_witnessEmbed E)

/-- **`R` is essentially surjective**, completing the third of the three
    properties the paper's proof of Theorem 3.12 names. -/
instance : restrictFunctor.{u}.EssSurj where
  mem_essImage Y := ⟨witness Y, ⟨witnessIso Y⟩⟩

/-! ## Theorem 3.12 -/

/-- `R` is an equivalence. The three fields are exactly the three properties the
    paper's proof establishes; each is discharged by `infer_instance` from the
    instances in `Restriction.lean` and above. -/
instance restrictFunctor_isEquivalence : restrictFunctor.{u}.IsEquivalence := {}

/-- **Theorem 3.12**: `Equ` and `PEqu` are equivalent.

    Assembled from the three properties, exactly as the paper assembles it:
    `R` is faithful by definition (`Restriction.lean`), full by the Extension
    Theorem, and essentially surjective by the Embedding Theorem. Mathlib's
    `Equivalence.ofFullyFaithfullyEssSurj` does the packaging.

    Note the direction: the functor goes `PEqu ⥤ Equ`, so the equivalence is
    stated that way round. -/
noncomputable def bauerBirkedalScott04_theorem_3_12 :
    PartialEquilogicalSpace.{u} ≌ EquilogicalSpace.{u} :=
  restrictFunctor.asEquivalence

end ScottDomains.EquilogicalSpaces
