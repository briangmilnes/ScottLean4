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

end ScottDomains.EquilogicalSpaces
