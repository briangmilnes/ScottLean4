import ScottDomains.EquilogicalSpaces.PartialEquilogical
import ScottDomains.Powerset

/-!
# The restriction functor `R : PEqu ⥤ Equ`, and Theorem 3.12

> **Theorem 3.12** The categories `Equ` and `PEqu` are equivalent.

> **Proof.** The naturally suggested functor from `PEqu` to `Equ` is the one that
> takes `⟨|𝒜|, Ω_𝒜, ≡_𝒜⟩` and restricts the topology to the subspace on the
> subset `{ x ∈ |𝒜| | x ≡_𝒜 x }`. On this subset the equivalence relation is
> "total". … We note first that the functor `R` is faithful by definition. Then,
> the functor `R` is full in view of The Extension Theorem … Finally, the functor
> `R` is essentially surjective on objects by virtue of The Embedding Theorem …

This module builds `R` and discharges the first of the three properties. The
paper's own proof structure is followed exactly, so the remaining work is named
rather than diffuse.

## Status

| Piece | Status |
| ----- | ------ |
| the functor `R` | **proved** |
| `R` faithful | **proved** |
| `R` full | owed — see below |
| `R` essentially surjective | owed — see below |
| Theorem 3.12 | assembled from the three, in `PartialEquilogical.lean` |

### What fullness still needs

Theorem 3.7 as proved extends a continuous map into a **powerset** space. The
paper's parenthesis is wider: "because continuous functions between `T₀`-spaces
can be extended to any algebraic lattices embedding them". Bridging the two needs
that **every algebraic lattice is a continuous retract of a powerset lattice** —
concretely `x ↦ compactsBelow x` into `𝒫 (K L)` with retraction `S ↦ sSup S` —
and then transport of the extension along that retraction. The paper flags this
itself when it says Theorem 3.7 "in fact holds for all the continuous retracts of
the powerset spaces". That retraction is not in the package.

### What essential surjectivity still needs

Given an equilogical space `ℰ`, the witness is `𝒫 Ω_ℰ` carrying the partial
equivalence relation transported along `nbhdFilter`, whose total part is the
image of `nbhdFilter` — homeomorphic to `ℰ` by Theorem 3.6, which is proved.
`IsAlgebraic (Set X)` is available from `ScottDomains.Powerset`, so the witness
*is* an object; what remains is building the object and the isomorphism.
-/

universe u

namespace ScottDomains.EquilogicalSpaces

open CategoryTheory

/-! ## The object part -/

/-- **Restriction to the total elements.** A partial equilogical space becomes an
    equilogical space by cutting down to `{ x | x ≡ x }`, where the partial
    equivalence relation *is* total.

    Reflexivity of the restricted relation is literally the subtype's membership
    proof: `x.2 : x.1 ∈ A.Total` unfolds to `A.Rel x.1 x.1`. `T₀` and the
    topology are inherited from the subspace. -/
def PartialEquilogicalSpace.restrict (A : PartialEquilogicalSpace.{u}) :
    EquilogicalSpace.{u} where
  carrier := ↥A.Total
  setoid :=
    { r := fun x y => A.Rel x.1 y.1
      iseqv := ⟨fun x => x.2, fun h => A.rel_symm h, fun h₁ h₂ => A.rel_trans h₁ h₂⟩ }

/-! ## The morphism part -/

/-- An equivariant map restricts to the total parts. It lands there because
    equivariance sends `x ≡ x` to `f x ≡ f x`. -/
def PEquivariant.restrict {A B : PartialEquilogicalSpace.{u}} (f : PEquivariant A B) :
    Equivariant A.restrict B.restrict where
  toFun := fun x => ⟨f.toFun x.1, f.equivariant x.2⟩
  continuous_toFun :=
    Continuous.subtype_mk (f.continuous_toFun.comp continuous_subtype_val) _
  equivariant := fun h => f.equivariant h

/-- Restriction respects `MapEquiv`, so it descends to the quotient. -/
theorem PEquivariant.restrict_congr {A B : PartialEquilogicalSpace.{u}}
    {f g : PEquivariant A B} (h : PEquivariant.MapEquiv f g) :
    Equivariant.MapEquiv f.restrict g.restrict :=
  fun x y hxy => h x.1 y.1 hxy

/-- **The restriction functor `R : PEqu ⥤ Equ`.** -/
def restrictFunctor : PartialEquilogicalSpace.{u} ⥤ EquilogicalSpace.{u} where
  obj A := A.restrict
  map f := Quotient.map PEquivariant.restrict
    (fun _ _ h => PEquivariant.restrict_congr h) f
  map_id := by rintro A; rfl
  map_comp := by rintro A B C ⟨f⟩ ⟨g⟩; rfl

/-! ## `R` is faithful -/

/-- **`R` is faithful — "by definition", as the paper says.**

    Two equivariant maps agreeing on the total part agree everywhere *as
    morphisms*, because `MapEquiv` only ever tests them at `≡`-related arguments,
    and `A.Rel x y` already forces both `x` and `y` to be total
    (`rel_refl_left`, `rel_refl_right`). Nothing is said about their values off
    the total part, and nothing needs to be. -/
instance : restrictFunctor.{u}.Faithful where
  map_injective := by
    rintro A B ⟨f⟩ ⟨g⟩ h
    refine Quotient.sound fun x y hxy => ?_
    exact Quotient.exact h
      ⟨x, PartialEquilogicalSpace.rel_refl_left hxy⟩
      ⟨y, PartialEquilogicalSpace.rel_refl_right hxy⟩ hxy

end ScottDomains.EquilogicalSpaces
