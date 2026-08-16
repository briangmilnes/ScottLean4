import ScottDomains.EquilogicalSpaces.EquProducts
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers

/-!
# Theorem 3.10, the completeness half: `Equ` is complete

> Take products first. The product (of any number) of topological spaces is a
> space with a product topology. …
>
> Next, take equalizers. Suppose `f, g : |ℰ| → |ℱ|` are two (representatives of)
> equivariant mappings. Form the set `{ x ∈ |ℰ| | f(x) ≡_ℱ g(x) }`. Endow this
> set with the subspace topology and with the restriction of the equivalence
> relation `≡_ℰ`. This structure, along with the obvious inclusion mapping into
> `ℰ`, is the desired equalizer. Thus, `Equ` is a complete category.

Products over an arbitrary index type and equalizers give all limits, by
Mathlib's `has_limits_of_hasEqualizers_and_products`.

## Why the equalizer is well defined on *classes*

A morphism of `Equ` is a `MapEquiv`-class, and the paper's equalizer is built
from *representatives* — so on the face of it the subset
`{ x | f x ≡ g x }` could depend on the choice. It does not, and the reason is
that an equilogical space carries a **total** equivalence relation: `x ≡ x` holds
for every `x`, so `f ≡ f'` gives `f x ≡ f' x` at every point, not merely at
"total" ones. The two subsets therefore coincide.

This is a place where `Equ` is genuinely easier than `PEqu`, where the relation
is partial and the same argument would only work on the total part. It is also
why `HasLimit` can be proved here by `Quotient.inductionOn₂` on the two
morphisms: `HasLimit` is a `Prop`, so descending to representatives is free.
-/

universe u v

namespace ScottDomains.EquilogicalSpaces

open CategoryTheory CategoryTheory.Limits

/-! ## Products over an arbitrary index type -/

/-- The product of a family of equilogical spaces: the product topology with the
    componentwise equivalence relation. -/
def EquilogicalSpace.pi {J : Type u} (A : J → EquilogicalSpace.{u}) :
    EquilogicalSpace.{u} where
  carrier := ∀ j, (A j).carrier
  setoid :=
    { r := fun x y => ∀ j, (A j).Rel (x j) (y j)
      iseqv :=
        ⟨fun x j => (A j).setoid.refl (x j),
         fun h j => (A j).setoid.symm (h j),
         fun h₁ h₂ j => (A j).setoid.trans (h₁ j) (h₂ j)⟩ }

namespace EquilogicalSpace

/-- A projection out of the product. -/
def piProj {J : Type u} (A : J → EquilogicalSpace.{u}) (j : J) :
    Equivariant (EquilogicalSpace.pi A) (A j) where
  toFun := fun x => x j
  continuous_toFun := continuous_apply j
  equivariant := fun h => h j

/-- The map into the product determined by a family of maps. -/
def piLift {J : Type u} {T : EquilogicalSpace.{u}} {A : J → EquilogicalSpace.{u}}
    (f : ∀ j, Equivariant T (A j)) : Equivariant T (EquilogicalSpace.pi A) where
  toFun := fun t j => (f j).toFun t
  continuous_toFun := continuous_pi fun j => (f j).continuous_toFun
  equivariant := fun h j => (f j).equivariant h

end EquilogicalSpace

/-! ## Equalizers -/

/-- The equalizer object for two *representatives*: the subspace on
    `{ x | f x ≡ g x }` with the restricted relation. -/
def EquilogicalSpace.eqObj {A B : EquilogicalSpace.{u}} (f g : Equivariant A B) :
    EquilogicalSpace.{u} where
  carrier := { x : A.carrier // B.Rel (f.toFun x) (g.toFun x) }
  setoid :=
    { r := fun x y => A.Rel x.1 y.1
      iseqv :=
        ⟨fun x => A.setoid.refl x.1, fun h => A.setoid.symm h,
         fun h₁ h₂ => A.setoid.trans h₁ h₂⟩ }

namespace EquilogicalSpace

/-- The inclusion of the equalizer. -/
def eqInc {A B : EquilogicalSpace.{u}} (f g : Equivariant A B) :
    Equivariant (eqObj f g) A where
  toFun := Subtype.val
  continuous_toFun := continuous_subtype_val
  equivariant := fun h => h

/-- The inclusion equalizes `f` and `g`.

    Note it is *not* enough that `f x ≡ g x` pointwise: `MapEquiv` compares `f`
    at `x` with `g` at a *related* `y`. The extra step is `g`'s equivariance,
    composed with the defining property of the subtype. -/
theorem eqInc_equalizes {A B : EquilogicalSpace.{u}} (f g : Equivariant A B) :
    Equivariant.MapEquiv (Equivariant.comp f (eqInc f g))
      (Equivariant.comp g (eqInc f g)) :=
  fun x _ h => B.setoid.trans x.2 (g.equivariant h)

/-- Any map equalizing `f` and `g` factors through the subtype. The witness uses
    reflexivity of `T`'s relation — available because `Equ`'s relations are
    total. -/
def eqLift {A B T : EquilogicalSpace.{u}} {f g : Equivariant A B}
    (t : Equivariant T A)
    (ht : Equivariant.MapEquiv (Equivariant.comp f t) (Equivariant.comp g t)) :
    Equivariant T (eqObj f g) where
  toFun := fun x => ⟨t.toFun x, ht x x (T.setoid.refl x)⟩
  continuous_toFun := Continuous.subtype_mk t.continuous_toFun _
  equivariant := fun h => t.equivariant h

theorem eqLift_congr {A B T : EquilogicalSpace.{u}} {f g : Equivariant A B}
    {t t' : Equivariant T A} {ht ht'} (h : Equivariant.MapEquiv t t') :
    Equivariant.MapEquiv (eqLift (f := f) (g := g) t ht)
      (eqLift (f := f) (g := g) t' ht') :=
  fun x y hxy => h x y hxy

end EquilogicalSpace

/-! ## Not yet assembled: the Mathlib limit API

    Everything above is the paper's construction and is **proved**: the product
    object with its projections and pairing, and the equalizer object with its
    inclusion, the proof that the inclusion equalizes, and the factorisation.

    What is *not* done is wrapping these as `HasLimitsOfShape (Discrete J)` and
    `HasLimit (parallelPair f g)`, and hence
    `has_limits_of_hasEqualizers_and_products`. Two obstacles, both mechanical
    rather than mathematical, and both measured:

    * **`Quotient.out` on a morphism.** The lift out of a fan must choose a
      representative of each leg — the paper's own "after applying the Axiom of
      Choice to pick representatives" — but `s.proj j` has type `s.pt ⟶ F.obj ⟨j⟩`,
      and `⟶` does not unfold for field notation, so `(s.proj j).out` is rejected.
      This is the same friction recorded in r0064 and r0071; the fix is the same
      shape, retyping the morphism first, but it has to be threaded through every
      leg of a fan indexed by an arbitrary `J`.
    * **API drift.** `mkFanLimit` is deprecated in this Mathlib in favour of
      `Fan.IsLimit.mk`, and the `Fork.IsLimit.mk` obligations need their
      `Quotient` inductions arranged before the fork is built rather than inside
      it.

    So Theorem 3.10's completeness half stays owed in `Theorems3.lean`. The
    mathematics is here; the categorical packaging is not. -/

end ScottDomains.EquilogicalSpaces
