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

/-! ## Choosing a representative of a morphism

    The paper's parenthesis — "after applying the Axiom of Choice to pick
    representatives" — is `Quotient.out`. It cannot be written as
    `(s.proj j).out` directly: `s.proj j` has type `s.pt ⟶ F.obj ⟨j⟩`, and `⟶`
    does not unfold for field notation. Retyping it once in a `def`, whose body
    is checked at *default* transparency, is the whole fix. -/

/-- A chosen representative of a morphism of `Equ`. -/
noncomputable def homOut {A B : EquilogicalSpace.{u}} (f : A ⟶ B) :
    Equivariant A B := Quotient.out f

theorem homOut_spec {A B : EquilogicalSpace.{u}} (f : A ⟶ B) :
    Quotient.mk _ (homOut f) = f := Quotient.out_eq f

/-! ## Products, as limits

    `hasProducts_of_limit_fans` is the purpose-built entry point: it wants a fan
    and a proof that it is a limit, and handles the passage from `Fan f` to
    `Cone F` for `F : Discrete J ⥤ Equ` itself. -/

open EquilogicalSpace in
/-- The fan on the product object. -/
def equFan {J : Type u} (A : J → EquilogicalSpace.{u}) : Fan A :=
  Fan.mk (EquilogicalSpace.pi A) (fun j => Quotient.mk _ (piProj A j))

open EquilogicalSpace in
/-- It is a limit. The lift chooses a representative of each leg with `homOut` —
    the paper's appeal to choice — and `homOut_spec` is what makes the
    factorisation hold on the nose. -/
noncomputable def equFanIsLimit {J : Type u} (A : J → EquilogicalSpace.{u}) :
    IsLimit (equFan A) :=
  Fan.IsLimit.mk _
    (fun s => Quotient.mk _ (piLift fun j => homOut (s.proj j)))
    (fun s j => homOut_spec (s.proj j))
    (fun s m hm => by
      revert hm
      refine Quotient.inductionOn m (fun m => ?_)
      intro hm
      refine Quotient.sound (fun x y hxy j => ?_)
      exact Quotient.exact ((hm j).trans (homOut_spec (s.proj j)).symm) x y hxy)

instance : HasProducts.{u} EquilogicalSpace.{u} :=
  hasProducts_of_limit_fans equFan equFanIsLimit

/-! ## Equalizers, as limits -/

open EquilogicalSpace in
instance equHasLimitParallelPair {A B : EquilogicalSpace.{u}} (f g : A ⟶ B) :
    HasLimit (parallelPair f g) := by
  refine Quotient.inductionOn₂ f g (fun f g => HasLimit.mk ?_)
  refine
    { cone := Fork.ofι (P := eqObj f g) (Quotient.mk _ (eqInc f g))
        (Quotient.sound (eqInc_equalizes f g))
      isLimit := Fork.IsLimit.mk _
        (fun s => Quotient.mk _
          (eqLift (homOut (Fork.ι s))
            (Quotient.exact ((homOut_spec (Fork.ι s)).symm ▸ s.condition))))
        (fun s => homOut_spec (Fork.ι s))
        (fun s m hm => ?_) }
  revert hm
  refine Quotient.inductionOn m (fun m => ?_)
  intro hm
  refine Quotient.sound (fun x y hxy => ?_)
  exact Quotient.exact (hm.trans (homOut_spec (Fork.ι s)).symm) x y hxy

instance : HasEqualizers EquilogicalSpace.{u} :=
  hasEqualizers_of_hasLimit_parallelPair _

/-- **Theorem 3.10, the completeness half**: `Equ` is complete. -/
instance equHasLimits : HasLimitsOfSize.{u, u} EquilogicalSpace.{u} :=
  has_limits_of_hasEqualizers_and_products

end ScottDomains.EquilogicalSpaces
