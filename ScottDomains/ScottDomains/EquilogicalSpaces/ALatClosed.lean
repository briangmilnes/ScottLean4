import ScottDomains.EquilogicalSpaces.ALatProducts
import ScottDomains.Skeleton.Lemma17
import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# Theorem 3.8: `ALat` is cartesian closed

The last link. `ALatProducts.lean` gave `HasFiniteProducts ALat`; this module
builds the exponential functor and the adjunction

    (- × B)  ⊣  (B ⟹ -)

which is cartesian closure in the paper's own §2 phrasing: "the functor `· × B`
is adjoint to `B → ·` for all objects `B`".

## Why the product functor is built here rather than taken from Mathlib

Mathlib's `Limits.prod.functor.obj B` is defined through `limit`, which selects a
cone by `Classical.choice` from the `Nonempty (LimitCone _)` that
`HasLimit.mk` supplies. It is therefore *isomorphic* to the cone
`ALatProducts.prodFan` but not *definitionally* it, so an adjunction stated
against it would need transport along that iso before any `rfl` could fire.

`prodFunctorRight` below is the concrete functor `X ↦ X × B`, whose object part
is `AlgebraicLattice.prod` on the nose. Every naturality obligation then closes
by `ext` and `rfl`. Relating it to Mathlib's chosen product is a separate,
purely formal step and is not needed to state Theorem 3.8.

## What each half costs

The exponential's *object* part was already in hand — the carrier is a complete
lattice (`scottHomCompleteLattice`) and algebraic (`isAlgebraic_scottHom`). Its
*morphism* part is post-composition, and that needs `scottContinuous_postcomp`
below: post-composing with a fixed `q` is Scott-continuous **as a map on the
function space**. The package proves this for endomorphisms as
`Skeleton.Lemma17.scottContinuous_compFun`; the argument generalizes verbatim to
`q : β ⟶ γ`, which is what a functor between different objects needs.

The adjunction itself is `scottHomCurry` — already proved in
`ScottDomains.Currying` — packaged by `Adjunction.mkOfHomEquiv`.
-/

universe u

namespace ScottDomains.EquilogicalSpaces

open CategoryTheory ScottDomains

/-! ## Post-composition is continuous on the function space -/

section Postcomp

variable {α β γ : Type u} [CompletePartialOrder α] [CompletePartialOrder β]
  [CompletePartialOrder γ]

/-- Post-composition with a fixed `q` is Scott-continuous as a map
    `(α → β) → (α → γ)` on function spaces.

    Suprema in the function space are pointwise, so at each `x` the claim reduces
    to continuity of `q` applied to the evaluation image of `d` at `x`. This is
    `Skeleton.Lemma17.scottContinuous_compFun` with the endomorphism restriction
    lifted: there `p, q` are endomaps of a single object, here `q : β → γ` goes
    between two, which is what the exponential *functor* requires. -/
theorem scottContinuous_postcomp (q : ScottHom β γ) :
    ScottContinuous (fun f : ScottHom α β => Combinator.comp q f) := by
  intro d hne hd F hF
  constructor
  · rintro _ ⟨f, hf, rfl⟩
    intro x
    exact q.monotone (hF.1 hf x)
  · intro G hG x
    have hqlub : IsLUB (⇑q '' ((fun f : ScottHom α β => f x) '' d)) (q (F x)) :=
      q.scottContinuous (hne.image _) (ScottHom.directedOn_eval_image hd x)
        (ScottHom.isLUB_eval_image_of_isLUB hd hF x)
    refine hqlub.2 ?_
    rintro _ ⟨_, ⟨f, hf, rfl⟩, rfl⟩
    exact hG ⟨f, hf, rfl⟩ x

end Postcomp

/-! ## The two functors -/

/-- The exponential object `B ⟹ Y`. Its carrier is the function space; that this
    is an object of `ALat` is `scottHomCompleteLattice` together with
    `isAlgebraic_scottHom`. -/
noncomputable def expObj (B Y : AlgebraicLattice.{u}) : AlgebraicLattice.{u} where
  carrier := ScottHom B.carrier Y.carrier

/-- The exponential functor `B ⟹ -`, acting on morphisms by post-composition. -/
noncomputable def expFunctor (B : AlgebraicLattice.{u}) :
    AlgebraicLattice.{u} ⥤ AlgebraicLattice.{u} where
  obj Y := expObj B Y
  map f := ⟨fun g => Combinator.comp f g, scottContinuous_postcomp f⟩
  map_id _ := hom_ext fun _ => ScottHom.ext fun _ => rfl
  map_comp _ _ := hom_ext fun _ => ScottHom.ext fun _ => rfl

/-- The functor `- × B`, with object part `AlgebraicLattice.prod` on the nose.
    The morphism part is `⟨f p.1, p.2⟩`, assembled from the package's bundled
    projections and pairing so continuity comes for free. -/
def prodFunctorRight (B : AlgebraicLattice.{u}) :
    AlgebraicLattice.{u} ⥤ AlgebraicLattice.{u} where
  obj X := X.prod B
  map f := Combinator.prodMkHom
    (Combinator.comp f (Morphism.prodFst)) (Morphism.prodSnd)
  map_id _ := by exact ScottHom.ext fun _ => rfl
  map_comp _ _ := by exact ScottHom.ext fun _ => rfl

/-! ## The adjunction -/

/-- **Theorem 3.8**: `- × B ⊣ B ⟹ -`, hence `ALat` is cartesian closed.

    The hom-equivalence is `ScottDomains.Currying.scottHomCurry`, already proved:
    `ScottHom X (ScottHom B Y) ≃o ScottHom (X × B) Y`. Both naturality squares
    close by `ext` and `rfl`, because `prodFunctorRight` uses the product on the
    nose rather than Mathlib's chosen limit. -/
noncomputable def prodExpAdjunction (B : AlgebraicLattice.{u}) :
    prodFunctorRight B ⊣ expFunctor B :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun _ _ => by exact scottHomCurry.symm.toEquiv
      homEquiv_naturality_left_symm := by
        intros; exact ScottHom.ext fun _ => rfl
      homEquiv_naturality_right := by
        intros; exact ScottHom.ext fun _ => ScottHom.ext fun _ => rfl }

/-- `- × B` is a left adjoint, for every `B` — Theorem 3.8 in the paper's §2
    phrasing, and the exact shape `Theorems3.bauerBirkedalScott04_theorem_3_13`
    uses for `Equ`. -/
theorem isLeftAdjoint_prodFunctorRight (B : AlgebraicLattice.{u}) :
    Functor.IsLeftAdjoint (prodFunctorRight B) :=
  ⟨⟨_, ⟨prodExpAdjunction B⟩⟩⟩

/-- **Theorem 3.8**, under the paper's number.

    Restated so that a reader looking for "3.8" finds it by name, as
    `CLAUDE.md`'s naming rule intends. The content is
    `isLeftAdjoint_prodFunctorRight` above. -/
theorem bauerBirkedalScott04_theorem_3_8 (B : AlgebraicLattice.{u}) :
    CategoryTheory.Functor.IsLeftAdjoint (prodFunctorRight B) :=
  isLeftAdjoint_prodFunctorRight B

end ScottDomains.EquilogicalSpaces
