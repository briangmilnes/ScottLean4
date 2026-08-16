import Mathlib.Topology.Separation.Basic
import Mathlib.CategoryTheory.Category.Basic

/-!
# Equilogical spaces: the category `Equ`

A. Bauer, L. Birkedal and D. S. Scott, *Equilogical Spaces*, Theoretical Computer
Science **315**(1):35–59, 2004. Read from the Elsevier preprint (2 March 2001,
27 pp.) in `ScottDomains/papers/Bauer Birkedal Scott 2004 Equilogical Spaces.pdf`,
so section and theorem numbers below are the printed ones, not preprint pages.

The paper's genesis is Scott's privately circulated manuscript *A New Category?*
(December 1996; Version 2, 19 April 1998), whose text and separate formalization
live at `DanaScottPapers/Scott-1998-A-New-Category.txt` and
`ScottLean/Scott/Scott1998ANewCategory.lean`. That development is **independent
of this one**: it is core Lean 4 with a hand-rolled `TopSpace`, whereas this
module is Mathlib-based. Results are attributed to the 2004 paper here.

## What the paper is for

`Set` and `Top` are both complete, cocomplete, well-powered and co-well-powered,
and `Set` is cartesian closed — but `Top` is not, since in general no topology on
the set of continuous functions makes `· × B ⊣ B → ·` valid. The paper's fix
keeps `Top₀` and adjoins *arbitrary* equivalence relations:

> Definition 3.9. (1) Objects are structures `⟨|ℰ|, Ω_ℰ, ≡_ℰ⟩`, where
> `⟨|ℰ|, Ω_ℰ⟩` is a `T₀`-space and `≡_ℰ` is an (arbitrary) equivalence relation
> on the set `|ℰ|`.
> (2) The mappings between equilogical spaces are the equivalence classes of
> continuous mappings between the topological spaces that preserve the
> equivalence relation (**equivariant** mappings), where the equivalence relation
> on mappings is defined by
> `f ≡_{ℰ→ℱ} g ⟺ ∀ x, y ∈ |ℰ|. (x ≡_ℰ y ⟹ f(x) ≡_ℱ g(y))`.

Two points of that definition are easy to get wrong and are made explicit here.

**Morphisms are equivalence classes, not maps.** `Hom A B` below is a `Quotient`,
so every categorical law is an equality of classes. Stating them up to `Eq` on
representatives would be a different — and false — claim.

**`MapEquiv` relates `f` at `x` to `g` at `y` for *distinct* `≡`-related points**,
not merely `f x ≡ g x` pointwise. The diagonal reading is weaker. It also makes
reflexivity nontrivial: `MapEquiv f f` is exactly the equivariance of `f`, which
is why `mapSetoid` below can only be formed for `Equivariant`, never for bare
continuous maps. The paper calls this "an elementary exercise"; it is discharged
here as `mapSetoid`, with no `sorry`.

## Naming

`CLAUDE.md` fixes `<author><year?>_<kind>_<N>_<M>[_<semantic>]` for a result by
another author, and gives only single-author examples (`jung_theorem_1_37`,
`gunter87_lemma_24_MPair`). For this paper's three authors that spells
`bauerBirkedalScott04_theorem_3_13`. The choice of author slot is a reading of
the rule, not something the rule states; flagged rather than assumed silently.

## Status

Definitions and the category structure are proved. The paper's principal
theorems of §3 are stated with content and left as obligations; see
`ScottDomains/EquilogicalSpaces/README.md` for the tally and for what §4
(dependent type theory) and §5 (Kleene–Kreisel totality) would still need.
-/

universe u

namespace ScottDomains.EquilogicalSpaces

open CategoryTheory

/-! ## Definition 3.9(1): objects -/

/-- An **equilogical space**: a `T₀` topological space together with an arbitrary
    equivalence relation on its points.

    The paper stresses that the equivalence relation "may have very little to do
    with the topology", so no compatibility is required — in some cases the only
    equivariant maps between two spaces are the constant ones despite a rich
    underlying topology. -/
structure EquilogicalSpace : Type (u + 1) where
  /-- The underlying set of points, `|ℰ|`. -/
  carrier : Type u
  /-- The topology `Ω_ℰ`. -/
  [topologicalSpace : TopologicalSpace carrier]
  /-- The `T₀` separation axiom: the topology distinguishes the points. -/
  [t0Space : T0Space carrier]
  /-- The equivalence relation `≡_ℰ`, arbitrary. -/
  setoid : Setoid carrier

attribute [instance] EquilogicalSpace.topologicalSpace EquilogicalSpace.t0Space

namespace EquilogicalSpace

instance : CoeSort EquilogicalSpace (Type u) := ⟨carrier⟩

/-- The equivalence relation `≡_ℰ` of an equilogical space, as a plain relation. -/
def Rel (A : EquilogicalSpace) (x y : A.carrier) : Prop := A.setoid.r x y

theorem Rel.refl (A : EquilogicalSpace) (x : A.carrier) : A.Rel x x :=
  A.setoid.iseqv.refl x

theorem Rel.symm {A : EquilogicalSpace} {x y : A.carrier} (h : A.Rel x y) :
    A.Rel y x :=
  A.setoid.iseqv.symm h

theorem Rel.trans {A : EquilogicalSpace} {x y z : A.carrier}
    (h₁ : A.Rel x y) (h₂ : A.Rel y z) : A.Rel x z :=
  A.setoid.iseqv.trans h₁ h₂

end EquilogicalSpace

/-! ## Definition 3.9(2): equivariant maps and their equivalence -/

/-- An **equivariant map**: a continuous map preserving the equivalence
    relations. These are the *representatives* of morphisms of `Equ`, not the
    morphisms themselves. -/
structure Equivariant (A B : EquilogicalSpace.{u}) where
  /-- The underlying function on points. -/
  toFun : A.carrier → B.carrier
  /-- Continuity for the two topologies. -/
  continuous_toFun : Continuous toFun
  /-- Preservation of the equivalence relations. -/
  equivariant : ∀ {x y : A.carrier}, A.Rel x y → B.Rel (toFun x) (toFun y)

namespace Equivariant

/-- **Definition 3.9(2)**, the equivalence of mappings:
    `f ≡ g ⟺ ∀ x y. x ≡_A y → f x ≡_B g y`.

    Note the two *distinct* points: this is strictly stronger than pointwise
    `f x ≡_B g x`. -/
def MapEquiv {A B : EquilogicalSpace.{u}} (f g : Equivariant A B) : Prop :=
  ∀ x y : A.carrier, A.Rel x y → B.Rel (f.toFun x) (g.toFun y)

/-- Reflexivity of `MapEquiv` **is** equivariance — the two statements are the
    same proposition. This is why the relation is an equivalence only on
    equivariant maps. -/
theorem mapEquiv_refl {A B : EquilogicalSpace.{u}} (f : Equivariant A B) :
    MapEquiv f f := fun _ _ h => f.equivariant h

theorem mapEquiv_symm {A B : EquilogicalSpace.{u}} {f g : Equivariant A B}
    (h : MapEquiv f g) : MapEquiv g f :=
  fun x y hxy => (h y x hxy.symm).symm

/-- Transitivity needs `A.Rel x x`, which is *derived* from `A.Rel x y` by
    symmetry and transitivity rather than taken from reflexivity of the
    setoid — the same argument would therefore go through for a partial
    equivalence relation, which is what Definition 3.11 exploits. -/
theorem mapEquiv_trans {A B : EquilogicalSpace.{u}} {f g h : Equivariant A B}
    (h₁ : MapEquiv f g) (h₂ : MapEquiv g h) : MapEquiv f h :=
  fun x y hxy => (h₁ x x (hxy.trans hxy.symm)).trans (h₂ x y hxy)

/-- The paper's "elementary exercise": `MapEquiv` is an equivalence relation on
    the equivariant maps `A → B`. Proved, no `sorry`. -/
instance mapSetoid (A B : EquilogicalSpace.{u}) : Setoid (Equivariant A B) where
  r := MapEquiv
  iseqv := ⟨mapEquiv_refl, mapEquiv_symm, mapEquiv_trans⟩

/-- The identity equivariant map. -/
def id (A : EquilogicalSpace.{u}) : Equivariant A A where
  toFun := fun x => x
  continuous_toFun := continuous_id
  equivariant := fun h => h

/-- Composition of equivariant maps. -/
def comp {A B C : EquilogicalSpace.{u}} (g : Equivariant B C) (f : Equivariant A B) :
    Equivariant A C where
  toFun := fun x => g.toFun (f.toFun x)
  continuous_toFun := g.continuous_toFun.comp f.continuous_toFun
  equivariant := fun h => g.equivariant (f.equivariant h)

/-- Composition respects `MapEquiv` in both arguments, so it descends to the
    quotient. This is the fact that makes `Equ` a category at all. -/
theorem comp_congr {A B C : EquilogicalSpace.{u}}
    {g g' : Equivariant B C} {f f' : Equivariant A B}
    (hg : MapEquiv g g') (hf : MapEquiv f f') : MapEquiv (comp g f) (comp g' f') :=
  fun x y hxy => hg _ _ (hf x y hxy)

end Equivariant

/-! ## The category `Equ` -/

open Equivariant in
/-- **The category `Equ`** (Definition 3.9). Morphisms are `MapEquiv`-classes of
    equivariant maps, so `Hom A B` is a `Quotient`. All four category laws are
    proved. -/
instance equCategory : LargeCategory EquilogicalSpace.{u} where
  Hom A B := Quotient (mapSetoid A B)
  id A := Quotient.mk _ (Equivariant.id A)
  comp f g := Quotient.map₂ (fun a b => Equivariant.comp b a)
    (fun _ _ h₁ _ _ h₂ => comp_congr h₂ h₁) f g
  id_comp := by
    rintro A B ⟨f⟩
    rfl
  comp_id := by
    rintro A B ⟨f⟩
    rfl
  assoc := by
    rintro A B C D ⟨f⟩ ⟨g⟩ ⟨h⟩
    rfl

end ScottDomains.EquilogicalSpaces
