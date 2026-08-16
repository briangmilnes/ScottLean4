import ScottDomains.EquilogicalSpaces.Basic
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts

/-!
# Finite products in `Equ`

Part of Theorem 3.10:

> **Theorem 3.10** The category `Equ` is complete, cocomplete, and it is regular
> well-powered, and regular co-well-powered.

with the paper's construction for the product half:

> Take products first. The product (of any number) of topological spaces is a
> space with a product topology. The product of equivalence relations is an
> equivalence relation. The projection mappings are clearly equivariant.

## Why this is so much shorter than the `PEqu` version

An object of `Equ` is a bare `T₀` space with an equivalence relation — no
lattice, no Σ-topology. So the ambient product topology **is** the right one,
`Prod.instT0Space` gives the separation axiom, and none of `PEquClosed.lean`'s
instance machinery is needed: no `Wrap`, no `@[reducible]`, no Scott-continuity
bridge. The only friction that remains is the one intrinsic to `Equ` — morphisms
are `MapEquiv`-classes, so each limit obligation is an equality of classes and
goes through `Quotient.inductionOn`.
-/

universe u

namespace ScottDomains.EquilogicalSpaces

open CategoryTheory CategoryTheory.Limits

/-! ## The terminal object -/

/-- The one-point equilogical space. -/
def equTerminal : EquilogicalSpace.{u} where
  carrier := PUnit.{u + 1}
  setoid := ⟨fun _ _ => True, ⟨fun _ => trivial, fun _ => trivial, fun _ _ => trivial⟩⟩

instance equUniqueToTerminal (A : EquilogicalSpace.{u}) :
    Unique (A ⟶ equTerminal.{u}) where
  default := Quotient.mk _
    { toFun := fun _ => PUnit.unit
      continuous_toFun := continuous_const
      equivariant := fun _ => trivial }
  uniq := by
    rintro ⟨f⟩
    exact Quotient.sound (fun _ _ _ => trivial)

/-- `PUnit` is terminal in `Equ`: the relation is total, so every map into it is
    equivariant and any two are `MapEquiv`. -/
def equIsTerminal : IsTerminal equTerminal.{u} :=
  IsTerminal.ofUnique _

instance : HasTerminal EquilogicalSpace.{u} :=
  equIsTerminal.hasTerminal

/-! ## Binary products -/

/-- The product of two equilogical spaces: the product topology with the
    componentwise equivalence relation. `T₀` is inherited. -/
def EquilogicalSpace.prod (A B : EquilogicalSpace.{u}) : EquilogicalSpace.{u} where
  carrier := A.carrier × B.carrier
  setoid :=
    { r := fun p q => A.Rel p.1 q.1 ∧ B.Rel p.2 q.2
      iseqv :=
        ⟨fun p => ⟨A.setoid.refl p.1, B.setoid.refl p.2⟩,
         fun h => ⟨A.setoid.symm h.1, B.setoid.symm h.2⟩,
         fun h₁ h₂ => ⟨A.setoid.trans h₁.1 h₂.1, B.setoid.trans h₁.2 h₂.2⟩⟩ }

namespace EquilogicalSpace

/-- First projection. -/
def prodFst (A B : EquilogicalSpace.{u}) : Equivariant (A.prod B) A where
  toFun := Prod.fst
  continuous_toFun := continuous_fst
  equivariant := fun h => h.1

/-- Second projection. -/
def prodSnd (A B : EquilogicalSpace.{u}) : Equivariant (A.prod B) B where
  toFun := Prod.snd
  continuous_toFun := continuous_snd
  equivariant := fun h => h.2

/-- Pairing. -/
def prodLift {T A B : EquilogicalSpace.{u}}
    (f : Equivariant T A) (g : Equivariant T B) : Equivariant T (A.prod B) where
  toFun := fun t => (f.toFun t, g.toFun t)
  continuous_toFun := f.continuous_toFun.prodMk g.continuous_toFun
  equivariant := fun h => ⟨f.equivariant h, g.equivariant h⟩

theorem prodLift_congr {T A B : EquilogicalSpace.{u}}
    {f f' : Equivariant T A} {g g' : Equivariant T B}
    (hf : Equivariant.MapEquiv f f') (hg : Equivariant.MapEquiv g g') :
    Equivariant.MapEquiv (prodLift f g) (prodLift f' g') :=
  fun x y hxy => ⟨hf x y hxy, hg x y hxy⟩

theorem prodFst_comp_prodLift {T A B : EquilogicalSpace.{u}}
    (f : Equivariant T A) (g : Equivariant T B) :
    Equivariant.comp (prodFst A B) (prodLift f g) = f := rfl

theorem prodSnd_comp_prodLift {T A B : EquilogicalSpace.{u}}
    (f : Equivariant T A) (g : Equivariant T B) :
    Equivariant.comp (prodSnd A B) (prodLift f g) = g := rfl

theorem prodLift_unique {T A B : EquilogicalSpace.{u}}
    (m : Equivariant T (A.prod B)) {f : Equivariant T A} {g : Equivariant T B}
    (h₁ : Equivariant.MapEquiv (Equivariant.comp (prodFst A B) m) f)
    (h₂ : Equivariant.MapEquiv (Equivariant.comp (prodSnd A B) m) g) :
    Equivariant.MapEquiv m (prodLift f g) :=
  fun x y hxy => ⟨h₁ x y hxy, h₂ x y hxy⟩

end EquilogicalSpace

/-- The binary fan. -/
def equProdFan (A B : EquilogicalSpace.{u}) : BinaryFan A B :=
  BinaryFan.mk (P := A.prod B)
    (Quotient.mk _ (EquilogicalSpace.prodFst A B))
    (Quotient.mk _ (EquilogicalSpace.prodSnd A B))

/-- It is a limit. Each obligation is an equality of `MapEquiv`-classes, so each
    goes through `Quotient.inductionOn` on representatives. -/
def equProdIsLimit (A B : EquilogicalSpace.{u}) : IsLimit (equProdFan A B) :=
  BinaryFan.isLimitMk
    (fun s => Quotient.map₂ EquilogicalSpace.prodLift
      (fun _ _ hf _ _ hg => EquilogicalSpace.prodLift_congr hf hg)
      (BinaryFan.fst s) (BinaryFan.snd s))
    (fun s => by
      refine Quotient.inductionOn₂ (BinaryFan.fst s) (BinaryFan.snd s) (fun f g => ?_)
      exact congrArg (Quotient.mk _) (EquilogicalSpace.prodFst_comp_prodLift f g))
    (fun s => by
      refine Quotient.inductionOn₂ (BinaryFan.fst s) (BinaryFan.snd s) (fun f g => ?_)
      exact congrArg (Quotient.mk _) (EquilogicalSpace.prodSnd_comp_prodLift f g))
    (fun s m h₁ h₂ => by
      revert h₁ h₂
      refine Quotient.inductionOn m (fun m => ?_)
      refine Quotient.inductionOn₂ (BinaryFan.fst s) (BinaryFan.snd s) (fun f g => ?_)
      intro h₁ h₂
      exact Quotient.sound
        (EquilogicalSpace.prodLift_unique m (Quotient.exact h₁) (Quotient.exact h₂)))

instance equHasLimitPair (A B : EquilogicalSpace.{u}) : HasLimit (pair A B) :=
  HasLimit.mk ⟨equProdFan A B, equProdIsLimit A B⟩

instance : HasBinaryProducts EquilogicalSpace.{u} :=
  hasBinaryProducts_of_hasLimit_pair _

/-- **Theorem 3.10, the finite-products half**: `Equ` has finite products. -/
instance : HasFiniteProducts EquilogicalSpace.{u} :=
  hasFiniteProducts_of_has_binary_and_terminal

end ScottDomains.EquilogicalSpaces
