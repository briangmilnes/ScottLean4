import ScottDomains.EquilogicalSpaces.ProductAlgebraic
import ScottDomains.Morphism
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts

/-!
# Finite products in `ALat`

The categorical assembly step: `ProductAlgebraic.lean` made `A × B` an *object*
of `ALat`; this module exhibits it as a *limit*, and adds the terminal object,
giving `HasFiniteProducts ALat`.

No new mathematics. The projections are the package's `Morphism.prodFst` and
`Morphism.prodSnd`, the pairing is `Combinator.prodMkHom`, and every proof
obligation is `ScottHom.ext` followed by `rfl` or a projection of the hypothesis.
That is the point: with `isAlgebraic_prod` in hand the limit structure is
bookkeeping.

The terminal object is the one-element lattice `PUnit`. Its algebraicity is
`Subsingleton` reasoning — every element is compact and equals every other.
-/

universe u

namespace ScottDomains.EquilogicalSpaces

open CategoryTheory CategoryTheory.Limits ScottDomains

/-! ## The terminal object -/

/-- `PUnit` is algebraic: with one element there is nothing to approximate. -/
instance isAlgebraic_punit : ScottDomains.IsAlgebraic PUnit.{u + 1} where
  directedOn_compactsBelow _ p hp _ _ :=
    ⟨p, hp, le_of_eq (Subsingleton.elim _ _), le_of_eq (Subsingleton.elim _ _)⟩
  isLUB_compactsBelow _ :=
    ⟨fun _ _ => le_of_eq (Subsingleton.elim _ _),
     fun _ _ => le_of_eq (Subsingleton.elim _ _)⟩

/-- The one-element algebraic lattice. -/
def alatTerminal : AlgebraicLattice.{u} where
  carrier := PUnit.{u + 1}

instance uniqueToTerminal (A : AlgebraicLattice.{u}) : Unique (A ⟶ alatTerminal.{u}) where
  default := ScottHom.const PUnit.unit
  uniq _ := ScottHom.ext fun _ => rfl

/-- `PUnit` is terminal in `ALat`: the only Scott-continuous map into a
    one-element lattice is the constant one. -/
def alatIsTerminal : IsTerminal alatTerminal.{u} :=
  IsTerminal.ofUnique _

instance : HasTerminal AlgebraicLattice.{u} :=
  alatIsTerminal.hasTerminal

/-! ## Binary products -/

/-! ### Morphisms of `ALat` as functions

    Typeclass search will not unfold `A ⟶ B` to `ScottHom A.carrier B.carrier`,
    so neither function application nor `DFunLike.congr_fun` works on a morphism
    stated with `⟶`. Re-exporting the instance is the standard bundled-category
    fix and is what makes the limit proofs below readable. -/

instance homFunLike (A B : AlgebraicLattice.{u}) :
    FunLike (A ⟶ B) A.carrier B.carrier :=
  inferInstanceAs (FunLike (ScottHom A.carrier B.carrier) A.carrier B.carrier)

@[ext] theorem hom_ext {A B : AlgebraicLattice.{u}} {f g : A ⟶ B}
    (h : ∀ x, f x = g x) : f = g :=
  ScottHom.ext h

/-- The binary fan on `A × B` with the package's bundled projections. -/
def prodFan (A B : AlgebraicLattice.{u}) : BinaryFan A B :=
  BinaryFan.mk (P := A.prod B)
    (Morphism.prodFst : ScottHom (A.carrier × B.carrier) A.carrier)
    (Morphism.prodSnd : ScottHom (A.carrier × B.carrier) B.carrier)

/-- The fan is a limit. `lift` is `Combinator.prodMkHom`; the two factorizations
    are `rfl`, and uniqueness is `Prod.ext` on the two hypotheses. -/
def prodIsLimit (A B : AlgebraicLattice.{u}) : IsLimit (prodFan A B) :=
  BinaryFan.isLimitMk
    (fun s => Combinator.prodMkHom
      (BinaryFan.fst s : ScottHom s.pt.carrier A.carrier)
      (BinaryFan.snd s : ScottHom s.pt.carrier B.carrier))
    (fun _ => hom_ext fun _ => rfl)
    (fun _ => hom_ext fun _ => rfl)
    (fun _ _ h₁ h₂ => hom_ext fun x =>
      Prod.ext (DFunLike.congr_fun h₁ x) (DFunLike.congr_fun h₂ x))

instance hasLimitPair (A B : AlgebraicLattice.{u}) : HasLimit (pair A B) :=
  HasLimit.mk ⟨prodFan A B, prodIsLimit A B⟩

instance : HasBinaryProducts AlgebraicLattice.{u} :=
  hasBinaryProducts_of_hasLimit_pair _

/-- **`ALat` has finite products.** With a terminal object and binary products,
    Mathlib assembles the rest. This is the first of the two things Theorem 3.8
    was waiting on. -/
instance : HasFiniteProducts AlgebraicLattice.{u} :=
  hasFiniteProducts_of_has_binary_and_terminal

end ScottDomains.EquilogicalSpaces
