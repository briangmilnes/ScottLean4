import ScottDomains.EquilogicalSpaces.CartesianClosure
import ScottDomains.Combinator
import Mathlib.CategoryTheory.Category.Basic

/-!
# `ALat`: the category of algebraic lattices

The carrier category of Definition 3.11 and Theorem 3.8 of Bauer–Birkedal–Scott
2004. The paper treats `ALat` as known — "algebraic lattices are just one of many
cartesian closed categories proposed for domain theory" — and cites Gierz et al.,
*A Compendium of Continuous Lattices* for it. This module supplies it.

An **algebraic lattice** here is a complete lattice that is algebraic in the
package's sense (`ScottDomains.IsAlgebraic`: every element is the least upper
bound of its directed set of compact approximants). Morphisms are the bundled
Scott-continuous maps `ScottHom`.

## The `BoundedComplete` instance

`ScottDomains.FunctionSpaceDomain` proves `IsAlgebraic (ScottHom α β)` for `α`
algebraic and `β` algebraic **and bounded complete**. Every complete lattice is
bounded complete — `sSup s` is a least upper bound of `s` whether or not `s` is
bounded — but the package had no instance saying so, which is what blocked
Theorem 3.8 from using its own function-space result. `completeLattice_boundedComplete`
below supplies it in one line.

The instance is sound because `CompleteLattice.toCompletePartialOrder` is defined
with `sSup := sSup`: the `SupSet` the `CompletePartialOrder` carries is literally
the lattice's own, so `isLUB_sSup` discharges the field directly with no
compatibility side condition.

## What this does and does not settle

Bundling `ALat` and its category is done here, proved. Cartesian closure of
`ALat` is **still not stated**, and one concrete obstruction remains: an
exponential must be an *object*, so `ScottHom X Y` needs a `CompleteLattice`
structure, and the package gives it only a `CompletePartialOrder`. The pointwise
lattice structure on a function space between complete lattices is standard but
is not in the package. See `README.md`.
-/

universe u

namespace ScottDomains.EquilogicalSpaces

open CategoryTheory ScottDomains

/-! ## Every complete lattice is bounded complete -/

/-- A complete lattice is bounded complete: `sSup s` is a least upper bound of
    every subset, so in particular of every subset that happens to be bounded
    above. The `BddAbove` hypothesis is discarded.

    This is what lets `ScottDomains.FunctionSpaceDomain`'s
    `IsAlgebraic (ScottHom α β)` apply when the codomain is a lattice. -/
instance completeLattice_boundedComplete {L : Type u} [CompleteLattice L] :
    ScottDomains.BoundedComplete L where
  isLUB_sSup_of_bddAbove s _ := isLUB_sSup s

/-! ## Objects -/

/-- An **algebraic lattice**: a complete lattice in which every element is the
    least upper bound of its directed set of compact approximants. -/
structure AlgebraicLattice : Type (u + 1) where
  /-- The underlying set. -/
  carrier : Type u
  [completeLattice : CompleteLattice carrier]
  [isAlgebraic : ScottDomains.IsAlgebraic carrier]

attribute [instance] AlgebraicLattice.completeLattice AlgebraicLattice.isAlgebraic

namespace AlgebraicLattice

instance : CoeSort AlgebraicLattice (Type u) := ⟨carrier⟩

/-- The identity Scott-continuous map, built as `ContinuousConstruction.idHom`
    does. The package has no `ScottHom.id` under that name. -/
def idHom (A : AlgebraicLattice.{u}) : ScottHom A.carrier A.carrier :=
  ⟨_root_.id, ScottContinuous.id⟩

@[simp] theorem idHom_apply (A : AlgebraicLattice.{u}) (x : A.carrier) :
    A.idHom x = x := rfl

end AlgebraicLattice

/-! ## The category -/

/-- **`ALat`**: algebraic lattices and Scott-continuous maps.

    Unlike `Equ` and `PEqu`, morphisms here are honest functions, not
    equivalence classes — there is no relation to quotient by — so the category
    laws are `ext`-then-`rfl`. -/
instance alatCategory : LargeCategory AlgebraicLattice.{u} where
  Hom A B := ScottHom A.carrier B.carrier
  id A := A.idHom
  comp f g := ScottDomains.Combinator.comp g f
  id_comp _ := by ext _; rfl
  comp_id _ := by ext _; rfl
  assoc _ _ _ := by ext _; rfl

/-! ## Towards Theorem 3.8 -/

/-- The function space of algebraic lattices is algebraic — the exponential's
    carrier is at least an *algebraic* object.

    **Proved**, and it is `completeLattice_boundedComplete` above that makes it
    go through: `FunctionSpaceDomain`'s result wants the codomain bounded
    complete, and until now nothing said a complete lattice is. -/
theorem isAlgebraic_scottHom (A B : AlgebraicLattice.{u}) :
    ScottDomains.IsAlgebraic (ScottHom A.carrier B.carrier) :=
  inferInstance

end ScottDomains.EquilogicalSpaces
