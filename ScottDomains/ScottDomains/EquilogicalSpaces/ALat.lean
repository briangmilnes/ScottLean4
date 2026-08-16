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

/-! ## The function space is a complete lattice

    The second half of "the exponential is an object": `ScottHom X Y` must be a
    *lattice*, and the package gives it only a `CompletePartialOrder`. -/

section ScottHomLattice

variable {α : Type u} [Preorder α] {β : Type u} [CompleteLattice β]

/-- With a complete-lattice codomain, the pointwise supremum of an **arbitrary**
    set of Scott-continuous maps is Scott-continuous — no directedness, no
    boundedness.

    The mathematics is that suprema commute: for directed `D` with `⋁ D = a`,

        (⨆ᵢ fᵢ)(a) = ⨆ᵢ fᵢ(a) = ⨆ᵢ ⨆_{x∈D} fᵢ(x) = ⨆_{x∈D} ⨆ᵢ fᵢ(x) = ⨆_{x∈D} (⨆ᵢ fᵢ)(x)

    and the interchange holds unconditionally in a complete lattice.

    In Lean it is one application of the package's own
    `scottContinuous_pointwiseSup_of_forall_isLUB`, which was deliberately
    stated *without* directedness — "only that each evaluation image attains its
    least upper bound at `sSup`". A complete-lattice codomain is a third
    sufficient condition alongside the directed and bounded-complete ones, and
    the existing design accommodates it for free. -/
theorem scottContinuous_pointwiseSup_of_completeLattice (d : Set (ScottHom α β)) :
    ScottContinuous fun x => sSup ((fun f : ScottHom α β => f x) '' d) :=
  ScottHom.scottContinuous_pointwiseSup_of_forall_isLUB fun _ => isLUB_sSup _

/-- Consequently the package's `sSup` is pointwise on **every** set: the `dite`
    in its definition always takes the positive branch, so the `const ⊥` junk
    value never fires when the codomain is a lattice.

    This is why no second `SupSet` is introduced below, and hence no `SupSet`
    diamond — the very hazard `ScottHom.lean` records as having broken an
    `Iff.rfl` in r0004. Branching the definition on *continuity* rather than on
    directedness is what makes this work. -/
theorem coe_sSup_of_completeLattice (d : Set (ScottHom α β)) (x : α) :
    (sSup d) x = sSup ((fun f : ScottHom α β => f x) '' d) :=
  ScottHom.coe_sSup_of_continuous (scottContinuous_pointwiseSup_of_completeLattice d) x

/-- Every set of Scott-continuous maps into a complete lattice has a least upper
    bound, namely the package's own `sSup`. -/
theorem isLUB_sSup_scottHom (d : Set (ScottHom α β)) : IsLUB d (sSup d) := by
  constructor
  · intro f hf x
    dsimp only
    rw [coe_sSup_of_completeLattice]
    exact le_sSup ⟨f, hf, rfl⟩
  · intro g hg x
    dsimp only
    rw [coe_sSup_of_completeLattice]
    refine sSup_le ?_
    rintro _ ⟨f, hf, rfl⟩
    exact hg hf x

/-- **`ScottHom α β` is a complete lattice** when `β` is, with the *existing*
    `SupSet` and the *existing* `⊥`.

    Now a real `instance`, where the previous revision had a `def`. Mathlib's
    `completeLatticeOfSup` documents itself as having "bad definitional
    properties" and sets `bot := sSup ∅`, whereas the package's
    `CompletePartialOrder (ScottHom α β)` sets `bot := const ⊥`. Registering that
    globally would have put an `OrderBot` diamond across the library — the hazard
    `ScottHom.lean` records as having broken an `Iff.rfl` in r0004.

    The fix is to override the one bad field: `bot` is hand-rolled back to
    `const ⊥`, so the `OrderBot` this instance carries is *definitionally* the
    one `CompletePartialOrder` already carried, and the diamond collapses. `sSup`
    was never at risk — it is the package's own, by
    `coe_sSup_of_completeLattice`. Verified by rebuilding all 1538 jobs. -/
noncomputable instance scottHomCompleteLattice : CompleteLattice (ScottHom α β) :=
  { completeLatticeOfSup (ScottHom α β) isLUB_sSup_scottHom with
    bot := ScottHom.const ⊥
    bot_le := fun _ _ => bot_le }

/-- The two descriptions of `⊥` agree: the least upper bound of the empty family
    is the constant-`⊥` function. This is the compatibility fact the instance
    above is built to respect rather than to prove after the fact. -/
theorem scottHom_bot_eq_const : (⊥ : ScottHom α β) = ScottHom.const ⊥ := rfl

end ScottHomLattice

end ScottDomains.EquilogicalSpaces
