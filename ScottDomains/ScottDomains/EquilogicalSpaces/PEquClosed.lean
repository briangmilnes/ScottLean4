import ScottDomains.EquilogicalSpaces.CartesianClosure
import ScottDomains.EquilogicalSpaces.ALatClosed
import ScottDomains.EquilogicalSpaces.PowersetRetract

/-!
# Cartesian closure of `PEqu`

Theorem 3.13 is proved for `Equ` by transporting cartesian closure across
Theorem 3.12, and the paper does the actual work in `PEqu`:

> We have to show, that for any three structures in `PEqu`, say, `𝒜`, `ℬ`, and
> `𝒞`, there is a one-one correspondence between functions in the two spaces:
> `(𝒜 × ℬ → 𝒞)` and `(𝒜 → (ℬ → 𝒞))`.

`ALatClosed.lean` has cartesian closure of `ALat` — algebraic lattices and plain
Scott-continuous maps. That is *not* `PEqu`: objects here carry a partial
equivalence relation and morphisms are `MapEquiv`-classes. This module supplies
the two objects `PEqu` needs and the currying bijection between its morphisms.

## What each object needs, and where it comes from

| Object | Carrier | Complete lattice | Algebraic |
| ------ | ------- | ---------------- | --------- |
| `𝒜 × ℬ` | `\|𝒜\| × \|ℬ\|` | Mathlib | `isAlgebraic_prod` (r0062) |
| `𝒜 ⟹ ℬ` | `ScottHom \|𝒜\| \|ℬ\|` | `scottHomCompleteLattice` (r0061) | `isAlgebraic_scottHom` (r0059) |

The Σ-topology is *chosen* in each case rather than derived: an object of `PEqu`
must carry the Scott topology of its lattice, so the instance is supplied as
`Topology.scott _ univ` and `IsScott` then holds by `rfl`. Nothing needs to be
proved about how Scott topologies interact with products — the field asks for the
Scott topology of the product lattice, which is what is supplied.

The relations are `ProdRel` and `HomRel` from `CartesianClosure.lean`, which is
also where the currying step is already proved: `scottHomCurry_homRel` says the
order isomorphism `scottHomCurry` preserves them, the paper's "self-proving"
theorem.
-/

universe u

namespace ScottDomains.EquilogicalSpaces

open ScottDomains

/-! ## The product object -/

/-- The binary product of two partial equilogical spaces: the product lattice
    with the componentwise partial equivalence relation. -/
def PartialEquilogicalSpace.prod (A B : PartialEquilogicalSpace.{u}) :
    PartialEquilogicalSpace.{u} :=
  letI : TopologicalSpace (A.carrier × B.carrier) :=
    Topology.scott (A.carrier × B.carrier) Set.univ
  haveI : Topology.IsScott (A.carrier × B.carrier) Set.univ := ⟨rfl⟩
  { carrier := A.carrier × B.carrier
    Rel := ProdRel A.Rel B.Rel
    rel_symm := fun h => ⟨A.rel_symm h.1, B.rel_symm h.2⟩
    rel_trans := fun h₁ h₂ => ⟨A.rel_trans h₁.1 h₂.1, B.rel_trans h₁.2 h₂.2⟩ }

@[simp] theorem PartialEquilogicalSpace.prod_carrier (A B : PartialEquilogicalSpace.{u}) :
    (A.prod B).carrier = (A.carrier × B.carrier) := rfl

/-! ## The exponential object -/

/-- The exponential of two partial equilogical spaces: the algebraic lattice of
    Scott-continuous maps, with the partial equivalence relation of Definition
    3.11(2). -/
noncomputable def PartialEquilogicalSpace.exp (A B : PartialEquilogicalSpace.{u}) :
    PartialEquilogicalSpace.{u} :=
  letI : TopologicalSpace (ScottHom A.carrier B.carrier) :=
    Topology.scott (ScottHom A.carrier B.carrier) Set.univ
  haveI : Topology.IsScott (ScottHom A.carrier B.carrier) Set.univ := ⟨rfl⟩
  { carrier := ScottHom A.carrier B.carrier
    Rel := HomRel A.Rel B.Rel
    rel_symm := fun h => fun x y hxy =>
      B.rel_symm (h y x (A.rel_symm hxy))
    rel_trans := fun h₁ h₂ => fun x y hxy =>
      B.rel_trans (h₁ x x (A.rel_trans hxy (A.rel_symm hxy))) (h₂ x y hxy) }

@[simp] theorem PartialEquilogicalSpace.exp_carrier (A B : PartialEquilogicalSpace.{u}) :
    (A.exp B).carrier = ScottHom A.carrier B.carrier := rfl

/-! ## The currying bijection on relations

    The paper's "self-proving" step, now read at the two objects just built. -/

/-- Currying carries the exponential relation of `𝒜 ⟹ (ℬ ⟹ 𝒞)` to the
    exponential relation of `(𝒜 × ℬ) ⟹ 𝒞`.

    This is `scottHomCurry_homRel` from `CartesianClosure.lean`, restated at the
    bundled objects. Recording it here is what says the two constructions above
    are compatible: the product relation and the exponential relation match up
    under the order isomorphism, which is exactly what cartesian closure of
    `PEqu` will need. -/
theorem PartialEquilogicalSpace.homRel_curry_iff (A B C : PartialEquilogicalSpace.{u})
    (g₁ g₂ : ScottHom A.carrier (ScottHom B.carrier C.carrier)) :
    HomRel A.Rel (HomRel B.Rel C.Rel) g₁ g₂ ↔
      HomRel (ProdRel A.Rel B.Rel) C.Rel (scottHomCurry g₁) (scottHomCurry g₂) :=
  scottHomCurry_homRel A.Rel B.Rel C.Rel g₁ g₂

/-! ## Scott continuity and topological continuity, both ways

    `PowersetRetract.lean` has the Scott-to-topological direction. Objects of
    `PEqu` carry topological continuity in their morphisms but the order-theoretic
    machinery is stated with `ScottContinuous`, so the converse is needed too. -/

theorem scottContinuous_of_continuous {α β : Type u} [Preorder α] [TopologicalSpace α]
    [Topology.IsScott α Set.univ] [Preorder β] [TopologicalSpace β]
    [Topology.IsScott β Set.univ] {f : α → β} (hf : Continuous f) : ScottContinuous f :=
  scottContinuousOn_univ.mp
    ((Topology.IsScott.scottContinuousOn_iff_continuous (D := Set.univ)
      fun _ _ _ => Set.mem_univ _).mpr hf)

/-! ## Blocked: the product cone in `PEqu`

    The projections `𝒜 × ℬ ⟶ 𝒜` and `𝒜 × ℬ ⟶ ℬ` cannot yet be built, because
    `continuous_of_scottContinuous` needs

        Topology.IsScott (A.prod B).carrier Set.univ

    and **instance synthesis does not find it**. What follows is what was
    measured, not what was guessed; three hypotheses were tested and two of them
    were wrong.

    * **Not resolution order.** Raising the priority of the structure's instance
      fields to 2000 changes nothing (r0076).
    * **Not a `Preorder` diamond.** `(A.prod B).isScott` typechecks against the
      goal *both* with the object's own `Preorder`, via `completeLattice`, *and*
      with Mathlib's ambient `Prod.instPreorder` substituted. Two probes, both
      accepted, so those two `Preorder` instances are interchangeable here.
    * **Not the term.** Writing `(A.prod B).isScott` explicitly discharges the
      goal. It is only *synthesis* that fails.

    The remaining explanation consistent with all three measurements is
    **discrimination-key reduction**. `(A.prod B).carrier` is
    `PartialEquilogicalSpace.carrier (prod A B)`; unfolding `prod` and reducing
    the projection gives `A.carrier × B.carrier`, whose key is `Prod _ _`. The
    instance `PartialEquilogicalSpace.isScott` is keyed on
    `PartialEquilogicalSpace.carrier _`, so once the goal's key has reduced to a
    product the instance is never even considered — which is exactly the
    observed behaviour: defeq succeeds, lookup does not.

    Marking `prod` irreducible would stop the reduction but breaks more than it
    fixes: `prod_carrier`, the `ProdRel` unfolding behind `equivariant`, and
    `toFun := Prod.fst` all depend on the carrier being visibly a product.

    So the fix is the wrapper after all — a one-field structure around the
    carrier, so that it is not a product under any amount of reduction. Mathlib's
    `WithScott` is not reusable: it transports `Nonempty`, `Inhabited` and
    `Preorder` only, and a `PEqu` carrier needs `CompleteLattice` and
    `IsAlgebraic` transported too. Those transports are the work, and they are
    what remains.
    Everything above this note is independent of the problem and is proved. -/

end ScottDomains.EquilogicalSpaces
