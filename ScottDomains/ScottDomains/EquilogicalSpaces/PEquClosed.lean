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

    Building the projections `A × B ⟶ A` and `A × B ⟶ B` requires
    `Topology.IsScott (A.prod B).carrier Set.univ`, and **instance resolution
    does not find it**, although `PartialEquilogicalSpace.isScott` is an
    instance and `(A.prod B).isScott` is exactly that fact.

    The cause is an instance clash, not a missing lemma. `(A.prod B).carrier` is
    *definitionally* `A.carrier × B.carrier`, so Mathlib's product-topology
    instance `instTopologicalSpaceProd` is a candidate for
    `TopologicalSpace (A.prod B).carrier` alongside the object's own
    `(A.prod B).topologicalSpace`. When the product topology wins,
    `IsScott (A.prod B).carrier Set.univ` becomes a statement about the *product*
    topology — which is a different topology from the Scott topology of the
    product lattice, and generally strictly coarser. No instance exists for it,
    and none should.

    **Raising the priority of the structure's instance fields does not fix it** —
    tried, at priority 2000, and the same three goals still fail. So the clash is
    not resolution *order*. The remaining candidate is the `Preorder` argument
    rather than the topology: `IsScott α D` takes `[Preorder α]` as well as
    `[TopologicalSpace α]`, and on a carrier that is syntactically a product
    `Prod.instPreorder` competes with the path through the object's
    `completeLattice` field. `PartialEquilogicalSpace.isScott` is stated with the
    latter, so if the goal carries the former the instance cannot apply however
    it is prioritised. This has **not** been confirmed by a resolution trace.

    The fix is structural: the carrier must be protected from ambient instances
    by a one-field wrapper in the manner of Mathlib's `WithLower` / `WithScott`,
    so that it is not syntactically a product and no ambient `Prod` instance is
    a candidate. Mathlib's `WithScott` is not directly reusable here — it
    transports only `Nonempty`, `Inhabited` and `Preorder`, whereas a `PEqu`
    carrier needs `CompleteLattice` and `IsAlgebraic` transported too, and those
    transports are the actual work.

    Everything above this comment is independent of the problem and is proved. -/

end ScottDomains.EquilogicalSpaces
