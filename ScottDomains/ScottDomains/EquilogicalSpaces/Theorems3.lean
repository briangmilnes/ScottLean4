import ScottDomains.EquilogicalSpaces.Basic
import ScottDomains.EquilogicalSpaces.EquProducts
import ScottDomains.EquilogicalSpaces.EquLimits
import ScottDomains.EquilogicalSpaces.EquColimits
import ScottDomains.EquilogicalSpaces.PEquClosed
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
import Mathlib.CategoryTheory.Limits.Shapes.RegularMono
import Mathlib.CategoryTheory.Subobject.Basic
import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# The principal theorems of §3

A. Bauer, L. Birkedal and D. S. Scott, *Equilogical Spaces*, TCS **315**(1):35–59,
2004, §3, as printed in
`ScottDomains/papers/Bauer Birkedal Scott 2004 Equilogical Spaces.pdf`.

Everything here is an **obligation** carried by `sorry`, or a `Prop`-valued claim.
The category structure they are about is proved in
`ScottDomains.EquilogicalSpaces.Basic`, which has no `sorry`.

## The proof spine the paper uses

Three facts of Scott's, all noticed in 1970/71, carry §3:

| # | Result | Statement |
| -- | ------ | --------- |
| 3.6 | Embedding Theorem | `x ↦ 𝒯(x)` topologically embeds a `T₀`-space into `𝒫 Ω_𝒯` with the Σ-topology |
| 3.7 | Extension Theorem | a continuous `f` on a subspace `𝒴 ⊆ 𝒳` into `𝒫 A` extends continuously to `𝒳` |
| 3.8 | — | `ALat` is cartesian closed |

Theorem 3.12 (`Equ ≃ PEqu`) falls out of exactly these three: the restriction
functor `R` to `{x ∣ x ≡ x}` is *faithful* by definition, *full* by 3.7, and
*essentially surjective* by 3.6. Theorem 3.13 then transports cartesian closure
back along that equivalence from 3.8 — in `PEqu` the exponential is the algebraic
lattice of continuous functions under the Σ-topology carrying the induced partial
equivalence relation, and the currying bijection is already an isomorphism of
algebraic lattices, so only preservation of the relation remains. The paper calls
that step "self-proving".

Neither `PEqu` nor the Σ-topology is defined yet, so **3.6, 3.7, 3.8 and 3.12 are
not stated here** — writing them would mean inventing encodings this module
cannot yet express faithfully. They are listed in `README.md` as the next
tranche. Only what can be said with content about `Equ` itself appears below.

## Why the names say `regular`

Theorem 3.10 asserts well-poweredness only in its **regular** form. Footnote 4:

> The authors are indebted to Peter Johnstone for pointing out that, contrary to
> the assertion made in Scott's original unpublished manuscript, `Equ` is *not*
> well powered, for there are fairly simple examples of objects in the category
> with an unbounded number of non-isomorphic subobjects.

So `WellPowered EquilogicalSpace` is **false** and must never be declared as an
instance here, however natural it looks next to the completeness instances —
declaring it would let typeclass resolution silently prove things that are not
true of this category. Mathlib packages `WellPowered` but has no
`RegularWellPowered`, so the two regular halves of 3.10 are stated directly as
`Small.{u}` claims over Mathlib's `IsRegularMono`.
-/

universe u

namespace ScottDomains.EquilogicalSpaces

open CategoryTheory CategoryTheory.Limits

/-! ## Theorem 3.10: completeness and cocompleteness -/

/-- **Theorem 3.10** (completeness half): `Equ` is complete.

    **Proved**, in `EquLimits.lean`. Products over an arbitrary index type are
    the product topology with the componentwise relation; the equalizer of
    `f, g : ℰ → ℱ` is the subspace `{ x ∣ f x ≡_ℱ g x }` with `≡_ℰ` restricted;
    and Mathlib's `has_limits_of_hasEqualizers_and_products` assembles the rest.

    The paper's "after applying the Axiom of Choice to pick representatives" is
    `Quotient.out`, wrapped as `homOut` because `⟶` does not unfold for field
    notation. -/
instance bauerBirkedalScott04_theorem_3_10_hasLimits :
    HasLimitsOfSize.{u, u} EquilogicalSpace.{u} := inferInstance

/-- **Theorem 3.10** (cocompleteness half): `Equ` is cocomplete.

    **Proved**, in `EquColimits.lean`. Coproducts are disjoint unions with the
    union of the relations — which needed `T0Space` for a sigma type, absent from
    Mathlib and proved there. The coequalizer keeps `ℱ`'s topology and coarsens
    `≡_ℱ` to `Relation.EqvGen` of it together with `{ (f x, g x) }`; **no topology
    is placed on the quotient**, which the paper flags as one reason `Equ` is not
    equivalent to `Set`. Mathlib's
    `has_colimits_of_hasCoequalizers_and_coproducts` assembles the rest. -/
instance bauerBirkedalScott04_theorem_3_10_hasColimits :
    HasColimitsOfSize.{u, u} EquilogicalSpace.{u} := inferInstance

/-! ## Theorem 3.10: the regular well-poweredness halves -/

/-- The regular subobjects of `A`: those subobjects whose representing
    monomorphism is an equalizer. Per §3.2 of the 1998 manuscript these are
    obtained by selecting some equivalence classes and taking their union as a
    subspace — and the manuscript warns there are subobjects *not* of this form,
    which is exactly why the unqualified statement fails. -/
def RegularSubobject (A : EquilogicalSpace.{u}) : Type (u + 1) :=
  { S : Subobject A // IsRegularMono S.arrow }

/-- The regular quotients of `A`, as the regular subobjects of `A` in the
    opposite category. Per §3.2, forming a regular quotient is coarsening the
    equivalence relation — putting equivalence classes together. -/
def RegularQuotient (A : EquilogicalSpace.{u}) : Type (u + 1) :=
  { S : Subobject (Opposite.op A) // IsRegularMono S.arrow }

/-- **Theorem 3.10** (regular well-poweredness): the regular subobjects of every
    object form a set. Smallness is rendered as `Small.{u}`, matching how
    Mathlib's own `WellPowered` renders "constitute a set" — Lean's type theory
    has no proper classes.

    A `Prop`-valued claim rather than an instance: Mathlib has no
    `RegularWellPowered` class, and see the module docstring on why no
    `WellPowered` instance may be declared for this category. -/
def Theorem310RegularWellPowered : Prop :=
  ∀ A : EquilogicalSpace.{u}, Small.{u} (RegularSubobject A)

/-- **Theorem 3.10** (regular co-well-poweredness): no object has a proper class
    of non-isomorphic regular quotients. -/
def Theorem310RegularCoWellPowered : Prop :=
  ∀ A : EquilogicalSpace.{u}, Small.{u} (RegularQuotient A)

/-- **Footnote 4** to Theorem 3.10, recorded as a claim and deliberately left
    unasserted: `Equ` is *not* well-powered.

    Written out as the negation of `∀ A, Small.{u} (Subobject A)` rather than as
    `¬ WellPowered …`, so the statement is self-contained and carries no
    `LocallySmall` side condition.

    Not a `theorem … := sorry`. Discharging it needs Johnstone's counterexample,
    which the paper cites but does not exhibit; until that is in hand, reading
    "an unbounded number of non-isomorphic subobjects" as failure of `Small.{u}`
    is an unchecked encoding. A `sorry` asserts the statement is true as written;
    a claim `def` records it without asserting. -/
def Theorem310NotWellPowered : Prop :=
  ¬ ∀ A : EquilogicalSpace.{u}, Small.{u} (Subobject A)

/-! ## Theorem 3.13: cartesian closure -/

/-- **Theorem 3.10**, the finite-products fragment: `Equ` has finite products.

    **Proved**, in `EquProducts.lean`: `PUnit` is terminal and `A.prod B` — the
    product topology with the componentwise equivalence relation — is a binary
    product, whence Mathlib's
    `hasFiniteProducts_of_has_binary_and_terminal`. Restated here under the
    paper's number. -/
instance bauerBirkedalScott04_theorem_3_10_hasFiniteProducts :
    HasFiniteProducts EquilogicalSpace.{u} := inferInstance

/-- **Theorem 3.13**: `Equ` is cartesian closed — the paper's headline result,
    and the property `Top₀` does not share.

    **Proved**, in `PEquClosed.lean`, as `bauerBirkedalScott04_theorem_3_13_equ`:
    cartesian closure is established in `PEqu`, where the paper establishes it,
    and transported along Theorem 3.12.

    Stated with the concrete functor `equProdFunctorRight B`, which is `· × B`.
    An earlier draft of this file used Mathlib's `Limits.prod.functor.obj B`;
    that is `B ⨯ ·`, the *opposite* order, and it routes through `limit`, which
    picks a cone by `Classical.choice` and so is only isomorphic to the concrete
    product rather than equal to it. The paper's own §2 phrasing is "the functor
    `· × B` is adjoint to `B → ·`", so the concrete functor is both the faithful
    reading and the workable one. -/
theorem bauerBirkedalScott04_theorem_3_13 (B : EquilogicalSpace.{u}) :
    Functor.IsLeftAdjoint (equProdFunctorRight B) :=
  bauerBirkedalScott04_theorem_3_13_equ B

end ScottDomains.EquilogicalSpaces
