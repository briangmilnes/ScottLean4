import ScottDomains.EquilogicalSpaces.SigmaTopology
import ScottDomains.Domain
import Mathlib.CategoryTheory.Equivalence

/-!
# Definition 3.11 and Theorem 3.12: the category `PEqu`

A. Bauer, L. Birkedal and D. S. Scott, *Equilogical Spaces*, TCS **315**(1):35–59,
2004, §3, `ScottDomains/papers/Bauer Birkedal Scott 2004 Equilogical Spaces.pdf`.

> **Definition 3.11** (1) Objects are structures `𝒜 = ⟨|𝒜|, Ω_𝒜, ≡_𝒜⟩`, where
> `⟨|𝒜|, Ω_𝒜⟩` is the Σ-topology of an algebraic lattice, and where `≡_𝒜` is a
> *partial* equivalence relation, i.e., reflexive only on a subset of `|𝒜|`.

`PEqu` exists to make Theorem 3.13 provable. `Equ` itself has no evident
exponential — that is exactly why `Top₀` fails to be cartesian closed — but in
`PEqu` the underlying object of an exponential is the algebraic lattice of
continuous functions, and `ALat` *is* cartesian closed (Theorem 3.8). Theorem
3.12 then transports the structure back.

## Why the `Equ` proofs survive the weakening to a PER

`Basic.lean`'s `mapEquiv_trans` derives `A.Rel x x` from `A.Rel x y` by symmetry
followed by transitivity, rather than reading it off reflexivity. That was
written for this module: the identical argument goes through when `≡` is only
*partial*, which is why `mapSetoid` below is a near-copy rather than a new proof
idea. Reflexivity of the relation on maps is, as in `Equ`, precisely
equivariance.

## Status

Definition 3.11 and the category `PEqu` are proved. Theorems 3.6, 3.7 and 3.12
are stated as obligations. Theorem 3.8 (`ALat` is cartesian closed) is **not**
stated here — it needs a bundled category of algebraic lattices and should
interoperate with `ScottDomains.FunctionSpaceDomain` (`IsAlgebraic (ScottHom α β)`)
and `ScottDomains.Currying` (`D → (E → F) ≅ (D × E) → F`), which already carry
most of its content. See this directory's `README.md`.
-/

universe u

namespace ScottDomains.EquilogicalSpaces

open Set Topology

/-! ## Definition 3.11(1): objects -/

/-- A **partial equilogical space**: an algebraic lattice under its Σ-topology,
    together with a partial equivalence relation — symmetric and transitive, but
    reflexive only on a subset.

    Algebraicity is carried by the package's `ScottDomains.IsAlgebraic`, which is
    stated over `CompletePartialOrder`; a `CompleteLattice` supplies that through
    `CompleteLattice.toCompletePartialOrder`. Using the package's class rather
    than a Mathlib equivalent is deliberate: Theorem 3.8 will need to meet
    `FunctionSpaceDomain.lean`, which is phrased in these terms. -/
structure PartialEquilogicalSpace : Type (u + 1) where
  /-- The underlying set of the algebraic lattice, `|𝒜|`. -/
  carrier : Type u
  [completeLattice : CompleteLattice carrier]
  [topologicalSpace : TopologicalSpace carrier]
  /-- The topology is the Σ-topology (Definition 3.4); see `SigmaTopology.lean`. -/
  [isScott : IsScott carrier univ]
  /-- The lattice is algebraic. -/
  [isAlgebraic : ScottDomains.IsAlgebraic carrier]
  /-- The partial equivalence relation `≡_𝒜`. -/
  Rel : carrier → carrier → Prop
  rel_symm : ∀ {x y : carrier}, Rel x y → Rel y x
  rel_trans : ∀ {x y z : carrier}, Rel x y → Rel y z → Rel x z

attribute [instance] PartialEquilogicalSpace.completeLattice
  PartialEquilogicalSpace.topologicalSpace PartialEquilogicalSpace.isScott
  PartialEquilogicalSpace.isAlgebraic

namespace PartialEquilogicalSpace

instance : CoeSort PartialEquilogicalSpace (Type u) := ⟨carrier⟩

/-- The subset on which the partial equivalence relation is reflexive — the
    "total" elements. Theorem 3.12's restriction functor `R` cuts a partial
    equilogical space down to exactly this subset. -/
def Total (A : PartialEquilogicalSpace.{u}) : Set A.carrier := { x | A.Rel x x }

/-- A PER is reflexive wherever it is inhabited: `x ≡ y` forces `x ≡ x`. This is
    the step that lets every `Equ` argument survive the weakening. -/
theorem rel_refl_left {A : PartialEquilogicalSpace.{u}} {x y : A.carrier}
    (h : A.Rel x y) : A.Rel x x :=
  A.rel_trans h (A.rel_symm h)

theorem rel_refl_right {A : PartialEquilogicalSpace.{u}} {x y : A.carrier}
    (h : A.Rel x y) : A.Rel y y :=
  A.rel_trans (A.rel_symm h) h

theorem mem_total_of_rel {A : PartialEquilogicalSpace.{u}} {x y : A.carrier}
    (h : A.Rel x y) : x ∈ A.Total := rel_refl_left h

end PartialEquilogicalSpace

/-! ## Definition 3.11(2): equivariant maps -/

/-- An **equivariant map** of partial equilogical spaces: continuous between the
    Σ-topologies and preserving the partial equivalence relations. -/
structure PEquivariant (A B : PartialEquilogicalSpace.{u}) where
  /-- The underlying function. -/
  toFun : A.carrier → B.carrier
  /-- Continuity for the two Σ-topologies. -/
  continuous_toFun : Continuous toFun
  /-- Preservation of the partial equivalence relations. -/
  equivariant : ∀ {x y : A.carrier}, A.Rel x y → B.Rel (toFun x) (toFun y)

namespace PEquivariant

/-- **Definition 3.11(2)**, the equivalence of mappings, in the same two-point
    form as Definition 3.9(2). The paper remarks that equivariant maps for `PEqu`
    are exactly the `f` satisfying `f ≡ f`, "which means that the function
    preserves the underlying equivalence relation" — which is `mapEquiv_refl`. -/
def MapEquiv {A B : PartialEquilogicalSpace.{u}} (f g : PEquivariant A B) : Prop :=
  ∀ x y : A.carrier, A.Rel x y → B.Rel (f.toFun x) (g.toFun y)

theorem mapEquiv_refl {A B : PartialEquilogicalSpace.{u}} (f : PEquivariant A B) :
    MapEquiv f f := fun _ _ h => f.equivariant h

theorem mapEquiv_symm {A B : PartialEquilogicalSpace.{u}} {f g : PEquivariant A B}
    (h : MapEquiv f g) : MapEquiv g f :=
  fun x y hxy => B.rel_symm (h y x (A.rel_symm hxy))

/-- Transitivity, with `A.Rel x x` supplied by `rel_refl_left` rather than by
    reflexivity — the whole reason this proof survives partiality. -/
theorem mapEquiv_trans {A B : PartialEquilogicalSpace.{u}} {f g h : PEquivariant A B}
    (h₁ : MapEquiv f g) (h₂ : MapEquiv g h) : MapEquiv f h :=
  fun x y hxy =>
    B.rel_trans (h₁ x x (PartialEquilogicalSpace.rel_refl_left hxy)) (h₂ x y hxy)

instance mapSetoid (A B : PartialEquilogicalSpace.{u}) : Setoid (PEquivariant A B) where
  r := MapEquiv
  iseqv := ⟨mapEquiv_refl, mapEquiv_symm, mapEquiv_trans⟩

/-- The identity equivariant map. -/
def id (A : PartialEquilogicalSpace.{u}) : PEquivariant A A where
  toFun := fun x => x
  continuous_toFun := continuous_id
  equivariant := fun h => h

/-- Composition of equivariant maps. -/
def comp {A B C : PartialEquilogicalSpace.{u}} (g : PEquivariant B C) (f : PEquivariant A B) :
    PEquivariant A C where
  toFun := fun x => g.toFun (f.toFun x)
  continuous_toFun := g.continuous_toFun.comp f.continuous_toFun
  equivariant := fun h => g.equivariant (f.equivariant h)

theorem comp_congr {A B C : PartialEquilogicalSpace.{u}}
    {g g' : PEquivariant B C} {f f' : PEquivariant A B}
    (hg : MapEquiv g g') (hf : MapEquiv f f') : MapEquiv (comp g f) (comp g' f') :=
  fun x y hxy => hg _ _ (hf x y hxy)

end PEquivariant

/-! ## The category `PEqu` -/

open CategoryTheory PEquivariant in
/-- **The category `PEqu`** (Definition 3.11). As in `Equ`, morphisms are
    `MapEquiv`-classes, so `Hom A B` is a `Quotient` and every law is an equality
    of classes. All four are proved. -/
instance pequCategory : LargeCategory PartialEquilogicalSpace.{u} where
  Hom A B := Quotient (mapSetoid A B)
  id A := Quotient.mk _ (PEquivariant.id A)
  comp f g := Quotient.map₂ (fun a b => PEquivariant.comp b a)
    (fun _ _ h₁ _ _ h₂ => comp_congr h₂ h₁) f g
  id_comp := by rintro A B ⟨f⟩; rfl
  comp_id := by rintro A B ⟨f⟩; rfl
  assoc := by rintro A B C D ⟨f⟩ ⟨g⟩ ⟨h⟩; rfl

/-! ## Theorems 3.6, 3.7 and 3.12 -/

section EmbeddingExtension

variable {X : Type u} [TopologicalSpace X]

/-- **Definition 3.1**: the neighbourhood filter `𝒯(x) = { U ∈ Ω_𝒯 ∣ x ∈ U }`,
    as an element of the powerset lattice `𝒫 Ω_𝒯`. -/
def nbhdFilter (x : X) : Set (Set X) := { U | IsOpen U ∧ x ∈ U }

/-- Two points with the same neighbourhood filter are inseparable — immediate,
    since `nbhdFilter x = nbhdFilter y` says exactly that every open set contains
    one iff it contains the other. -/
theorem inseparable_of_nbhdFilter_eq {x y : X} (h : nbhdFilter x = nbhdFilter y) :
    Inseparable x y :=
  inseparable_iff_forall_isOpen.mpr fun s hs =>
    ⟨fun hx => (Set.ext_iff.mp h s).mp ⟨hs, hx⟩ |>.2,
     fun hy => (Set.ext_iff.mp h s).mpr ⟨hs, hy⟩ |>.2⟩

/-- **Definition 3.2**, in the form the paper gives as the alternative reading of
    `T₀`: "for all `x, y ∈ |𝒯|`, if `𝒯(x) = 𝒯(y)`, then `x = y`".

    **Proved.** This is the injectivity half of the Embedding Theorem, and it is
    where — and the only place where — the `T₀` hypothesis is spent. -/
theorem nbhdFilter_injective [T0Space X] :
    Function.Injective (nbhdFilter : X → Set (Set X)) :=
  fun _ _ h => (inseparable_of_nbhdFilter_eq h).eq

/-- **Theorem 3.6 (The Embedding Theorem)**: for a `T₀`-space `𝒯`, the map
    `x ↦ 𝒯(x)` is a topological embedding of `𝒯` into `𝒫 Ω_𝒯` under the
    Σ-topology.

    Obligation — but now only the *topological* half. Injectivity is discharged
    above by `nbhdFilter_injective`, so what remains is that the map induces the
    topology: the Σ-open sets of `𝒫 Ω_𝒯` are exactly those of "finite
    character", which the paper describes as the product topology on `2^A` where
    the two-element set has one open and one closed point. With
    `sigmaOpen_iff_isOpen` now proved in `SigmaTopology.lean`, that side can be
    attacked through Definition 3.4's own wording rather than through Mathlib's
    directed-set formulation.

    This is one of the three Scott facts of 1970/71 that carry §3, and it is what
    makes Theorem 3.12's restriction functor essentially surjective. -/
theorem bauerBirkedalScott04_theorem_3_6_embedding [T0Space X]
    [TopologicalSpace (Set (Set X))] [IsScott (Set (Set X)) univ] :
    Topology.IsEmbedding (nbhdFilter : X → Set (Set X)) := by
  sorry

/-- **Theorem 3.7 (The Extension Theorem)**: if `𝒴` is a subspace of `𝒳` and
    `f : |𝒴| → 𝒫 A` is continuous, then `f` extends continuously to all of `𝒳`.

    Obligation. Stated for a subset `s ⊆ X` with the subspace topology. The paper
    notes the result in fact holds for every continuous retract of a powerset —
    the continuous lattices — but that the powerset case suffices here.

    This is what makes Theorem 3.12's restriction functor **full**. -/
theorem bauerBirkedalScott04_theorem_3_7_extension {A : Type u}
    [TopologicalSpace (Set A)] [IsScott (Set A) univ]
    (s : Set X) (f : s → Set A) (hf : Continuous f) :
    ∃ g : X → Set A, Continuous g ∧ ∀ y : s, g y = f y := by
  sorry

end EmbeddingExtension

/-- **Theorem 3.12**: the categories `Equ` and `PEqu` are equivalent.

    Obligation, and the hinge of the whole section. The paper's functor
    `R : PEqu → Equ` restricts a partial equilogical space to its total part
    `{ x ∣ x ≡ x }` with the subspace topology, on which the relation becomes
    total. Then:

    * `R` is **faithful** by definition;
    * `R` is **full** by Theorem 3.7, since a continuous map between `T₀`-spaces
      extends to any algebraic lattices embedding them;
    * `R` is **essentially surjective** by Theorem 3.6 — and note that the
      equivalence relation on the `T₀`-space does not have to be extended, it
      remains partial.

    Theorem 3.13 is proved by transporting cartesian closure of `PEqu` across
    this equivalence, so discharging 3.13 honestly means discharging this
    first. -/
theorem bauerBirkedalScott04_theorem_3_12 :
    Nonempty (CategoryTheory.Equivalence PartialEquilogicalSpace.{u} EquilogicalSpace.{u}) := by
  sorry

end ScottDomains.EquilogicalSpaces
