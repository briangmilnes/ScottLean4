import ScottDomains.EquilogicalSpaces.SigmaTopology
import ScottDomains.EquilogicalSpaces.Extension
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

    **Proved.** The subbasic preimage is the key computation:

        nbhdFilter ⁻¹' (memSet U) = { x | IsOpen U ∧ x ∈ U }

    which is `U` when `U` is open and `∅` otherwise — open either way. So
    `continuous_of_preimage_memSet` gives continuity, and the same computation
    read backwards exhibits every open `U` of `𝒯` as a preimage, which is the
    other half of inducing. Injectivity is `nbhdFilter_injective`, where the `T₀`
    hypothesis is spent.

    This is one of the three Scott facts of 1970/71 that carry §3, and it is what
    makes Theorem 3.12's restriction functor essentially surjective. -/
theorem nbhdFilter_preimage_memSet
    [TopologicalSpace (Set (Set X))] [IsScott (Set (Set X)) univ] (U : Set X) :
    (nbhdFilter : X → Set (Set X)) ⁻¹' memSet U = { x | IsOpen U ∧ x ∈ U } := rfl

theorem isOpen_nbhdFilter_preimage_memSet
    [TopologicalSpace (Set (Set X))] [IsScott (Set (Set X)) univ] (U : Set X) :
    IsOpen ((nbhdFilter : X → Set (Set X)) ⁻¹' memSet U) := by
  rw [nbhdFilter_preimage_memSet]
  by_cases hU : IsOpen U
  · simp [hU]
  · simp [hU]

theorem continuous_nbhdFilter
    [TopologicalSpace (Set (Set X))] [IsScott (Set (Set X)) univ] :
    Continuous (nbhdFilter : X → Set (Set X)) :=
  continuous_of_preimage_memSet _ isOpen_nbhdFilter_preimage_memSet

theorem bauerBirkedalScott04_theorem_3_6_embedding [T0Space X]
    [TopologicalSpace (Set (Set X))] [IsScott (Set (Set X)) univ] :
    Topology.IsEmbedding (nbhdFilter : X → Set (Set X)) := by
  refine ⟨⟨le_antisymm ?_ ?_⟩, nbhdFilter_injective⟩
  · -- Every induced-open set is open: this is continuity.
    exact continuous_nbhdFilter.le_induced
  · -- Every open `U` is a preimage, namely of `memSet U`.
    intro U hU
    exact ⟨memSet U, isOpen_memSet U, by
      rw [nbhdFilter_preimage_memSet]
      ext x
      simp [hU]⟩

/-- **Theorem 3.7 (The Extension Theorem)**: if `𝒴` is a subspace of `𝒳` and
    `f : |𝒴| → 𝒫 A` is continuous, then `f` extends continuously to all of `𝒳`.

    **Proved**, in `Extension.lean`; restated here under the paper's number so
    that §3 reads in order. The extension is `g x = { a | x ∈ V a }` with `V a`
    an open set cutting out `f ⁻¹' { S | a ∈ S }` on the subspace, and continuity
    is the finite-character property of Σ-open sets.

    This is what makes Theorem 3.12's restriction functor **full**. -/
theorem bauerBirkedalScott04_theorem_3_7_extension {A : Type u}
    [TopologicalSpace (Set A)] [IsScott (Set A) univ]
    (s : Set X) (f : s → Set A) (hf : Continuous f) :
    ∃ g : X → Set A, Continuous g ∧ ∀ y : s, g y = f y :=
  bauerBirkedalScott04_theorem_3_7 s f hf

end EmbeddingExtension

/-! ## Theorem 3.12

    **Proved**, in `EssSurj.lean`, and not restated here: it needs the
    restriction functor `R : PEqu ⥤ Equ`, which is built in `Restriction.lean`
    downstream of this module, so the statement cannot be phrased at this point
    in the import order.

    The paper's proof structure, and where each piece lives:

    * `R` is **faithful** by definition — `Restriction.lean`;
    * `R` is **full** by the Extension Theorem in its algebraic-lattice form —
      `Restriction.lean`, on `PowersetRetract.lean`;
    * `R` is **essentially surjective** by the Embedding Theorem 3.6 above —
      `EssSurj.lean`. -/

end ScottDomains.EquilogicalSpaces
