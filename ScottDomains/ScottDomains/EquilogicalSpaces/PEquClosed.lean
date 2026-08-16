import ScottDomains.EquilogicalSpaces.CartesianClosure
import ScottDomains.EquilogicalSpaces.ALatClosed
import ScottDomains.EquilogicalSpaces.PowersetRetract
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts

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

/-! ## A protected carrier

    `Wrap` is a type synonym in the manner of Mathlib's `WithScott` and
    `WithLower`, and it exists for one reason: **instance lookup keys**.

    A carrier that reduces to `A.carrier × B.carrier` has discrimination key
    `Prod _ _`, and `PartialEquilogicalSpace.isScott` is keyed on
    `PartialEquilogicalSpace.carrier _`. Once the goal's key has reduced past the
    projection, that instance is never considered — synthesis fails even though
    the term discharges the goal by hand (r0077 measured exactly this).

    Because `Wrap α` is a plain `def`, it is *definitionally* `α`, so every
    instance transports by identity — `‹CompleteLattice α›` and friends, no
    construction and no proof obligations. But because it is **not reducible**,
    the ambient `Prod` instances are not candidates on it, and the instances
    declared here are found instead.

    ## Two changes are needed, and each was verified necessary by deleting it

    `Wrap` alone is not enough, and `@[reducible]` alone is not enough:

    * **`@[reducible]` on `prod`.** Instance resolution runs at `instances`
      transparency, which does not unfold a plain `def`. Without it, matching
      `PartialEquilogicalSpace.isScott` against the goal requires comparing
      `(A.prod B).topologicalSpace` with the ambient candidate, and resolution
      cannot unfold `prod` far enough to do so — synthesis fails even though the
      term `(A.prod B).isScott` discharges the goal by hand at default
      transparency. This is what r0075–r0077 kept failing to name.
    * **`Wrap` on the carrier.** Removing it while keeping `@[reducible]` was
      tried: the carrier reduces to a bare `A.carrier × B.carrier`, the ambient
      product instances become candidates again, and the module fails with
      nineteen errors starting at the object's own `IsScott` field.

    So the two are complementary — `@[reducible]` lets resolution *reach* the
    carrier, `Wrap` controls *what it finds there*. -/

def Wrap (α : Type u) : Type u := α

instance [CompleteLattice α] : CompleteLattice (Wrap α) := ‹CompleteLattice α›

instance [CompleteLattice α] [ScottDomains.IsAlgebraic α] :
    ScottDomains.IsAlgebraic (Wrap α) := ‹ScottDomains.IsAlgebraic α›

instance [CompleteLattice α] : TopologicalSpace (Wrap α) :=
  Topology.scott (Wrap α) Set.univ

instance [CompleteLattice α] : Topology.IsScott (Wrap α) Set.univ := ⟨rfl⟩

/-! ## The product object -/

/-- The binary product of two partial equilogical spaces: the product lattice,
    behind `Wrap`, with the componentwise partial equivalence relation.

    `Wrap` costs nothing definitionally — `ProdRel A.Rel B.Rel` is accepted here
    unchanged, because `Wrap (|𝒜| × |ℬ|)` *is* `|𝒜| × |ℬ|` — and it is what makes
    the projections below typecheck at all. -/
@[reducible] def PartialEquilogicalSpace.prod (A B : PartialEquilogicalSpace.{u}) :
    PartialEquilogicalSpace.{u} where
  carrier := Wrap (A.carrier × B.carrier)
  Rel := ProdRel A.Rel B.Rel
  rel_symm := fun h => ⟨A.rel_symm h.1, B.rel_symm h.2⟩
  rel_trans := fun h₁ h₂ => ⟨A.rel_trans h₁.1 h₂.1, B.rel_trans h₁.2 h₂.2⟩

/-! ## The exponential object -/

/-- The exponential of two partial equilogical spaces: the algebraic lattice of
    Scott-continuous maps, with the partial equivalence relation of Definition
    3.11(2). -/
@[reducible] noncomputable def PartialEquilogicalSpace.exp
    (A B : PartialEquilogicalSpace.{u}) : PartialEquilogicalSpace.{u} where
  carrier := Wrap (ScottHom A.carrier B.carrier)
  Rel := HomRel A.Rel B.Rel
  rel_symm := fun h => fun x y hxy =>
    B.rel_symm (h y x (A.rel_symm hxy))
  rel_trans := fun h₁ h₂ => fun x y hxy =>
    B.rel_trans (h₁ x x (A.rel_trans hxy (A.rel_symm hxy))) (h₂ x y hxy)

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

/-! ## The product cone in `PEqu`

    With the carrier behind `Wrap`, `Topology.IsScott (A.prod B).carrier Set.univ`
    is found by synthesis and the cone goes through. Each Scott-continuity fact
    is still stated at the object's carrier first, so that unification does not
    pin the domain to a bare product via the ambient `Prod` instances before the
    goal's own are consulted. -/

namespace PartialEquilogicalSpace

theorem scottContinuous_fst (A B : PartialEquilogicalSpace.{u}) :
    ScottContinuous (Prod.fst : (A.prod B).carrier → A.carrier) :=
  ScottContinuous.fst

theorem scottContinuous_snd (A B : PartialEquilogicalSpace.{u}) :
    ScottContinuous (Prod.snd : (A.prod B).carrier → B.carrier) :=
  ScottContinuous.snd

theorem scottContinuous_pair {T A B : PartialEquilogicalSpace.{u}}
    (f : PEquivariant T A) (g : PEquivariant T B) :
    ScottContinuous (fun t : T.carrier => ((f.toFun t, g.toFun t) : (A.prod B).carrier)) :=
  ScottContinuous.prodMk (scottContinuous_of_continuous f.continuous_toFun)
    (scottContinuous_of_continuous g.continuous_toFun)

/-- First projection. -/
def prodFst (A B : PartialEquilogicalSpace.{u}) : PEquivariant (A.prod B) A where
  toFun := Prod.fst
  continuous_toFun := continuous_of_scottContinuous (scottContinuous_fst A B)
  equivariant := fun h => h.1

/-- Second projection. -/
def prodSnd (A B : PartialEquilogicalSpace.{u}) : PEquivariant (A.prod B) B where
  toFun := Prod.snd
  continuous_toFun := continuous_of_scottContinuous (scottContinuous_snd A B)
  equivariant := fun h => h.2

/-- The pairing of two equivariant maps. -/
def prodLift {T A B : PartialEquilogicalSpace.{u}}
    (f : PEquivariant T A) (g : PEquivariant T B) : PEquivariant T (A.prod B) where
  toFun := fun t => (f.toFun t, g.toFun t)
  continuous_toFun := continuous_of_scottContinuous (scottContinuous_pair f g)
  equivariant := fun h => ⟨f.equivariant h, g.equivariant h⟩

/-- Pairing respects `MapEquiv` in both arguments, so it descends to the
    quotient — the step with no counterpart in `ALatProducts.lean`, where
    morphisms are functions rather than classes. -/
theorem prodLift_congr {T A B : PartialEquilogicalSpace.{u}}
    {f f' : PEquivariant T A} {g g' : PEquivariant T B}
    (hf : PEquivariant.MapEquiv f f') (hg : PEquivariant.MapEquiv g g') :
    PEquivariant.MapEquiv (prodLift f g) (prodLift f' g') :=
  fun x y hxy => ⟨hf x y hxy, hg x y hxy⟩

theorem prodFst_comp_prodLift {T A B : PartialEquilogicalSpace.{u}}
    (f : PEquivariant T A) (g : PEquivariant T B) :
    PEquivariant.comp (prodFst A B) (prodLift f g) = f := rfl

theorem prodSnd_comp_prodLift {T A B : PartialEquilogicalSpace.{u}}
    (f : PEquivariant T A) (g : PEquivariant T B) :
    PEquivariant.comp (prodSnd A B) (prodLift f g) = g := rfl

/-- Uniqueness up to `MapEquiv`: a map into the product is determined by its two
    components. -/
theorem prodLift_unique {T A B : PartialEquilogicalSpace.{u}}
    (m : PEquivariant T (A.prod B)) {f : PEquivariant T A} {g : PEquivariant T B}
    (h₁ : PEquivariant.MapEquiv (PEquivariant.comp (prodFst A B) m) f)
    (h₂ : PEquivariant.MapEquiv (PEquivariant.comp (prodSnd A B) m) g) :
    PEquivariant.MapEquiv m (prodLift f g) :=
  fun x y hxy => ⟨h₁ x y hxy, h₂ x y hxy⟩

end PartialEquilogicalSpace

/-! ## The cone as a Mathlib limit

    Every obligation here is an equality of `MapEquiv`-**classes**, so each one
    is discharged by inducting on representatives and then applying the
    corresponding equation between `PEquivariant` maps. That is the difference
    from `ALatProducts.lean`, where morphisms are functions and the same
    obligations were `rfl`. -/

open CategoryTheory CategoryTheory.Limits

/-- The binary fan on `𝒜 × ℬ` in `PEqu`. -/
def pequProdFan (A B : PartialEquilogicalSpace.{u}) : BinaryFan A B :=
  BinaryFan.mk (P := A.prod B)
    (Quotient.mk _ (PartialEquilogicalSpace.prodFst A B))
    (Quotient.mk _ (PartialEquilogicalSpace.prodSnd A B))

/-- The fan is a limit. -/
def pequProdIsLimit (A B : PartialEquilogicalSpace.{u}) :
    IsLimit (pequProdFan A B) :=
  BinaryFan.isLimitMk
    (fun s => Quotient.map₂ PartialEquilogicalSpace.prodLift
      (fun _ _ hf _ _ hg => PartialEquilogicalSpace.prodLift_congr hf hg)
      (BinaryFan.fst s) (BinaryFan.snd s))
    (fun s => by
      refine Quotient.inductionOn₂ (BinaryFan.fst s) (BinaryFan.snd s)
        (fun f g => ?_)
      exact congrArg (Quotient.mk _)
        (PartialEquilogicalSpace.prodFst_comp_prodLift f g))
    (fun s => by
      refine Quotient.inductionOn₂ (BinaryFan.fst s) (BinaryFan.snd s)
        (fun f g => ?_)
      exact congrArg (Quotient.mk _)
        (PartialEquilogicalSpace.prodSnd_comp_prodLift f g))
    (fun s m h₁ h₂ => by
      revert h₁ h₂
      refine Quotient.inductionOn m (fun m => ?_)
      refine Quotient.inductionOn₂ (BinaryFan.fst s) (BinaryFan.snd s)
        (fun f g => ?_)
      intro h₁ h₂
      exact Quotient.sound
        (PartialEquilogicalSpace.prodLift_unique m
          (Quotient.exact h₁) (Quotient.exact h₂)))

instance pequHasLimitPair (A B : PartialEquilogicalSpace.{u}) : HasLimit (pair A B) :=
  HasLimit.mk ⟨pequProdFan A B, pequProdIsLimit A B⟩

instance : HasBinaryProducts PartialEquilogicalSpace.{u} :=
  hasBinaryProducts_of_hasLimit_pair _

/-! ## The exponential functor

    Object part is `exp`; morphism part is post-composition. Two things have to
    be checked that have no counterpart in `ALatClosed.lean`: that a `PEqu`
    morphism's *topological* continuity gives the *Scott* continuity the function
    space needs, and that post-composition respects `MapEquiv` so that it
    descends to the quotient. -/

/-- A `PEqu` morphism's underlying map, bundled as a `ScottHom`. Declared outside
    the `PartialEquilogicalSpace` namespace so that dot notation on a
    `PEquivariant` finds it. -/
noncomputable def PEquivariant.toScottHom {A B : PartialEquilogicalSpace.{u}}
    (f : PEquivariant A B) : ScottHom A.carrier B.carrier :=
  ⟨f.toFun, scottContinuous_of_continuous f.continuous_toFun⟩

namespace PartialEquilogicalSpace

/-- Post-composition with `f`, as an equivariant map `(B ⟹ Y) ⟶ (B ⟹ Z)`.

    Continuity is `scottContinuous_postcomp` (r0064). Equivariance is one step:
    if `g₁ ≈ g₂` in `B ⟹ Y` then at `≡`-related `x`, `y` we get
    `g₁ x ≈_Y g₂ y`, and `f` carries that to `f (g₁ x) ≈_Z f (g₂ y)`. -/
noncomputable def expMap (B : PartialEquilogicalSpace.{u})
    {Y Z : PartialEquilogicalSpace.{u}} (f : PEquivariant Y Z) :
    PEquivariant (B.exp Y) (B.exp Z) where
  toFun := fun g => Combinator.comp f.toScottHom g
  continuous_toFun :=
    continuous_of_scottContinuous (scottContinuous_postcomp f.toScottHom)
  equivariant := fun h x y hxy => f.equivariant (h x y hxy)

/-- Post-composition respects `MapEquiv`, so it descends to the quotient. -/
theorem expMap_congr (B : PartialEquilogicalSpace.{u})
    {Y Z : PartialEquilogicalSpace.{u}} {f f' : PEquivariant Y Z}
    (hf : PEquivariant.MapEquiv f f') :
    PEquivariant.MapEquiv (expMap B f) (expMap B f') := by
  intro g₁ g₂ h x y hxy
  exact hf _ _ (h x y hxy)

end PartialEquilogicalSpace

open CategoryTheory in
/-- **The exponential functor `B ⟹ -` on `PEqu`.** -/
noncomputable def pequExpFunctor (B : PartialEquilogicalSpace.{u}) :
    PartialEquilogicalSpace.{u} ⥤ PartialEquilogicalSpace.{u} where
  obj Y := B.exp Y
  map f := Quotient.map (PartialEquilogicalSpace.expMap B)
    (fun _ _ h => PartialEquilogicalSpace.expMap_congr B h) f
  map_id := by
    rintro Y
    exact Quotient.sound (fun _ _ h => h)
  map_comp := by
    rintro X Y Z ⟨f⟩ ⟨g⟩
    exact Quotient.sound
      (fun _ _ h x y hxy => g.equivariant (f.equivariant (h x y hxy)))

/-! ## The product functor `- × B` -/

namespace PartialEquilogicalSpace

/-- `f × B`, the action of `- × B` on a morphism. -/
noncomputable def prodMapRight (B : PartialEquilogicalSpace.{u})
    {X Y : PartialEquilogicalSpace.{u}} (f : PEquivariant X Y) :
    PEquivariant (X.prod B) (Y.prod B) :=
  prodLift (PEquivariant.comp f (prodFst X B)) (prodSnd X B)

theorem prodMapRight_congr (B : PartialEquilogicalSpace.{u})
    {X Y : PartialEquilogicalSpace.{u}} {f f' : PEquivariant X Y}
    (hf : PEquivariant.MapEquiv f f') :
    PEquivariant.MapEquiv (prodMapRight B f) (prodMapRight B f') :=
  fun _ _ h => ⟨hf _ _ h.1, h.2⟩

end PartialEquilogicalSpace

open CategoryTheory in
/-- **The functor `- × B` on `PEqu`**, with object part `prod` on the nose. -/
noncomputable def pequProdFunctorRight (B : PartialEquilogicalSpace.{u}) :
    PartialEquilogicalSpace.{u} ⥤ PartialEquilogicalSpace.{u} where
  obj X := X.prod B
  map f := Quotient.map (PartialEquilogicalSpace.prodMapRight B)
    (fun _ _ h => PartialEquilogicalSpace.prodMapRight_congr B h) f
  map_id := by
    rintro X
    exact Quotient.sound (fun _ _ h => h)
  map_comp := by
    rintro X Y Z ⟨f⟩ ⟨g⟩
    exact Quotient.sound (fun _ _ h => ⟨g.equivariant (f.equivariant h.1), h.2⟩)

/-! ## Currying and uncurrying `PEqu` morphisms

    The bijection `(𝒜 × ℬ ⟶ 𝒞) ≃ (𝒜 ⟶ ℬ ⟹ 𝒞)` at the level of representatives.
    The underlying order isomorphism is `ScottDomains.Currying.scottHomCurry`;
    what is added here is that both directions are equivariant, and that both
    respect `MapEquiv` so they descend to the quotient. -/

namespace PartialEquilogicalSpace

/-- Currying a representative. -/
noncomputable def pequCurry {X B Y : PartialEquilogicalSpace.{u}}
    (F : PEquivariant (X.prod B) Y) : PEquivariant X (B.exp Y) where
  toFun := ScottHom.curry F.toScottHom
  continuous_toFun :=
    continuous_of_scottContinuous (ScottHom.curry F.toScottHom).scottContinuous
  equivariant := fun hxy _ _ hbb' => F.equivariant ⟨hxy, hbb'⟩

/-- Uncurrying a representative. -/
noncomputable def pequUncurry {X B Y : PartialEquilogicalSpace.{u}}
    (G : PEquivariant X (B.exp Y)) : PEquivariant (X.prod B) Y where
  toFun := ScottHom.uncurry G.toScottHom
  continuous_toFun :=
    continuous_of_scottContinuous (ScottHom.uncurry G.toScottHom).scottContinuous
  equivariant := fun h => G.equivariant h.1 _ _ h.2

/-- Both sides of the correspondence unpack to the same statement — the paper's
    "self-proving" step, now at the level of `MapEquiv` between morphisms rather
    than `HomRel` inside one function space. -/
theorem pequCurry_congr {X B Y : PartialEquilogicalSpace.{u}}
    {F F' : PEquivariant (X.prod B) Y} (h : PEquivariant.MapEquiv F F') :
    PEquivariant.MapEquiv (pequCurry F) (pequCurry F') :=
  fun _ _ hxy _ _ hbb' => h _ _ ⟨hxy, hbb'⟩

theorem pequUncurry_congr {X B Y : PartialEquilogicalSpace.{u}}
    {G G' : PEquivariant X (B.exp Y)} (h : PEquivariant.MapEquiv G G') :
    PEquivariant.MapEquiv (pequUncurry G) (pequUncurry G') :=
  fun _ _ hpq => h _ _ hpq.1 _ _ hpq.2

@[simp] theorem pequUncurry_pequCurry {X B Y : PartialEquilogicalSpace.{u}}
    (F : PEquivariant (X.prod B) Y) : pequUncurry (pequCurry F) = F := rfl

@[simp] theorem pequCurry_pequUncurry {X B Y : PartialEquilogicalSpace.{u}}
    (G : PEquivariant X (B.exp Y)) : pequCurry (pequUncurry G) = G := rfl

end PartialEquilogicalSpace

/-! ## Theorem 3.13 for `PEqu` -/

open CategoryTheory in
/-- **`PEqu` is cartesian closed**: `(- × B) ⊣ (B ⟹ -)`.

    This is the paper's Theorem 3.13, proved where the paper proves it. The
    hom-equivalence is `pequCurry`/`pequUncurry` descended to classes; both
    round-trips are `rfl`, because the underlying `scottHomCurry` is an
    isomorphism on the nose and currying a pair is definitional.

    Both naturality squares are equalities of classes and both hold on
    representatives — the two sides evaluate a curried map at the same point in
    each case. -/
noncomputable def pequProdExpAdjunction (B : PartialEquilogicalSpace.{u}) :
    pequProdFunctorRight B ⊣ pequExpFunctor B :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun _ _ =>
        { toFun := Quotient.map PartialEquilogicalSpace.pequCurry
            (fun _ _ h => PartialEquilogicalSpace.pequCurry_congr h)
          invFun := Quotient.map PartialEquilogicalSpace.pequUncurry
            (fun _ _ h => PartialEquilogicalSpace.pequUncurry_congr h)
          left_inv := by rintro ⟨F⟩; rfl
          right_inv := by rintro ⟨G⟩; rfl }
      homEquiv_naturality_left_symm := by
        rintro X' X Y ⟨f⟩ ⟨g⟩
        exact Quotient.sound (fun _ _ h => g.equivariant (f.equivariant h.1) _ _ h.2)
      homEquiv_naturality_right := by
        rintro X Y Y' ⟨f⟩ ⟨g⟩
        exact Quotient.sound
          (fun _ _ hxy _ _ hbb' => g.equivariant (f.equivariant ⟨hxy, hbb'⟩)) }

/-- **Theorem 3.13 for `PEqu`**, in the paper's §2 phrasing: `- × B` is a left
    adjoint for every `B`. -/
theorem bauerBirkedalScott04_theorem_3_13_pequ (B : PartialEquilogicalSpace.{u}) :
    CategoryTheory.Functor.IsLeftAdjoint (pequProdFunctorRight B) :=
  ⟨⟨_, ⟨pequProdExpAdjunction B⟩⟩⟩

end ScottDomains.EquilogicalSpaces
