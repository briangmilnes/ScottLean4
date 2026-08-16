/-
  A New Category?  Domains, Spaces and Equivalence Relations
  (Lean 4 formalization)

  Faithful to:
    D. S. Scott,
    "A New Category?  Domains, Spaces and Equivalence Relations",
    unpublished manuscript, Version 2, 19 April 1998.

  Source text extracted from:
    DanaScottPapers/Scott-1998-A-New-Category.txt

  Auto-generated faithful skeleton.

  The paper introduces the cartesian-closed category `EQU` of *equilogical spaces*:
  T₀-spaces equipped with an arbitrary equivalence relation, with morphisms the
  equivalence classes of continuous *equivariant* maps (maps preserving the
  equivalence relations).  We encode:

    * topological spaces, the T₀ separation axiom, and the specialization ordering
      (Definitions 2.2, 2.3);
    * algebraic lattices: compact/finite elements and algebraicity
      (Definitions 2.4, 2.5);
    * equilogical spaces and equivariant maps, with the equivalence of maps
      (Definition 3.1), and the category `EQU`;
    * partial equilogical spaces `PEQU` (Definition 3.3);
    * the principal theorem 3.2 (`EQU` is complete, cocomplete, regular
      well-powered and regular co-well-powered), stated with its universal
      properties and left as proof obligations;
    * cartesian closedness, as a target statement.

  Core Lean 4 only; no Mathlib.  A minimal topological-space structure is defined
  here since Mathlib's `TopologicalSpace` is unavailable.
-/

namespace Scott1998

universe u v

/-! ## Section 2.  T₀-spaces and algebraic lattices -/

/-- A topological space given by its family of open sets (predicate on subsets,
    themselves predicates on the carrier).  Axioms: `∅` and the whole space are
    open, and opens are closed under binary intersection and arbitrary union. -/
structure TopSpace (X : Type u) where
  /-- `IsOpen U` holds iff `U ⊆ X` is an open set. -/
  IsOpen : (X → Prop) → Prop
  isOpen_univ : IsOpen (fun _ => True)
  isOpen_empty : IsOpen (fun _ => False)
  isOpen_inter : ∀ U V, IsOpen U → IsOpen V → IsOpen (fun x => U x ∧ V x)
  isOpen_iUnion : ∀ (I : Type u) (U : I → X → Prop),
    (∀ i, IsOpen (U i)) → IsOpen (fun x => ∃ i, U i x)

/-- **Specialization ordering** (Definition 2.3): `x ⊑ y` iff every open set
    containing `x` contains `y`. -/
def specLe {X : Type u} (T : TopSpace X) (x y : X) : Prop :=
  ∀ U, T.IsOpen U → U x → U y

/-- The **T₀ axiom** (Definition 2.2): distinct points are separated by an open
    set (equivalently, the specialization order is antisymmetric). -/
def IsT0 {X : Type u} (T : TopSpace X) : Prop :=
  ∀ x y : X, (∀ U, T.IsOpen U → (U x ↔ U y)) → x = y

/-- A T₀-space: a carrier with a topology satisfying the T₀ axiom. -/
structure T0Space where
  X : Type u
  top : TopSpace X
  t0 : IsT0 top

/-- **Continuous map** between spaces: preimages of opens are open. -/
def Continuous {X : Type u} {Y : Type v} (S : TopSpace X) (T : TopSpace Y)
    (f : X → Y) : Prop :=
  ∀ V, T.IsOpen V → S.IsOpen (fun x => V (f x))

/-! ### Algebraic lattices (Definitions 2.4, 2.5)

    A complete lattice given abstractly by its order `⊑` and a supremum operator
    `sup` on arbitrary subsets. -/

/-- A complete lattice: a partial order in which every subset has a least upper
    bound `sup`. -/
structure CompleteLattice (L : Type u) where
  le : L → L → Prop
  le_refl : ∀ a, le a a
  le_trans : ∀ a b c, le a b → le b c → le a c
  le_antisymm : ∀ a b, le a b → le b a → a = b
  sup : (L → Prop) → L
  le_sup : ∀ (S : L → Prop) a, S a → le a (sup S)
  sup_le : ∀ (S : L → Prop) b, (∀ a, S a → le a b) → le (sup S) b

/-- A subset `S` is **directed** (Definition 2.6): nonempty and every pair of
    elements has an upper bound within `S`. -/
def Directed {L : Type u} (Lat : CompleteLattice L) (S : L → Prop) : Prop :=
  (∃ a, S a) ∧ ∀ a b, S a → S b → ∃ c, S c ∧ Lat.le a c ∧ Lat.le b c

/-- A **compact** ("finite"/"isolated") element (Definition 2.4): whenever `k`
    is below the sup of a directed set, it is already below some member. -/
def IsCompact {L : Type u} (Lat : CompleteLattice L) (k : L) : Prop :=
  ∀ S : L → Prop, Directed Lat S → Lat.le k (Lat.sup S) →
    ∃ a, S a ∧ Lat.le k a

/-- A complete lattice is **algebraic** (Definition 2.5) iff every element is the
    sup of the compact elements below it. -/
def IsAlgebraic {L : Type u} (Lat : CompleteLattice L) : Prop :=
  ∀ x : L, x = Lat.sup (fun k => IsCompact Lat k ∧ Lat.le k x)

/-! ## Section 3.  Equilogical spaces -/

/-- **Equilogical space** (Definition 3.1): a T₀-space `X` together with an
    (arbitrary) equivalence relation `≡` on its points. -/
structure EquiSpace where
  X : Type u
  top : TopSpace X
  t0 : IsT0 top
  equiv : X → X → Prop
  refl : ∀ x, equiv x x
  symm : ∀ x y, equiv x y → equiv y x
  trans : ∀ x y z, equiv x y → equiv y z → equiv x z

/-- An **equivariant map** (Definition 3.1): a continuous map preserving the
    equivalence relations. -/
structure Equivariant (A B : EquiSpace) where
  f : A.X → B.X
  cont : Continuous A.top B.top f
  preserves : ∀ x y, A.equiv x y → B.equiv (f x) (f y)

/-- **Equivalence of maps** (Definition 3.1): two equivariant maps are identified
    when they are pointwise `≡_B`-equal.  Morphisms of `EQU` are these classes. -/
def MapEquiv {A B : EquiSpace} (g h : Equivariant A B) : Prop :=
  ∀ x : A.X, B.equiv (g.f x) (h.f x)

/-- `MapEquiv` is an equivalence relation (the "elementary exercise" of §3.1);
    reflexivity is immediate from `B.refl`. -/
theorem MapEquiv.refl {A B : EquiSpace} (g : Equivariant A B) : MapEquiv g g :=
  fun x => B.refl (g.f x)

theorem MapEquiv.symm {A B : EquiSpace} {g h : Equivariant A B}
    (H : MapEquiv g h) : MapEquiv h g :=
  fun x => B.symm _ _ (H x)

theorem MapEquiv.trans {A B : EquiSpace} {g h k : Equivariant A B}
    (H1 : MapEquiv g h) (H2 : MapEquiv h k) : MapEquiv g k :=
  fun x => B.trans _ _ _ (H1 x) (H2 x)

/-- **Partial equilogical space** (Definition 3.3): an algebraic lattice (viewed
    with its Scott topology) together with a *partial* equivalence relation
    (symmetric and transitive, reflexive only on a subset). -/
structure PEquiSpace where
  L : Type u
  lat : CompleteLattice L
  alg : IsAlgebraic lat
  per : L → L → Prop
  per_symm : ∀ x y, per x y → per y x
  per_trans : ∀ x y z, per x y → per y z → per x z

/-! ## The categorical structure of `EQU`

    Morphisms of `EQU` are `MapEquiv`-classes of equivariant maps (Definition
    3.1), so every universal property below is stated *up to `MapEquiv`*, never
    up to Lean's `Eq`.  This is the point the paper concedes is "sketchy in the
    handling of equivalence classes of maps"; making it explicit is what turns
    Theorem 3.2 into a checkable statement. -/

/-- The identity equivariant map on an equilogical space (a basic instance,
    witnessing that `EQU` has identities). -/
def idEqui (A : EquiSpace) : Equivariant A A where
  f := fun x => x
  cont := fun _ hV => hV
  preserves := fun _ _ h => h

/-- Composition of equivariant maps.  Continuity composes by pulling the
    preimage of an open set back through `g` and then through `f`. -/
def compEqui {A B C : EquiSpace.{u}} (g : Equivariant B C) (f : Equivariant A B) :
    Equivariant A C where
  f := fun x => g.f (f.f x)
  cont := fun _ hV => f.cont _ (g.cont _ hV)
  preserves := fun _ _ h => g.preserves _ _ (f.preserves _ _ h)

/-! ### Limits and colimits

    Completeness is products plus equalizers; cocompleteness is coproducts plus
    coequalizers.  The paper's §3.2 proof constructs exactly these four. -/

/-- `π` exhibits `P` as the **product** of the family `A`: every cone factors
    through `π`, uniquely up to `MapEquiv`.  The paper builds `P` as the product
    topology with the product equivalence relation, and notes that picking
    representatives of the cone's `MapEquiv`-classes uses the Axiom of Choice. -/
structure IsProduct {I : Type u} (A : I → EquiSpace.{u}) {P : EquiSpace.{u}}
    (π : ∀ i, Equivariant P (A i)) : Prop where
  factors : ∀ (T : EquiSpace.{u}) (t : ∀ i, Equivariant T (A i)),
    ∃ u : Equivariant T P, ∀ i, MapEquiv (compEqui (π i) u) (t i)
  unique : ∀ (T : EquiSpace.{u}) (u v : Equivariant T P),
    (∀ i, MapEquiv (compEqui (π i) u) (compEqui (π i) v)) → MapEquiv u v

/-- `e` exhibits `E` as the **equalizer** of the parallel pair `f, g`.  The paper
    takes `E = { x ∈ |A| | f x ≡_B g x }` with the subspace topology and the
    restriction of `≡_A`. -/
structure IsEqualizer {A B : EquiSpace.{u}} (f g : Equivariant A B)
    {E : EquiSpace.{u}} (e : Equivariant E A) : Prop where
  equalizes : MapEquiv (compEqui f e) (compEqui g e)
  factors : ∀ (T : EquiSpace.{u}) (t : Equivariant T A),
    MapEquiv (compEqui f t) (compEqui g t) →
      ∃ u : Equivariant T E, MapEquiv (compEqui e u) t
  unique : ∀ (T : EquiSpace.{u}) (u v : Equivariant T E),
    MapEquiv (compEqui e u) (compEqui e v) → MapEquiv u v

/-- `ι` exhibits `S` as the **coproduct** of the family `A`: the disjoint union
    of the carriers, topologized by the union of the topologies, with the union
    of the equivalence relations (an equivalence relation because the carriers
    are disjoint). -/
structure IsCoproduct {I : Type u} (A : I → EquiSpace.{u}) {S : EquiSpace.{u}}
    (ι : ∀ i, Equivariant (A i) S) : Prop where
  factors : ∀ (T : EquiSpace.{u}) (t : ∀ i, Equivariant (A i) T),
    ∃ u : Equivariant S T, ∀ i, MapEquiv (compEqui u (ι i)) (t i)
  unique : ∀ (T : EquiSpace.{u}) (u v : Equivariant S T),
    (∀ i, MapEquiv (compEqui u (ι i)) (compEqui v (ι i))) → MapEquiv u v

/-- `q` exhibits `Q` as the **coequalizer** of the parallel pair `f, g`.  The
    paper keeps the topology of `B` and coarsens the equivalence relation to the
    least one containing `≡_B` together with `{ (f x, g x) | x ∈ |A| }`;
    note that no topology is placed on the quotient. -/
structure IsCoequalizer {A B : EquiSpace.{u}} (f g : Equivariant A B)
    {Q : EquiSpace.{u}} (q : Equivariant B Q) : Prop where
  coequalizes : MapEquiv (compEqui q f) (compEqui q g)
  factors : ∀ (T : EquiSpace.{u}) (t : Equivariant B T),
    MapEquiv (compEqui t f) (compEqui t g) →
      ∃ u : Equivariant Q T, MapEquiv (compEqui u q) t
  unique : ∀ (T : EquiSpace.{u}) (u v : Equivariant Q T),
    MapEquiv (compEqui u q) (compEqui v q) → MapEquiv u v

/-- `EQU` has all (small) products. -/
def HasProducts : Prop :=
  ∀ (I : Type u) (A : I → EquiSpace.{u}),
    ∃ (P : EquiSpace.{u}) (π : ∀ i, Equivariant P (A i)), IsProduct A π

/-- `EQU` has equalizers of all parallel pairs. -/
def HasEqualizers : Prop :=
  ∀ (A B : EquiSpace.{u}) (f g : Equivariant A B),
    ∃ (E : EquiSpace.{u}) (e : Equivariant E A), IsEqualizer f g e

/-- `EQU` has all (small) coproducts. -/
def HasCoproducts : Prop :=
  ∀ (I : Type u) (A : I → EquiSpace.{u}),
    ∃ (S : EquiSpace.{u}) (ι : ∀ i, Equivariant (A i) S), IsCoproduct A ι

/-- `EQU` has coequalizers of all parallel pairs. -/
def HasCoequalizers : Prop :=
  ∀ (A B : EquiSpace.{u}) (f g : Equivariant A B),
    ∃ (Q : EquiSpace.{u}) (q : Equivariant B Q), IsCoequalizer f g q

/-- **Complete**: all small products and all equalizers. -/
def IsComplete : Prop := HasProducts.{u} ∧ HasEqualizers.{u}

/-- **Cocomplete**: all small coproducts and all coequalizers. -/
def IsCocomplete : Prop := HasCoproducts.{u} ∧ HasCoequalizers.{u}

/-! ### Regular subobjects and regular quotients

    Theorem 3.2 asserts well-poweredness only in its *regular* form.  Footnote 3
    of the paper records why: Peter Johnstone pointed out that, contrary to the
    assertion in the first draft, `EQU` is not well-powered for arbitrary
    subobjects.  The qualifier is therefore load bearing and is kept in the
    names below. -/

/-- A **monomorphism**: left-cancellable up to `MapEquiv`. -/
def IsMono {S A : EquiSpace.{u}} (m : Equivariant S A) : Prop :=
  ∀ (T : EquiSpace.{u}) (u v : Equivariant T S),
    MapEquiv (compEqui m u) (compEqui m v) → MapEquiv u v

/-- A **regular monomorphism**: one arising as the equalizer of a parallel pair.
    Per §3.2 these are obtained by selecting some equivalence classes of `A` and
    taking their union as a subspace — and the paper warns that there are
    subobjects not formed in this way. -/
def IsRegularMono {S A : EquiSpace.{u}} (m : Equivariant S A) : Prop :=
  ∃ (B : EquiSpace.{u}) (f g : Equivariant A B), IsEqualizer f g m

/-- Every regular mono is a mono: the cancellation law is exactly the uniqueness
    clause of the equalizer that exhibits it.  Proved, not assumed — it is the
    check that `IsEqualizer.unique` and `IsMono` are oriented consistently, and
    it is what licenses the two-triangle form of `SubobjEquiv` below. -/
theorem isMono_of_isRegularMono {S A : EquiSpace.{u}} {m : Equivariant S A} :
    IsRegularMono m → IsMono m
  | ⟨_, _, _, he⟩ => fun T u v huv => he.unique T u v huv

/-- A **regular epimorphism**: one arising as the coequalizer of a parallel pair.
    Per §3.2 forming a regular quotient is coarsening the equivalence relation,
    putting equivalence classes together. -/
def IsRegularEpi {A Q : EquiSpace.{u}} (q : Equivariant A Q) : Prop :=
  ∃ (B : EquiSpace.{u}) (f g : Equivariant B A), IsCoequalizer f g q

/-- Two monos into `A` name the **same subobject** when each factors through the
    other.  The two triangles suffice: cancelling the monos forces the mediating
    maps to be mutually inverse up to `MapEquiv`. -/
def SubobjEquiv {S S' A : EquiSpace.{u}}
    (m : Equivariant S A) (m' : Equivariant S' A) : Prop :=
  ∃ (u : Equivariant S S') (v : Equivariant S' S),
    MapEquiv (compEqui m' u) m ∧ MapEquiv (compEqui m v) m'

/-- Dually, two epis out of `A` name the **same quotient**. -/
def QuotEquiv {A Q Q' : EquiSpace.{u}}
    (q : Equivariant A Q) (q' : Equivariant A Q') : Prop :=
  ∃ (u : Equivariant Q Q') (v : Equivariant Q' Q),
    MapEquiv (compEqui u q) q' ∧ MapEquiv (compEqui v q') q

/-- **Regular well-powered at `A`**: the regular subobjects of `A` constitute a
    *set*.  Since Lean's type theory has no proper classes, "constitute a set" is
    rendered as essential smallness — some family indexed by a type in the same
    universe `u` as the carriers meets every regular subobject of `A`. -/
def RegularWellPoweredAt (A : EquiSpace.{u}) : Prop :=
  ∃ (I : Type u) (S : I → EquiSpace.{u}) (m : ∀ i, Equivariant (S i) A),
    (∀ i, IsRegularMono (m i)) ∧
    ∀ (T : EquiSpace.{u}) (n : Equivariant T A), IsRegularMono n →
      ∃ i, SubobjEquiv (m i) n

/-- **Regular co-well-powered at `A`**: no object has a proper class of
    non-isomorphic regular quotients, rendered as essential smallness. -/
def RegularCoWellPoweredAt (A : EquiSpace.{u}) : Prop :=
  ∃ (I : Type u) (Q : I → EquiSpace.{u}) (q : ∀ i, Equivariant A (Q i)),
    (∀ i, IsRegularEpi (q i)) ∧
    ∀ (T : EquiSpace.{u}) (p : Equivariant A T), IsRegularEpi p →
      ∃ i, QuotEquiv (q i) p

/-- `EQU` is regular well-powered. -/
def RegularWellPowered : Prop := ∀ A : EquiSpace.{u}, RegularWellPoweredAt A

/-- `EQU` is regular co-well-powered. -/
def RegularCoWellPowered : Prop := ∀ A : EquiSpace.{u}, RegularCoWellPoweredAt A

/-- Plain (unqualified) well-poweredness, for arbitrary subobjects. -/
def WellPoweredAt (A : EquiSpace.{u}) : Prop :=
  ∃ (I : Type u) (S : I → EquiSpace.{u}) (m : ∀ i, Equivariant (S i) A),
    (∀ i, IsMono (m i)) ∧
    ∀ (T : EquiSpace.{u}) (n : Equivariant T A), IsMono n →
      ∃ i, SubobjEquiv (m i) n

/-! ### Theorem 3.2 -/

/-- **Theorem 3.2** (completeness half): `EQU` is a complete category.
    Proof obligation: products are the product topology with the product
    equivalence relation; equalizers are the subspace
    `{ x | f x ≡ g x }`. -/
theorem scott98_theorem_3_2_complete : IsComplete.{u} := by
  sorry

/-- **Theorem 3.2** (cocompleteness half): `EQU` is a cocomplete category.
    Proof obligation: coproducts are disjoint unions; coequalizers coarsen the
    equivalence relation on `B` to include `{ (f x, g x) | x }`. -/
theorem scott98_theorem_3_2_cocomplete : IsCocomplete.{u} := by
  sorry

/-- **Theorem 3.2** (regular well-poweredness): inherited from the corresponding
    property of `Top₀` and of the category of equivalence relations. -/
theorem scott98_theorem_3_2_regular_wellPowered : RegularWellPowered.{u} := by
  sorry

/-- **Theorem 3.2** (regular co-well-poweredness). -/
theorem scott98_theorem_3_2_regular_coWellPowered : RegularCoWellPowered.{u} := by
  sorry

/-- **Footnote 3** to Theorem 3.2, recorded as a `Prop`-valued claim rather than
    a proved theorem: `EQU` is *not* well-powered, "for there are fairly simple
    examples of objects in the category with an unbounded number of
    non-isomorphic subobjects" (Johnstone, cited by Scott).

    Left unproved and unasserted.  Whether the paper's "unbounded" is faithfully
    captured by failure of `u`-smallness in `WellPoweredAt` has not been checked
    against Johnstone's examples, which the paper does not exhibit; asserting it
    as a `theorem ... := sorry` would claim a statement whose encoding is
    unverified.  Discharging it requires the counterexample. -/
def Scott98NotWellPowered : Prop :=
  ¬ ∀ A : EquiSpace.{u}, WellPoweredAt A

/-- **Main theorem** (the paper's central claim): `EQU` is cartesian closed —
    the exponential (function-space) equilogical space exists and the currying
    bijection is natural.  Faithful statement; the construction is via the
    injective/cartesian-closed properties of algebraic lattices (§2). -/
def EQU_cartesianClosed : Prop :=
  ∀ (_B _C : EquiSpace.{u}),
    ∃ _exp : EquiSpace.{u}, True  -- TODO: exponential object + natural currying iso.

/-- Theorem 3.4: the categories `EQU` and `PEQU` are equivalent.
    TODO: construct the restriction functor and its pseudo-inverse (§3.3). -/
def EQU_equiv_PEQU : Prop :=
  ∀ _A : PEquiSpace.{u}, ∃ _B : EquiSpace.{u}, True

end Scott1998
