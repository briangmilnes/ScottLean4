/-
  Continuous Lattices (Lean 4 faithful skeleton)

  Faithful to:
    Dana Scott, "Continuous Lattices",
    in: Toposes, Algebraic Geometry and Logic (Lawvere, ed.),
    Lecture Notes in Mathematics 274, Springer, 1972, pp. 97-136.

  Source text extracted from:
    DanaScottPapers/Scott-1972-Continuous-Lattices.txt

  This is an auto-generated faithful skeleton.  It transcribes the core formal
  objects of the paper:

    * Complete lattices (Section 2), bundled as a `structure` with carrier
      `Type`, an order relation, the partial-order axioms, and an arbitrary
      supremum operator `sSup` with its characterizing (least-upper-bound)
      property.  Subsets are `carrier -> Prop`.
    * Directed subsets and their (least upper bound) sups.
    * The way-below relation  x << y  (Scott writes  x < y ), Section 2, given
      lattice-theoretically (p. 117):
        "x < y iff whenever y ⊑ ⨆Z and Z ⊆ D is directed, then x ⊑ z for
         some z ∈ Z."
    * Continuous lattices (Definition 2.3):  every element is the directed
      sup of the elements way-below it,  y = ⨆{ x : x << y }.
    * Scott-continuous functions (Proposition 2.5):  monotone maps preserving
      directed sups; equivalently, maps whose inverse images of open sets are
      open.
    * Scott-open sets (Section 2, conditions (i) and (ii)): upper sets that
      are inaccessible by directed sups.
    * Function spaces [D -> E] (Definition 3.1, Theorem 3.3) with the
      pointwise order (Proposition 3.2).

  Core Lean 4 only; no Mathlib.  Tractable facts about `<<` are proved.
  Genuinely topology-heavy or "well-known" results (the interpolation
  property, Proposition 2.5, the Knaster-Tarski/fixed-point theorem 3.14) are
  left as `sorry` with a `-- TODO` marker; no proof is fabricated.
-/

namespace Scott1972

/-! ## Section 2. Complete lattices

    "Our main interest will lie with those partially ordered sets in which
     every subset has a lub: namely, complete lattices."

    We bundle a complete lattice as a carrier `Type`, an order relation `le`,
    the three partial-order axioms, and an arbitrary-sup operator `sSup` taking
    a subset (a predicate `carrier -> Prop`) to its least upper bound, together
    with the two half-conditions characterizing `sSup S` as that lub. -/
structure CompleteLattice where
  carrier     : Type
  le          : carrier → carrier → Prop
  le_refl     : ∀ a, le a a
  le_trans    : ∀ a b c, le a b → le b c → le a c
  le_antisymm : ∀ a b, le a b → le b a → a = b
  /-- `sSup S` is the least upper bound of the subset `S`. -/
  sSup        : (carrier → Prop) → carrier
  /-- `sSup S` is an upper bound of `S`. -/
  sSup_isUB   : ∀ (S : carrier → Prop) a, S a → le a (sSup S)
  /-- `sSup S` is the least upper bound of `S`. -/
  sSup_isLUB  : ∀ (S : carrier → Prop) u, (∀ a, S a → le a u) → le (sSup S) u

/-- The bottom element  ⊥ = ⨆ ∅  (Scott's `± = ⨆∅`). -/
def CompleteLattice.bot (D : CompleteLattice) : D.carrier :=
  D.sSup (fun _ => False)

/-- The top element  ⊤ = ⨆ D  (Scott's `⊤ = ⨆D`). -/
def CompleteLattice.top (D : CompleteLattice) : D.carrier :=
  D.sSup (fun _ => True)

/-- `⊥` is the least element:  ⊥ ⊑ a  for all `a`. -/
theorem CompleteLattice.bot_le (D : CompleteLattice) (a : D.carrier) :
    D.le D.bot a := by
  show D.le (D.sSup (fun _ => False)) a
  apply D.sSup_isLUB
  intro b hb
  exact False.elim hb

/-- `⊤` is the greatest element:  a ⊑ ⊤  for all `a`. -/
theorem CompleteLattice.le_top (D : CompleteLattice) (a : D.carrier) :
    D.le a D.top := by
  show D.le a (D.sSup (fun _ => True))
  exact D.sSup_isUB _ a trivial

/-! ## Section 2. Directed sets

    "By a directed subset of X we of course mean that it is directed in the
     sense of the partial ordering ⊑. Note that in this paper directed sets
     are always non-empty."

    So a directed set is non-empty and every two of its elements have an
    upper bound within the set. -/
def Directed (D : CompleteLattice) (S : D.carrier → Prop) : Prop :=
  (∃ x, S x) ∧ ∀ x y, S x → S y → ∃ z, S z ∧ D.le x z ∧ D.le y z

/-! ## Section 2. The way-below relation  x << y

    Lattice-theoretic definition (p. 117):
      "x < y  iff  whenever y ⊑ ⨆Z and Z ⊆ D is directed,
       then x ⊑ z for some z ∈ Z."

    We write `wayBelow D x y` for Scott's  x < y  (the modern notation is
    `x ≪ y`). -/
def wayBelow (D : CompleteLattice) (x y : D.carrier) : Prop :=
  ∀ (S : D.carrier → Prop), Directed D S → D.le y (D.sSup S) →
    ∃ d, S d ∧ D.le x d

/-! ## Definition 2.3. Continuous lattice

    "A continuous lattice is a complete lattice D in which for every y ∈ D we
     have:  y = ⨆{ x ∈ D : x << y }." -/
def IsContinuousLattice (D : CompleteLattice) : Prop :=
  ∀ y : D.carrier, y = D.sSup (fun x => wayBelow D x y)

/-! ## Section 2. Scott-open sets

    A subset `U` is open in the induced (Scott) topology iff it satisfies:
      (i)  whenever x ∈ U and x ⊑ y, then y ∈ U          (`U` is an upper set);
      (ii) whenever S ⊆ X is directed, ⨆S exists and ⨆S ∈ U,
           then S ∩ U ≠ ∅.                               (inaccessible by ⨆). -/
def ScottOpen (D : CompleteLattice) (U : D.carrier → Prop) : Prop :=
  (∀ x y, U x → D.le x y → U y) ∧
  (∀ S, Directed D S → U (D.sSup S) → ∃ s, S s ∧ U s)

/-! ## Proposition 2.2. Elementary properties of  <<

    "In a complete lattice D we have: (i) ⊥ << x; ... (v) x << y implies
     x ⊑ y; ..."  We prove the tractable items and some standard consequences. -/

/-- Proposition 2.2 (v):  x << y  implies  x ⊑ y.
    Apply the definition to the (directed) singleton `{y}`, whose sup is ⊒ y. -/
theorem wayBelow_le (D : CompleteLattice) (x y : D.carrier)
    (h : wayBelow D x y) : D.le x y := by
  have hdir : Directed D (fun z => z = y) := by
    refine ⟨⟨y, rfl⟩, ?_⟩
    intro a b ha hb
    refine ⟨y, rfl, ?_, ?_⟩
    · rw [ha]; exact D.le_refl y
    · rw [hb]; exact D.le_refl y
  have hy : D.le y (D.sSup (fun z => z = y)) := D.sSup_isUB _ y rfl
  obtain ⟨d, hd, hxd⟩ := h (fun z => z = y) hdir hy
  subst hd
  exact hxd

/-- Auxiliary "one-sided transitivity":  x << y  and  y ⊑ d  imply  x ⊑ d.
    (Apply the definition of `<<` to the directed singleton `{d}`.) -/
theorem wayBelow_le_trans (D : CompleteLattice) (x y d : D.carrier)
    (hxy : wayBelow D x y) (hyd : D.le y d) : D.le x d := by
  have hdir : Directed D (fun z => z = d) := by
    refine ⟨⟨d, rfl⟩, ?_⟩
    intro a b ha hb
    refine ⟨d, rfl, ?_, ?_⟩
    · rw [ha]; exact D.le_refl d
    · rw [hb]; exact D.le_refl d
  have hy : D.le y (D.sSup (fun z => z = d)) :=
    D.le_trans _ _ _ hyd (D.sSup_isUB _ d rfl)
  obtain ⟨e, he, hxe⟩ := hxy (fun z => z = d) hdir hy
  subst he
  exact hxe

/-- `<<` is transitive:  x << y  and  y << z  imply  x << z. -/
theorem wayBelow_trans (D : CompleteLattice) (x y z : D.carrier)
    (hxy : wayBelow D x y) (hyz : wayBelow D y z) : wayBelow D x z := by
  intro S hS hz
  obtain ⟨d, hd, hyd⟩ := hyz S hS hz
  exact ⟨d, hd, wayBelow_le_trans D x y d hxy hyd⟩

/-- Proposition 2.2 (iv):  x ⊑ y  and  y << z  imply  x << z. -/
theorem wayBelow_of_le_left (D : CompleteLattice) (x y z : D.carrier)
    (hxy : D.le x y) (hyz : wayBelow D y z) : wayBelow D x z := by
  intro S hS hz
  obtain ⟨d, hd, hyd⟩ := hyz S hS hz
  exact ⟨d, hd, D.le_trans _ _ _ hxy hyd⟩

/-- Proposition 2.2 (i):  ⊥ << x  for all `x`.
    Any directed `S` is non-empty, and `⊥` is below its witness. -/
theorem bot_wayBelow (D : CompleteLattice) (x : D.carrier) :
    wayBelow D D.bot x := by
  intro S hS _
  obtain ⟨⟨d, hd⟩, _⟩ := hS
  exact ⟨d, hd, D.bot_le d⟩

/-! ## Proposition 2.5. Scott-continuity

    "If D and D' are complete lattices with their induced topologies, then a
     function f:D -> D' is continuous iff for all directed subsets S ⊆ D:
        f(⨆S) = ⨆{ f(x) : x ∈ S }."

    We formalize the right-hand (order-theoretic) side directly. -/

/-- `f` is monotone (⊑-preserving). In `T₀`-spaces continuous maps are always
    monotone (Section 2). -/
def Monotone (D E : CompleteLattice) (f : D.carrier → E.carrier) : Prop :=
  ∀ x y, D.le x y → E.le (f x) (f y)

/-- `f` preserves directed sups:  f(⨆S) = ⨆ f[S]  for all directed `S`.
    The image `f[S]` is the predicate `fun e => ∃ x, S x ∧ e = f x`. -/
def PreservesDirectedSups (D E : CompleteLattice) (f : D.carrier → E.carrier) :
    Prop :=
  ∀ (S : D.carrier → Prop), Directed D S →
    f (D.sSup S) = E.sSup (fun e => ∃ x, S x ∧ e = f x)

/-- `f` is continuous in the topological sense:  the inverse image of every
    Scott-open set is Scott-open. -/
def PreimageScottOpen (D E : CompleteLattice) (f : D.carrier → E.carrier) :
    Prop :=
  ∀ U, ScottOpen E U → ScottOpen D (fun x => U (f x))

/-- A bundled Scott-continuous function `D -> E`. -/
structure ScottContinuous (D E : CompleteLattice) where
  toFun                 : D.carrier → E.carrier
  preservesDirectedSups : PreservesDirectedSups D E toFun

/-- Preserving directed sups implies monotonicity.
    (The forward, elementary half of Proposition 2.5: for `x ⊑ y` the pair
     `{x, y}` is directed with sup `y`, and `f x ⊑ ⨆ f[{x,y}] = f y`.) -/
theorem monotone_of_preservesDirectedSups (D E : CompleteLattice)
    (f : D.carrier → E.carrier) (hf : PreservesDirectedSups D E f) :
    Monotone D E f := by
  intro x y hxy
  -- the two-element directed set S = {x, y}
  have hdir : Directed D (fun z => z = x ∨ z = y) := by
    refine ⟨⟨y, Or.inr rfl⟩, ?_⟩
    intro a b ha hb
    refine ⟨y, Or.inr rfl, ?_, ?_⟩
    · cases ha with
      | inl h => rw [h]; exact hxy
      | inr h => rw [h]; exact D.le_refl y
    · cases hb with
      | inl h => rw [h]; exact hxy
      | inr h => rw [h]; exact D.le_refl y
  -- its sup is y, since x ⊑ y
  have hsup : D.sSup (fun z => z = x ∨ z = y) = y := by
    apply D.le_antisymm
    · apply D.sSup_isLUB
      intro a ha
      cases ha with
      | inl h => rw [h]; exact hxy
      | inr h => rw [h]; exact D.le_refl y
    · exact D.sSup_isUB _ y (Or.inr rfl)
  have hpres := hf (fun z => z = x ∨ z = y) hdir
  rw [hsup] at hpres
  have himg : (fun e => ∃ z, (z = x ∨ z = y) ∧ e = f z) (f x) :=
    ⟨x, Or.inl rfl, rfl⟩
  have hle := E.sSup_isUB (fun e => ∃ z, (z = x ∨ z = y) ∧ e = f z) (f x) himg
  rw [← hpres] at hle
  exact hle

/-- Proposition 2.5 (full statement):  `f` preserves directed sups iff it is
    Scott-continuous in the topological sense. -/
theorem preservesDirectedSups_iff_topological (D E : CompleteLattice)
    (f : D.carrier → E.carrier) :
    PreservesDirectedSups D E f ↔ PreimageScottOpen D E f := by
  sorry -- TODO Proposition 2.5 (topology-heavy direction)

/-! ## Section 2. The interpolation property of  <<

    A central property of the way-below relation in a continuous lattice
    (used pervasively in the theory): `<<` interpolates. -/

/-- Interpolation property:  in a continuous lattice, x << z implies there is
    an intermediate `y` with  x << y << z. -/
theorem wayBelow_interpolation (D : CompleteLattice)
    (hD : IsContinuousLattice D) (x z : D.carrier) (h : wayBelow D x z) :
    ∃ y, wayBelow D x y ∧ wayBelow D y z := by
  sorry -- TODO interpolation property of << (Section 2)

/-! ## Section 3. Function spaces

    "3.1 Definition. For To-spaces X and Y we let [X -> Y] be the space of all
     continuous functions f: X -> Y endowed with the product topology,
     sometimes called the topology of pointwise convergence."

    "3.2 Proposition. The induced partial ordering on [X -> Y] is such that:
        f ⊑ g  iff  f(x) ⊑ g(x) for all x ∈ X." -/

/-- Proposition 3.2: the pointwise order on `[D -> E]` (Scott-continuous
    functions). -/
def funSpaceLe (D E : CompleteLattice) (f g : ScottContinuous D E) : Prop :=
  ∀ x, E.le (f.toFun x) (g.toFun x)

/-- Theorem 3.3: "If D and D' are continuous lattices, then so is [D -> D']
    under the induced partial ordering with the lattice topology agreeing with
    the product topology."  Stated here as: the function space carries a
    complete-lattice structure whose order is the pointwise order, and which is
    continuous.  (Construction of the sups requires the pointwise-lub argument
    of Theorem 3.3.) -/
theorem funSpace_isContinuousLattice (D E : CompleteLattice)
    (_hD : IsContinuousLattice D) (_hE : IsContinuousLattice E) :
    ∃ F : CompleteLattice,
      F.carrier = ScottContinuous D E ∧ IsContinuousLattice F := by
  sorry -- TODO Theorem 3.3 (function space is a continuous lattice)

/-! ## Proposition 3.14 / Section 2 (2.10). Fixed points

    "The proof of the existence of minimal fixed points in complete lattices is
     well known."  And 3.14:  "For a continuous lattice D there is a uniquely
     determined continuous mapping  fix : [D -> D] -> D  where f(fix(f)) =
     fix(f) and whenever f(x) = x then fix(f) ⊑ x."

    We state the underlying Knaster-Tarski least-fixed-point theorem for a
    monotone endofunction of a complete lattice. -/
theorem exists_least_fixpoint (D : CompleteLattice)
    (f : D.carrier → D.carrier) (_hf : Monotone D D f) :
    ∃ a, f a = a ∧ ∀ b, f b = b → D.le a b := by
  sorry -- TODO Knaster–Tarski least fixed point (Proposition 3.14)

end Scott1972
