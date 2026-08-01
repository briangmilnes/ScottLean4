/-
  Some Ordered Sets in Computer Science (Lean 4 formalization, faithful skeleton)

  Faithful to:
    D. Scott, "Some Ordered Sets in Computer Science",
    in I. Rival (ed.), Ordered Sets, pp. 677-718,
    D. Reidel Publishing Company, 1982.

  Source text extracted from:
    DanaScottPapers/Scott-1982-Some-Ordered-Sets-in-Computer-Science.txt

  This is an auto-generated faithful skeleton of the paper's core order-theoretic
  apparatus.  Scott's lectures develop the theory of *domains* -- posets that are
  closed under sups of directed subsets (and, for the finitary case, in which every
  element is the directed sup of the "compact"/finite elements below it).  Central
  notions transcribed here:

    * partial orders (posets), Example 1's ⊑ ("the inclusion between the graphs
      of the functions regarded as sets of ordered pairs");
    * directed sets and their sups (Scott replaces linearly-ordered "towers" by
      "unions of directed subfamilies"), and cpo's / directed-complete posets;
    * monotone and continuous maps ("A mapping between domains is continuous if it
      preserves directed sups"), and the characterization continuity ⇔ monotone +
      preservation of directed sups;
    * the flat domain of a data type -- Scott's  W̃ = {{n} | n ∈ ω} ∪ {∅},  i.e.
      "add ⊥ as the 'undefined' element to ω" -- here modelled as an `inductive`;
    * finite/compact elements and the way-below relation;
    * the fixed-point theorem  fix(F) = ⨆ₙ Fⁿ(⊥)  and the continuous fixed-point
      operator `fix : (X → X) → X`;
    * constructions on domains (product; lifting; and, in comments, sum and the
      function space).

  Core Lean 4 only; no Mathlib.  Posets/cpos are bundled `structure`s carrying the
  carrier `Type`, the order `le`, the order axioms, and (for cpos) a directed-sup
  operator with its least-upper-bound property.  Subsets are `Carrier → Prop`.
-/

namespace Scott1982

/-! ## Upper bounds, least upper bounds, directed sets

    Subsets of a carrier `α` are represented by their characteristic predicate
    `α → Prop`.  A *directed* set is a non-empty subset in which every pair of
    elements has an upper bound *inside the set*.  Scott: "it is better to take the
    closure condition as employing unions of directed subfamilies and to forget
    about linearly ordered towers." -/

/-- `u` is an upper bound of the subset `S` under the order `le`. -/
def IsUpperBound {α : Type} (le : α → α → Prop) (S : α → Prop) (u : α) : Prop :=
  ∀ x, S x → le x u

/-- `u` is a least upper bound (supremum) of `S`. -/
def IsLUB {α : Type} (le : α → α → Prop) (S : α → Prop) (u : α) : Prop :=
  IsUpperBound le S u ∧ ∀ v, IsUpperBound le S v → le u v

/-- `S` is a directed subset: non-empty, and any two members are dominated by a
    common member of `S`. -/
def Directed {α : Type} (le : α → α → Prop) (S : α → Prop) : Prop :=
  (∃ x, S x) ∧ ∀ x y, S x → S y → ∃ z, S z ∧ le x z ∧ le y z

/-- The image of a subset `S` under a map `f`, as a subset of the codomain. -/
def image {α β : Type} (f : α → β) (S : α → Prop) : β → Prop :=
  fun y => ∃ x, S x ∧ y = f x

/-! ## Partial orders (posets)

    EXAMPLE 1.  "The set (ℕ ⇀ ℕ) of all partial number-theoretic functions is
    partially ordered by the relation:  f ⊑ g  iff whenever f(n) is defined, then
    so is g(n) and f(n) = g(n)."  We axiomatize any such partial order abstractly:
    a carrier `Type` together with a reflexive, transitive, antisymmetric `le`. -/
structure Poset where
  Carrier : Type
  le : Carrier → Carrier → Prop
  le_refl : ∀ x, le x x
  le_trans : ∀ {x y z}, le x y → le y z → le x z
  le_antisymm : ∀ {x y}, le x y → le y x → x = y

/-! ## Complete partial orders (directed-complete posets, "cpo"s)

    A *cpo* is a poset with a least element `⊥` and, for every directed subset, a
    supremum.  This is Scott's closure property: "closure under ... sup of directed
    subsets", together with the least element "which is just the intersection of the
    whole family of sets".  The directed-sup operator `sup` is total, but its
    least-upper-bound property is asserted only for directed subsets. -/
structure CPO extends Poset where
  bot : Carrier
  bot_le : ∀ x, le bot x
  sup : (Carrier → Prop) → Carrier
  sup_isLUB : ∀ S, Directed le S → IsLUB le S (sup S)

/-! ## Monotone maps

    Scott, property (**): "f ⊑ g always implies F(f) ⊑ F(g)" -- every continuous
    functional is monotone. -/

/-- `f` is monotone for the order of the poset `D`. -/
def Monotone (D : Poset) (f : D.Carrier → D.Carrier) : Prop :=
  ∀ x y, D.le x y → D.le (f x) (f y)

/-- The image of a directed set under a monotone map is directed.  (This is the
    fact that makes the directed sup on the right-hand side of the continuity
    equation well-formed.) -/
theorem image_directed (D : Poset) {f : D.Carrier → D.Carrier}
    (hf : Monotone D f) {S : D.Carrier → Prop} (hS : Directed D.le S) :
    Directed D.le (image f S) := by
  obtain ⟨⟨x0, hx0⟩, hup⟩ := hS
  refine ⟨⟨f x0, ⟨x0, hx0, rfl⟩⟩, ?_⟩
  intro u v hu hv
  obtain ⟨x, hxS, hux⟩ := hu
  obtain ⟨y, hyS, hvy⟩ := hv
  obtain ⟨z, hzS, hxz, hyz⟩ := hup x y hxS hyS
  refine ⟨f z, ⟨z, hzS, rfl⟩, ?_, ?_⟩
  · rw [hux]; exact hf x z hxz
  · rw [hvy]; exact hf y z hyz

/-- Monotone maps are closed under composition. -/
theorem Monotone.comp (D : Poset) {f g : D.Carrier → D.Carrier}
    (hf : Monotone D f) (hg : Monotone D g) : Monotone D (fun x => f (g x)) := by
  intro x y hxy
  exact hf (g x) (g y) (hg x y hxy)

/-! ## Continuous maps

    "A mapping between domains is continuous if it preserves directed sups."
    Equivalently (Scott's equation (*), for towers):  F(⨆ fₙ) = ⨆ F(fₙ).  We build
    monotonicity into the definition and record the characterization theorem
    `continuous_iff`:  continuity ⇔ monotone ∧ preservation of directed sups. -/

/-- `f` sends the sup of every directed set to the sup of the image. -/
def PreservesDirectedSups (D : CPO) (f : D.Carrier → D.Carrier) : Prop :=
  ∀ S, Directed D.le S → f (D.sup S) = D.sup (image f S)

/-- A continuous self-map of a cpo: monotone and preserving directed sups. -/
def Continuous (D : CPO) (f : D.Carrier → D.Carrier) : Prop :=
  Monotone D.toPoset f ∧ PreservesDirectedSups D f

/-- MAIN CHARACTERIZATION.  A self-map is continuous iff it is monotone and
    preserves sups of directed sets.  (With continuity defined as this very
    conjunction, the equivalence is the identity; the content is the packaging of
    Scott's "preserves directed sups" together with monotonicity (**).) -/
theorem continuous_iff (D : CPO) (f : D.Carrier → D.Carrier) :
    Continuous D f ↔ (Monotone D.toPoset f ∧ PreservesDirectedSups D f) := Iff.rfl

/-- Continuous maps are monotone (Scott's (**): "all continuous functionals are
    monotone"). -/
theorem continuous_imp_monotone (D : CPO) {f : D.Carrier → D.Carrier}
    (hf : Continuous D f) : Monotone D.toPoset f := hf.1

/-! ## Finite / compact elements and the way-below relation

    "We call a set x ∈ 𝒞 which is the closure of a finite subset a finitely
    generated element, or just a finite element."  Order-theoretically the finite
    (compact) elements are characterized by the *way-below* relation:  `x ≪ y`
    holds when every directed set whose sup dominates `y` already has a member
    dominating `x`.  A *compact* element is one way-below itself. -/

/-- The way-below relation `x ≪ y`. -/
def WayBelow (D : CPO) (x y : D.Carrier) : Prop :=
  ∀ S, Directed D.le S → D.le y (D.sup S) → ∃ s, S s ∧ D.le x s

/-- `x` is a compact (finite) element:  `x ≪ x`. -/
def Compact (D : CPO) (x : D.Carrier) : Prop := WayBelow D x x

/-! ## The fixed-point theorem

    Section 1, the least fixed-point operator:
        "fix(F) = ⨆ₙ Fⁿ(⊥),  where ⊥ is the empty function (or least element) ...
         and where Fⁿ is the n-fold composition of F with itself.  Using the
         continuity of F, it can be shown ... that f = fix(F) is the least function
         ... such that f = F(f).  What is being stressed ... is ... that the whole
         operator fix is itself continuous."

    `iterate f n ⊥ = Fⁿ(⊥)` are the approximants forming a tower; `iterates` is the
    subset of all of them; `fix` is their directed sup. -/

/-- `iterate f n x = fⁿ(x)`, the n-fold composition. -/
def iterate {α : Type} (f : α → α) : Nat → α → α
  | 0,     x => x
  | n + 1, x => f (iterate f n x)

/-- The tower of approximants `{ Fⁿ(⊥) | n ∈ ℕ }` as a subset. -/
def iterates (D : CPO) (f : D.Carrier → D.Carrier) : D.Carrier → Prop :=
  fun x => ∃ n, x = iterate f n D.bot

/-- The least fixed point `fix(F) = ⨆ₙ Fⁿ(⊥)`. -/
def fix (D : CPO) (f : D.Carrier → D.Carrier) : D.Carrier :=
  D.sup (iterates D f)

/-- The approximants form an ascending chain (tower):  `Fⁿ(⊥) ⊑ Fⁿ⁺¹(⊥)`.
    (Tractable: base case is `⊥ ⊑ F(⊥)`; step case is monotonicity.) -/
theorem iterate_mono_step (D : CPO) {f : D.Carrier → D.Carrier}
    (hf : Monotone D.toPoset f) :
    ∀ n, D.le (iterate f n D.bot) (iterate f (n + 1) D.bot) := by
  intro n
  induction n with
  | zero => exact D.bot_le _
  | succ k ih => exact hf (iterate f k D.bot) (iterate f (k + 1) D.bot) ih

/-- The tower of approximants is a directed set.
    TODO: derive from `iterate_mono_step` that the chain is directed. -/
theorem iterates_directed (D : CPO) {f : D.Carrier → D.Carrier}
    (hf : Monotone D.toPoset f) : Directed D.le (iterates D f) := by
  sorry -- TODO: the ascending chain of iterates is directed (any two are comparable)

/-- FIXED-POINT THEOREM (existence).  For continuous `f`, `fix f` is a fixed point.
    TODO: full proof uses continuity `f (sup S) = sup (image f S)` on the tower. -/
theorem fix_is_fixedpoint (D : CPO) {f : D.Carrier → D.Carrier}
    (hf : Continuous D f) : fix D f = f (fix D f) := by
  sorry -- TODO: Scott's fixed-point theorem (Section 1)

/-- FIXED-POINT THEOREM (leastness).  `fix f` is below any pre-fixed point `y`
    (`f y ⊑ y`).  TODO: induction on the tower using `bot_le` and monotonicity. -/
theorem fix_is_least (D : CPO) {f : D.Carrier → D.Carrier}
    (hf : Continuous D f) (y : D.Carrier) (hy : D.le (f y) y) :
    D.le (fix D f) y := by
  sorry -- TODO: least pre-fixed-point property

/-! ## The flat domain of a data type

    Scott, near the end: "All we have done is to add ⊥ as the 'undefined' element
    to ω" -- the flat domain  W̃ = {{n} | n ∈ ω} ∪ {∅}.  Distinct data values are
    pairwise incomparable ("an antichain"), and `⊥` sits below all of them.  We
    model it directly as an `inductive` and prove the tractable order facts. -/

/-- The flat domain over a data type `α`:  a bottom plus one incomparable copy of
    each value of `α`. -/
inductive Flat (α : Type) where
  | bot : Flat α
  | val : α → Flat α

/-- The flat order:  `⊥ ⊑ everything`;  `val a ⊑ val b` iff `a = b`. -/
def Flat.le {α : Type} : Flat α → Flat α → Prop
  | Flat.bot,   _         => True
  | Flat.val _, Flat.bot  => False
  | Flat.val a, Flat.val b => a = b

/-- Reflexivity of the flat order. -/
theorem Flat.le_refl {α : Type} : ∀ x : Flat α, Flat.le x x
  | Flat.bot   => True.intro
  | Flat.val _ => rfl

/-- Transitivity of the flat order. -/
theorem Flat.le_trans {α : Type} {x y z : Flat α}
    (hxy : Flat.le x y) (hyz : Flat.le y z) : Flat.le x z := by
  cases x with
  | bot => trivial
  | val a =>
    cases y with
    | bot => exact False.elim hxy
    | val b =>
      cases z with
      | bot => exact False.elim hyz
      | val c => exact hxy.trans hyz

/-- Antisymmetry of the flat order. -/
theorem Flat.le_antisymm {α : Type} {x y : Flat α}
    (hxy : Flat.le x y) (hyx : Flat.le y x) : x = y := by
  cases x with
  | bot =>
    cases y with
    | bot => rfl
    | val b => exact False.elim hyx
  | val a =>
    cases y with
    | bot => exact False.elim hxy
    | val b => exact congrArg Flat.val hxy

/-- `⊥` is the least element of the flat domain. -/
theorem Flat.bot_le {α : Type} (x : Flat α) : Flat.le Flat.bot x := True.intro

/-- The flat domain bundled as a `Poset`. -/
def FlatPoset (α : Type) : Poset where
  Carrier := Flat α
  le := Flat.le
  le_refl := Flat.le_refl
  le_trans := fun hxy hyz => Flat.le_trans hxy hyz
  le_antisymm := fun hxy hyx => Flat.le_antisymm hxy hyx

/-! ## Lifting a poset

    The general *lifting* construction adjoins a fresh least element `⊥` below an
    existing poset (the flat domain is the special case where the underlying order
    is discrete).  Scott uses lifting to turn a set into "(almost) a closure
    system", e.g. `W̃`. -/

/-- Lift `α` by a new bottom. -/
inductive Lift (α : Type) where
  | bot : Lift α
  | up  : α → Lift α

/-- The lifted order for a base order `le`. -/
def Lift.le {α : Type} (le : α → α → Prop) : Lift α → Lift α → Prop
  | Lift.bot,  _        => True
  | Lift.up _, Lift.bot => False
  | Lift.up a, Lift.up b => le a b

/-- Lifting a poset `E` yields a poset with a new least element. -/
def LiftPoset (E : Poset) : Poset where
  Carrier := Lift E.Carrier
  le := Lift.le E.le
  le_refl := by
    intro x; cases x with
    | bot => trivial
    | up a => exact E.le_refl a
  le_trans := by
    intro x y z hxy hyz
    cases x with
    | bot => trivial
    | up a =>
      cases y with
      | bot => exact False.elim hxy
      | up b =>
        cases z with
        | bot => exact False.elim hyz
        | up c => exact E.le_trans hxy hyz
  le_antisymm := by
    intro x y hxy hyx
    cases x with
    | bot =>
      cases y with
      | bot => rfl
      | up b => exact False.elim hyx
    | up a =>
      cases y with
      | bot => exact False.elim hxy
      | up b => exact congrArg Lift.up (E.le_antisymm hxy hyx)

/-! ## Product of domains

    "the construction of products is even easier": the cartesian product `D₀ × D₁`
    ordered componentwise, isomorphic to "the usual cartesian product of |D₀| and
    |D₁|".  Here is the underlying poset. -/

/-- The componentwise (cartesian) product of two posets. -/
def ProdPoset (D E : Poset) : Poset where
  Carrier := D.Carrier × E.Carrier
  le := fun p q => D.le p.1 q.1 ∧ E.le p.2 q.2
  le_refl := fun p => ⟨D.le_refl p.1, E.le_refl p.2⟩
  le_trans := fun h1 h2 => ⟨D.le_trans h1.1 h2.1, E.le_trans h1.2 h2.2⟩
  le_antisymm := by
    intro p q h1 h2
    obtain ⟨a, b⟩ := p
    obtain ⟨c, d⟩ := q
    have e1 : a = c := D.le_antisymm h1.1 h2.1
    have e2 : b = d := E.le_antisymm h1.2 h2.2
    rw [e1, e2]

/-! ## Further constructions (function space and sum)

    Scott's remaining constructions, recorded here in prose (their faithful Lean
    encodings would follow the same `structure`/`inductive` pattern):

    * FUNCTION SPACE `(D₀ → D₁)`.  "THEOREM.  The set of continuous functions
      between two domains is again (isomorphic to) a domain under the pointwise
      partial order."  Carrier = continuous maps `D₀ → D₁`; order = pointwise;
      sup of a directed family taken pointwise.  With products and function spaces,
      "the category of domains ... is cartesian closed", and carries the continuous
      fixed-point operator `fix : (X → X) → X`.

    * SUM `D₀ + D₁`.  "This construct is called the sum of the domains."  Unlike a
      categorical coproduct, the two summands share the single bottom `⊥` (the
      "uniform occurrence of ⊥ in all domains is one of the blocks to forming
      disjoint sums"): elements are `⊥` together with the tagged elements of each
      summand -- i.e. a lifted disjoint union. -/

end Scott1982
