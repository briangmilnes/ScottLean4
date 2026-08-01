/-
  Outline of a Mathematical Theory of Computation (Lean 4 formalization, faithful skeleton)

  Faithful to:
    Dana Scott, "Outline of a Mathematical Theory of Computation",
    Technical Monograph PRG-2, Oxford University Computing Laboratory,
    Programming Research Group, November 1970.
    (Revised/expanded from the Proceedings of the Fourth Annual Princeton
     Conference on Information Sciences and Systems, 1970.)

  Source text extracted from:
    DanaScottPapers/Scott-1970-Outline-of-a-Mathematical-Theory-of-Computation-PRG2.txt

  This file is an auto-generated faithful skeleton of the foundational content
  of Sections 2, 3, 4, and 5:
    * Axiom 1  : a data type is a partially ordered set.
    * Axiom 2  : mappings between data types are monotonic.
    * Axiom 3' : a data type is a complete lattice under its partial ordering
                 (here we present the weaker cpo/directed-complete form as well,
                  which is what continuity and the fixed-point theorem require).
    * Axiom 4  : mappings between data types are continuous (preserve limits
                 of directed sets, i.e. least upper bounds).
    * The bottom element ⊥ (l.u.b. of the empty set) and top element ⊤.
    * Directed sets and their limits (least upper bounds).
    * Section 5: "It is a well-known theorem that every continuous (even
      monotonic) function mapping a complete lattice into itself has a fixed
      point." — the least fixed point as the l.u.b. of the iterates fⁿ(⊥).

  CORE Lean 4 only; no Mathlib.  A partial order is a `structure` bundling a
  carrier `Type` with a relation `≤` and the order axioms as fields.  Subsets
  are represented by predicates `X → Prop`.  Least upper bounds are given
  abstractly by a predicate `IsLUB` and, where a data type supplies them, by a
  supremum operator field with its defining property.

  `sorry` marks the genuinely deep results (existence of arbitrary sups, full
  continuity of specific functionals, the least-fixed-point construction as an
  actual limit) that are beyond a core-Lean skeleton.
-/

namespace Scott1970

/-! ## Axiom 1.  Data types are partially ordered sets.

    "AXIOM 1.  A data type is a partially ordered set."

    Scott writes `x ⊑ y` ("x approximates y", intuitively: y is consistent with
    x and is possibly more accurate / carries more information than x), and
    requires `⊑` to be reflexive, transitive, and antisymmetric.  We bundle the
    carrier and the relation with these three order axioms as fields. -/
structure DataType where
  /-- The set `D` of all objects of the type. -/
  Carrier : Type
  /-- The approximation ordering `x ⊑ y` ("x approximates y"). -/
  le : Carrier → Carrier → Prop
  le_refl : ∀ x, le x x
  le_trans : ∀ {x y z}, le x y → le y z → le x z
  le_antisymm : ∀ {x y}, le x y → le y x → x = y

/-- Notation `x ⊑[D] y` for the approximation ordering of data type `D`. -/
scoped notation:50 x " ⊑[" D "] " y => DataType.le D x y

/-! ## Axiom 2.  Mappings between data types are monotonic.

    "AXIOM 2.  Mappings between data types are monotonic."

    "x ⊑ y implies f(x) ⊑' f(y)": the more accurate the input, the more accurate
    the output.  Here `f : D.Carrier → E.Carrier` maps one data type into
    another (possibly the same). -/
def Monotone (D E : DataType) (f : D.Carrier → E.Carrier) : Prop :=
  ∀ ⦃x y⦄, (x ⊑[D] y) → (f x ⊑[E] f y)

/-- The identity mapping is monotonic. -/
theorem monotone_id (D : DataType) : Monotone D D (fun x => x) :=
  fun _ _ h => h

/-- The composite of monotonic mappings is monotonic. -/
theorem monotone_comp {D E F : DataType}
    {g : E.Carrier → F.Carrier} {f : D.Carrier → E.Carrier}
    (hg : Monotone E F g) (hf : Monotone D E f) :
    Monotone D F (fun x => g (f x)) :=
  fun _ _ h => hg (hf h)

/-! ## Least upper bounds (limits / joins).

    "in the sense of the partial ordering ⊑ the limit is naturally taken to be
     the least upper bound (l.u.b.)."

    We express the l.u.b. of a subset `X : D.Carrier → Prop` abstractly.  `u` is
    an upper bound of `X` if it dominates every member; `u` is the l.u.b. if it
    is an upper bound below every other upper bound. -/
def IsUpperBound (D : DataType) (X : D.Carrier → Prop) (u : D.Carrier) : Prop :=
  ∀ ⦃x⦄, X x → (x ⊑[D] u)

def IsLUB (D : DataType) (X : D.Carrier → Prop) (u : D.Carrier) : Prop :=
  IsUpperBound D X u ∧ ∀ ⦃v⦄, IsUpperBound D X v → (u ⊑[D] v)

/-- A least upper bound, when it exists, is unique (by antisymmetry). -/
theorem IsLUB.unique {D : DataType} {X : D.Carrier → Prop} {u v : D.Carrier}
    (hu : IsLUB D X u) (hv : IsLUB D X v) : u = v :=
  D.le_antisymm (hu.2 hv.1) (hv.2 hu.1)

/-! ## Directed sets.

    "A subset X ⊆ D is directed if every finite subset {x₀,x₁,…,x_{n-1}} ⊆ X has
     an upper bound y ∈ X … Note that a directed set is always non-empty."

    We take the standard binary+nonempty formulation, which is equivalent to the
    finite-subset formulation for the empty and pairwise cases used throughout:
    `X` is non-empty, and any two members have an upper bound within `X`. -/
structure Directed (D : DataType) (X : D.Carrier → Prop) : Prop where
  nonempty : ∃ x, X x
  directed : ∀ ⦃x y⦄, X x → X y → ∃ z, X z ∧ (x ⊑[D] z) ∧ (y ⊑[D] z)

/-! ## Axiom 3'.  Data types are complete lattices.

    "AXIOM 3'.  A data type is a complete lattice under its partial ordering."
    "we assume that every subset of the data type has a least upper bound."

    For the continuity/fixed-point development it suffices to have suprema of
    directed sets (a "cpo"); we record both.  We bundle a supremum operator with
    its defining property (`sup X` is the l.u.b. of `X`) as fields.

    The bottom element ⊥ is "the l.u.b. of the empty subset"; the top element ⊤
    is "the l.u.b. of the whole of D". -/
structure CompleteLattice extends DataType where
  /-- `sup X` supplies the least upper bound of the subset `X`. -/
  sup : (Carrier → Prop) → Carrier
  sup_isLUB : ∀ (X : Carrier → Prop),
    IsLUB (toDataType) X (sup X)

namespace CompleteLattice

/-- The bottom element ⊥ = l.u.b. of the empty subset. -/
def bot (L : CompleteLattice) : L.Carrier :=
  L.sup (fun _ => False)

/-- The top element ⊤ = l.u.b. of the whole carrier. -/
def top (L : CompleteLattice) : L.Carrier :=
  L.sup (fun _ => True)

/-- "⊥ is the very 'smallest' element in the partial ordering": ⊥ ⊑ x for all x.

    Proof: ⊥ is the l.u.b. of the empty set, and every `x` is (vacuously) an
    upper bound of the empty set, so ⊥ ⊑ x by the l.u.b. property. -/
theorem bot_le (L : CompleteLattice) (x : L.Carrier) :
    (bot L) ⊑[L.toDataType] x := by
  have hlub := L.sup_isLUB (fun _ => False)
  exact hlub.2 (fun y (h : False) => h.elim)

/-- "⊤ is the very 'largest' element in the partial ordering": x ⊑ ⊤ for all x.

    Proof: ⊤ is the l.u.b. of the full set, which contains `x`. -/
theorem le_top (L : CompleteLattice) (x : L.Carrier) :
    x ⊑[L.toDataType] (top L) := by
  have hlub := L.sup_isLUB (fun _ => True)
  exact hlub.1 (show (fun _ => True) x from trivial)

end CompleteLattice

/-! ## Axiom 4.  Mappings between data types are continuous.

    "AXIOM 4.  Mappings between data types are continuous."
    "A mapping that preserves all limits is called continuous:
        f(⨆ X) = ⨆ { f(x) : x ∈ X }."

    Continuity is stated relative to the l.u.b. structure: for every directed
    `X`, the image `f(⨆X)` is the l.u.b. of the image set `{ f x : x ∈ X }`.
    (Given monotonicity, `f` maps directed sets to directed sets, so the image
    set does have a l.u.b.; we require `f` to attain it.)

    We phrase the image set as `fun y => ∃ x, X x ∧ f x = y`. -/
def image (D E : DataType) (f : D.Carrier → E.Carrier)
    (X : D.Carrier → Prop) : E.Carrier → Prop :=
  fun y => ∃ x, X x ∧ f x = y

/-- Continuity: `f` preserves least upper bounds of directed sets. -/
def Continuous (D E : DataType) (f : D.Carrier → E.Carrier) : Prop :=
  ∀ ⦃X : D.Carrier → Prop⦄, Directed D X →
    ∀ ⦃u : D.Carrier⦄, IsLUB D X u →
      IsLUB E (image D E f X) (f u)

/-! "Someone may want to point out that … Axiom 4 implies Axiom 2" (p. 12): every
    continuous mapping is monotonic.  The standard proof considers the directed
    two-element set `{x, y}` with `x ⊑ y`; its l.u.b. is `y`, and continuity
    forces `f y` to be the l.u.b. of `{f x, f y}`, whence `f x ⊑ f y`.

    The image/directedness bookkeeping is routine but lengthy in core Lean; we
    record the statement and defer the proof. -/
theorem Continuous.monotone {D E : DataType} {f : D.Carrier → E.Carrier}
    (hf : Continuous D E f) : Monotone D E f := by
  sorry -- TODO: continuity ⇒ monotonicity via the directed set {x, y} for x ⊑ y

/-- The identity mapping is continuous. -/
theorem continuous_id (D : DataType) : Continuous D D (fun x => x) := by
  intro X _ u hu
  constructor
  · -- (fun x => x) u is an upper bound of the image of X under id
    intro y hy
    obtain ⟨x, hx, hxy⟩ := hy
    have : (x ⊑[D] u) := hu.1 hx
    exact hxy ▸ this
  · -- and it is below every other upper bound
    intro v hv
    refine hu.2 ?_
    intro x hx
    exact hv ⟨x, hx, rfl⟩

/-! ## Section 3, p. 11 (Axiom 4 discussion).

    "A function of two variables is continuous just when it is continuous in each
     of its variables separately … the function f defined by f(x) = g(x,x) is
     also continuous."

    We record only the statement that identifying the two arguments of a jointly
    continuous binary map yields a continuous unary map; a faithful proof needs
    the product data type and separate continuity, deferred here. -/
theorem continuous_diagonal {D E : DataType}
    (g : D.Carrier → D.Carrier → E.Carrier)
    (hg : ∀ y, Continuous D E (fun x => g x y))
    (hg' : ∀ x, Continuous D E (fun y => g x y)) :
    Continuous D E (fun x => g x x) := by
  sorry -- TODO: diagonalization of a jointly continuous function of two variables

/-! ## Section 5.  The least fixed-point theorem.

    "It is a well-known theorem that every continuous (even monotonic) function
     mapping a complete lattice into itself has a fixed point."

    The constructive (Kleene) form used throughout the paper: the least fixed
    point of a continuous `f : L → L` is the l.u.b. of the ascending chain of
    iterates
        ⊥ ⊑ f(⊥) ⊑ f²(⊥) ⊑ … ⊑ fⁿ(⊥) ⊑ …
    We build the iterates and the set of iterates, then state that its l.u.b. is
    a (indeed the least) fixed point. -/

/-- `iterate f n x = fⁿ(x)`. -/
def iterate {α : Type} (f : α → α) : Nat → α → α
  | 0, x => x
  | (n+1), x => f (iterate f n x)

/-- The set of finite iterates `{ fⁿ(⊥) : n ∈ ℕ }`. -/
def iterateChain (L : CompleteLattice) (f : L.Carrier → L.Carrier) :
    L.Carrier → Prop :=
  fun y => ∃ n, iterate f n (L.bot) = y

/-- The chain of iterates from ⊥ is ascending: fⁿ(⊥) ⊑ fⁿ⁺¹(⊥), given `f`
    monotonic.  Proof by induction on `n`, base case ⊥ ⊑ f(⊥) by `bot_le`. -/
theorem iterate_le_succ (L : CompleteLattice) (f : L.Carrier → L.Carrier)
    (hf : Monotone L.toDataType L.toDataType f) :
    ∀ n, (iterate f n (L.bot)) ⊑[L.toDataType] (iterate f (n+1) (L.bot)) := by
  intro n
  induction n with
  | zero =>
      -- iterate f 0 ⊥ = ⊥ ⊑ f ⊥ = iterate f 1 ⊥
      exact L.bot_le _
  | succ k ih =>
      -- fᵏ⁺¹(⊥) = f(fᵏ(⊥)) ⊑ f(fᵏ⁺¹(⊥)) = fᵏ⁺²(⊥), by monotonicity applied to ih
      exact hf ih

/-- The least fixed point, defined (Kleene-style) as the l.u.b. of the iterates
    of ⊥ under `f`. -/
def lfp (L : CompleteLattice) (f : L.Carrier → L.Carrier) : L.Carrier :=
  L.sup (iterateChain L f)

/-- The set of iterates is directed (it is a chain from ⊥, hence any two members
    are comparable, giving a common upper bound).  Requires `f` monotonic. -/
theorem iterateChain_directed (L : CompleteLattice) (f : L.Carrier → L.Carrier)
    (hf : Monotone L.toDataType L.toDataType f) :
    Directed L.toDataType (iterateChain L f) := by
  sorry -- TODO: the ascending chain {fⁿ(⊥)} is directed (linearly ordered)

/-! ### The fixed-point theorem (Section 5).

    "every continuous … function mapping a complete lattice into itself has a
     fixed point."

    With `lfp f = ⨆ₙ fⁿ(⊥)` and `f` continuous, continuity gives
        f(lfp f) = f(⨆ₙ fⁿ(⊥)) = ⨆ₙ f(fⁿ(⊥)) = ⨆ₙ fⁿ⁺¹(⊥) = ⨆ₙ fⁿ(⊥) = lfp f,
    the last step because dropping the `n = 0` term ⊥ from a set that already
    contains it does not change the l.u.b.  The chain manipulation is faithful
    but lengthy in core Lean; we state the theorem and defer its proof. -/
theorem lfp_isFixedPoint (L : CompleteLattice) (f : L.Carrier → L.Carrier)
    (hf : Continuous L.toDataType L.toDataType f) :
    f (lfp L f) = lfp L f := by
  sorry -- TODO: f(⨆ₙ fⁿ⊥) = ⨆ₙ fⁿ⁺¹⊥ = ⨆ₙ fⁿ⊥ = lfp f, via continuity of f

/-- `lfp f` is the *least* fixed point: it is below any other (pre)fixed point.

    Proof idea: if `f x ⊑ x` then by induction `fⁿ(⊥) ⊑ x` for all `n`
    (base ⊥ ⊑ x by `bot_le`), so `x` is an upper bound of the iterate chain and
    hence `lfp f = ⨆ₙ fⁿ(⊥) ⊑ x`. -/
theorem lfp_le_of_prefixed (L : CompleteLattice) (f : L.Carrier → L.Carrier)
    (hf : Monotone L.toDataType L.toDataType f)
    {x : L.Carrier} (hx : (f x ⊑[L.toDataType] x)) :
    (lfp L f) ⊑[L.toDataType] x := by
  have hub : IsUpperBound L.toDataType (iterateChain L f) x := by
    intro y hy
    obtain ⟨n, hn⟩ := hy
    -- fⁿ(⊥) ⊑ x by induction on n
    have key : ∀ m, (iterate f m (L.bot)) ⊑[L.toDataType] x := by
      intro m
      induction m with
      | zero => exact L.bot_le x
      | succ k ih =>
          -- fᵏ⁺¹(⊥) = f(fᵏ(⊥)) ⊑ f(x) ⊑ x
          exact L.le_trans (hf ih) hx
    exact hn ▸ key n
  exact (L.sup_isLUB (iterateChain L f)).2 hub

/-! ## Section 5.  Constructions of data types (product, sum, function space).

    "Suppose D and D' are two given data types.  There are three particularly
     important constructs: (D × D'), (D + D'), (D → D')."

    We record the product ordering faithfully.

        "⟨x,x'⟩ ⊑ ⟨y,y'⟩ iff x ⊑ y and x' ⊑' y'." -/
def prod (D E : DataType) : DataType where
  Carrier := D.Carrier × E.Carrier
  le := fun p q => (p.1 ⊑[D] q.1) ∧ (p.2 ⊑[E] q.2)
  le_refl := fun p => ⟨D.le_refl p.1, E.le_refl p.2⟩
  le_trans := fun h₁ h₂ => ⟨D.le_trans h₁.1 h₂.1, E.le_trans h₁.2 h₂.2⟩
  le_antisymm := fun {p q} h₁ h₂ => by
    have hx : p.1 = q.1 := D.le_antisymm h₁.1 h₂.1
    have hy : p.2 = q.2 := E.le_antisymm h₁.2 h₂.2
    -- pairs equal componentwise
    cases p; cases q; cases hx; cases hy; rfl

/-! The function space `(D → D')` has as elements all the continuous mappings,
    ordered pointwise:

        "f ⊑ g iff f(x) ⊑' g(x) for all x ∈ D."

    We bundle a continuous map with its continuity proof, and order pointwise.
    Antisymmetry needs function extensionality plus proof irrelevance for the
    bundled continuity witness; we record the underlying pointwise order as a
    `DataType` on the *raw* function space (Axiom 1 for `D → D'`). -/
def funPointwise (D E : DataType) : DataType where
  Carrier := D.Carrier → E.Carrier
  le := fun f g => ∀ x, (f x ⊑[E] g x)
  le_refl := fun f x => E.le_refl (f x)
  le_trans := fun hfg hgh x => E.le_trans (hfg x) (hgh x)
  le_antisymm := fun {f g} hfg hgf => by
    funext x
    exact E.le_antisymm (hfg x) (hgf x)

/-! ## Section 5, p. 18–20.  Recursive domain equations.

    "each element of D^ω can be regarded as a (continuous!) function on D^ω into
     D^ω … D^ω = (D^ω → D^ω)" and "V = N + R + L + V* + C + P".

    These reflexive/recursive domain equations are the deep constructions of the
    paper (the first mathematical model of the λ-calculus).  They are far beyond
    a core-Lean skeleton and are recorded here only as a comment; no `def` or
    theorem is asserted about their existence. -/

end Scott1970
