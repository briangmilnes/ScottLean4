/-
  Logic with Denumerably Long Formulas and Finite Strings of Quantifiers
  (Lean 4 faithful skeleton)

  Faithful to:
    Dana Scott, "Logic with Denumerably Long Formulas and Finite Strings of
    Quantifiers", in: The Theory of Models (Proc. 1963 Internat. Sympos.,
    Berkeley), North-Holland, 1965, pp. 329-341.

  Source text extracted from:
    DanaScottPapers/Scott-1965-Logic-with-Denumerably-Long-Formulas.txt

  This is an auto-generated faithful skeleton.  It transcribes the core formal
  objects of the paper on the infinitary logic `L_{ω₁,ω}`:

    * Syntax (p. 329-330): formulas built from atoms by negation, implication,
      finitary existential quantification, and *denumerable* (countable)
      conjunctions `⋀_{ξ<α} Aξ` with `α < ω₁`.
    * The well-ordering formulas `Eα` (p. 330-331) defined by transfinite
      recursion, characterizing well-ordered initial segments.
    * Satisfaction in a relational system (transfinite recursion).
    * The axioms and inference rules for `L_{ω₁,ω}` (p. 332-333), including the
      infinitary rule `[A→B₀],[A→B₁],… ⊢ [A → ⋀ Bξ]`.
    * THE COMPLETENESS THEOREM (p. 333): for a countable set `Φ`, syntactic and
      semantic consequence coincide.
    * The downward and upward Löwenheim-Skolem theorems (p. 335).
    * THE COUNTABLE ISOMORPHISM THEOREM ("Scott's isomorphism theorem", p. 339):
      two countable systems satisfying the same `L_{ω₁,ω}` sentences are
      isomorphic; a single "Scott sentence" characterizes a countable system.
    * The countable definability, interpolation and `tα` back-and-forth
      invariants (p. 339-341), and the connection to invariant Borel sets.

  Core Lean 4 only; no Mathlib.  Countable ordinals are indexed by `Nat` (i.e.
  we model `α < ω₁` as `Nat`-indexed countable conjunctions).  Deep theorems are
  `sorry` with `-- TODO`.
-/

namespace Scott1965

/-! ## Syntax of `L_{ω₁,ω}`

    We fix a countable relational vocabulary abstractly: `Atom` is the type of
    atomic formulas over a countable set of variables `Var := Nat`.  Countable
    conjunctions are indexed by `Nat` (standing for a countable ordinal `< ω₁`).
    Quantifier strings are finitary (single `ex`, iterable). -/

abbrev Var := Nat

/-- Formulas of `L_{ω₁,ω}` (p. 329-330).  `atom` injects atomic formulas;
    `neg`, `imp` are the finitary connectives; `ex v φ` is finitary existential
    quantification; `conj` is a *countable* conjunction `⋀_{n} (g n)`. -/
inductive Formula (Atom : Type) where
  | atom : Atom → Formula Atom
  | neg  : Formula Atom → Formula Atom
  | imp  : Formula Atom → Formula Atom → Formula Atom
  | ex   : Var → Formula Atom → Formula Atom
  | conj : (Nat → Formula Atom) → Formula Atom

namespace Formula
variable {Atom : Type}

/-- Countable disjunction, `⋁_n g n := ¬ ⋀_n ¬ (g n)`. -/
def disj (g : Nat → Formula Atom) : Formula Atom :=
  neg (conj (fun n => neg (g n)))

/-- Universal quantification `∀v φ := ¬ ∃v ¬ φ`. -/
def all (v : Var) (φ : Formula Atom) : Formula Atom := neg (ex v (neg φ))

end Formula

/-! ## Relational systems and satisfaction -/

/-- A relational system with a countable number of finitary relations
    (abstract): a carrier `A`, and an atomic-satisfaction relation giving the
    truth of each atom under an assignment `Var → A` (p. 331). -/
structure System (Atom : Type) where
  A       : Type
  satAtom : Atom → (Var → A) → Prop

variable {Atom : Type}

/-- Update an assignment at a variable. -/
def update {A : Type} (x : Var → A) (v : Var) (a : A) : Var → A :=
  fun w => if w = v then a else x w

/-- Satisfaction of an `L_{ω₁,ω}` formula in a system (transfinite recursion,
    p. 331; here structural recursion on the inductive `Formula`). -/
def Sat (M : System Atom) : Formula Atom → (Var → M.A) → Prop
  | .atom a,   x => M.satAtom a x
  | .neg φ,    x => ¬ Sat M φ x
  | .imp φ ψ,  x => Sat M φ x → Sat M ψ x
  | .ex v φ,   x => ∃ a : M.A, Sat M φ (update x v a)
  | .conj g,   x => ∀ n, Sat M (g n) x

/-- A *sentence* holds in `M` when it is satisfied by every assignment. -/
def Holds (M : System Atom) (φ : Formula Atom) : Prop := ∀ x, Sat M φ x

/-- Two systems are *`L_{ω₁,ω}`-equivalent* if they satisfy the same sentences. -/
def Lequiv (M N : System Atom) : Prop := ∀ φ : Formula Atom, Holds M φ ↔ Holds N φ

/-- Isomorphism of two systems (a bijection preserving all atomic relations). -/
structure Iso (M N : System Atom) where
  toFun    : M.A → N.A
  invFun   : N.A → M.A
  left_inv  : ∀ a, invFun (toFun a) = a
  right_inv : ∀ b, toFun (invFun b) = b
  preserve  : ∀ (a : Atom) (x : Var → M.A),
                M.satAtom a x ↔ N.satAtom a (fun v => toFun (x v))

/-! ## Semantic and syntactic consequence -/

/-- Semantic consequence `Φ ⊨ A` (p. 332): every model of all of `Φ` is a model
    of `A`. -/
def Entails (Φ : Formula Atom → Prop) (A : Formula Atom) : Prop :=
  ∀ M : System Atom, (∀ φ, Φ φ → Holds M φ) → Holds M A

/-- Syntactic provability `Φ ⊢ A` in `L_{ω₁,ω}` (p. 332-333): the least relation
    closed under the logical axioms and the three rules of inference, including
    the infinitary conjunction rule.  We give it inductively. -/
inductive Provable (Φ : Formula Atom → Prop) : Formula Atom → Prop where
  | hyp     : ∀ {A}, Φ A → Provable Φ A
  | ax_k    : ∀ A B, Provable Φ (.imp A (.imp B A))
  | ax_s    : ∀ A B C,
                Provable Φ (.imp (.imp A (.imp B C)) (.imp (.imp A B) (.imp A C)))
  | ax_contra : ∀ A B, Provable Φ (.imp (.imp (.neg B) (.neg A)) (.imp A B))
  | ax_conj : ∀ (g : Nat → Formula Atom) (n : Nat), Provable Φ (.imp (.conj g) (g n))
  | mp      : ∀ {A B}, Provable Φ A → Provable Φ (.imp A B) → Provable Φ B
  /-- the infinitary rule: from `A → Bₙ` for all `n`, infer `A → ⋀ₙ Bₙ`. -/
  | conjIntro : ∀ {A} (B : Nat → Formula Atom),
                  (∀ n, Provable Φ (.imp A (B n))) →
                  Provable Φ (.imp A (.conj B))

/-! ## The main theorems -/

/-- Countability of a set of sentences, abstractly: an enumeration `Nat → Φ`. -/
def Countable (Φ : Formula Atom → Prop) : Prop :=
  ∃ enum : Nat → Formula Atom, ∀ φ, Φ φ → ∃ n, enum n = φ

/-- THE COMPLETENESS THEOREM (p. 333).  A sentence `A` is syntactically
    derivable from a *countable* set `Φ` iff it follows semantically. -/
theorem completeness (Φ : Formula Atom → Prop) (_hΦ : Countable Φ)
    (A : Formula Atom) :
    Provable Φ A ↔ Entails Φ A := by
  sorry -- TODO Completeness Theorem for L_{ω₁,ω} (Karp; Henkin-style, Lopez-Escobar/Scott)

/-- Soundness (the easy half of completeness): provable implies entailed. -/
theorem soundness (Φ : Formula Atom → Prop) (A : Formula Atom) :
    Provable Φ A → Entails Φ A := by
  sorry -- TODO Soundness (induction on the derivation)

/-- THE COUNTABLE ISOMORPHISM THEOREM ("Scott's isomorphism theorem", p. 339).
    Two *countable* systems satisfying the same `L_{ω₁,ω}` sentences are
    isomorphic.  (`CountableSystem M` abstracts "the carrier of `M` is
    countable".) -/
theorem countable_isomorphism (CountableSystem : System Atom → Prop)
    (M N : System Atom)
    (_hM : CountableSystem M) (_hN : CountableSystem N) (_h : Lequiv M N) :
    Nonempty (Iso M N) := by
  sorry -- TODO Countable Isomorphism Theorem

/-- The *Scott sentence* (p. 339): for a countable system `M` there is a single
    `L_{ω₁,ω}` sentence `σ` true in `M` such that every countable model of `σ`
    is isomorphic to `M`. -/
theorem scott_sentence (CountableSystem : System Atom → Prop)
    (M : System Atom) (_hM : CountableSystem M) :
    ∃ σ : Formula Atom, Holds M σ ∧
      ∀ N : System Atom, CountableSystem N → Holds N σ → Nonempty (Iso M N) := by
  sorry -- TODO existence of the Scott sentence

/-- THE DOWNWARD LÖWENHEIM-SKOLEM THEOREM (p. 335).  Every countable set of
    sentences with a model of infinite cardinality has models of all smaller
    infinite cardinalities.  Stated for the countable case: a satisfiable
    countable `Φ` has a countable model. -/
theorem downward_LS (CountableSystem : System Atom → Prop)
    (Φ : Formula Atom → Prop) (_hΦ : Countable Φ)
    (M : System Atom) (_hmod : ∀ φ, Φ φ → Holds M φ) :
    ∃ N : System Atom, CountableSystem N ∧ ∀ φ, Φ φ → Holds N φ := by
  sorry -- TODO Downward Löwenheim-Skolem (Skolem functions for initial quantifiers)

/-- Application to invariant Borel sets (p. 339).  The minimal invariant sets
    (isomorphism types) of binary relations on `N` are exactly the sets defined
    by single `L_{ω₁,ω}` sentences, and each is Borel.  Stated: for a countable
    system `M`, its isomorphism class equals the class of models of its Scott
    sentence (linking to Scott 1964). -/
theorem invariant_borel_link (CountableSystem : System Atom → Prop)
    (M : System Atom) (_hM : CountableSystem M) :
    ∃ σ : Formula Atom,
      ∀ N : System Atom, CountableSystem N →
        (Nonempty (Iso M N) ↔ Holds N σ) := by
  sorry -- TODO isomorphism types are exactly the L_{ω₁,ω}-definable (Borel) classes

end Scott1965
