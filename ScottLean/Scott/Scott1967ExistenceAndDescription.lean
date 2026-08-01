/-
  Existence and Description in Formal Logic — free logic with descriptions
  (Lean 4 auto-generated faithful skeleton)

  Faithful to:
    D. Scott, "Existence and Description in Formal Logic",
    in R. Schoenman (ed.), Bertrand Russell: Philosopher of the Century,
    Allen & Unwin, London, 1967, pp. 181-200.

  Source text extracted from:
    DanaScottPapers/Scott-1967-Existence-and-Description-in-Formal-Logic.txt

  This file transcribes the core formal system of Section 1: a first-order
  *free* logic (empty domains allowed; free variables and terms may denote
  outside the domain) over a single binary predicate `R`, with a definite
  description operator `I x. φ` and the derived existence predicate `E! α`.

  We formalize:
    * SYNTAX: mutually inductive terms and formulas; `descr` (Scott's `I`)
      embeds a formula into a term.
    * SEMANTICS: a `Structure` with a domain predicate `dom` (Principles 1-3:
      bound variables range over the domain, which may be empty; terms/free
      variables may take values outside it) and a null entity `star`.
      Satisfaction and (relational) term-value are mutually recursive.
    * DEDUCTIVE SYSTEM: the Hilbert calculus (S0)-(S4), (I1), (I2) with the
      rules (MP) and (UG).
    * Soundness / completeness stated with `sorry`.

  Core Lean 4 only; no Mathlib.  Because Scott's `I` embeds a formula inside a
  term, term-value is given RELATIONALLY (`tval`, a `Prop`) so that it can be
  defined by the same mutual recursion as satisfaction without a universe clash
  and without invoking choice.
-/

namespace Scott1967ExistenceAndDescription

/-! ## 1. Syntax (Section 1, lines 127-134)

    "(i) all variables are terms; (ii) if α and β are terms then `α = β` and
     `αRβ` are formulas; (iii) if Φ, Ψ are formulas and x a variable then ¬Φ,
     [Φ → Ψ], ∀x Φ are formulas, while `I x Φ` is a term." -/

mutual
/-- Terms: variables `vᵢ` and definite descriptions `I vᵢ. φ`. -/
inductive Term where
  | var   : Nat → Term
  | descr : Nat → Formula → Term       -- `I vᵢ φ`
  deriving Repr
/-- Formulas over the single binary predicate `R` and identity `=`. -/
inductive Formula where
  | rel : Term → Term → Formula         -- `α R β`
  | eq  : Term → Term → Formula         -- `α = β`
  | neg : Formula → Formula
  | imp : Formula → Formula → Formula
  | all : Nat → Formula → Formula       -- `∀ vᵢ φ`
  deriving Repr
end

namespace Formula

/-- `∃x Φ := ¬∀x¬Φ` (line 280). -/
def ex (i : Nat) (φ : Formula) : Formula := neg (all i (neg φ))
/-- `Φ ∧ Ψ := ¬[Φ → ¬Ψ]`. -/
def and (φ ψ : Formula) : Formula := neg (imp φ (neg ψ))
/-- `Φ ∨ Ψ := ¬Φ → Ψ`. -/
def or (φ ψ : Formula) : Formula := imp (neg φ) ψ
/-- `Φ ↔ Ψ`. -/
def iff (φ ψ : Formula) : Formula := and (imp φ ψ) (imp ψ φ)

/-- The existence predicate `E! α := ∃x[x = α]` for a fresh variable `x`
    (lines 316-324).  Semantically: the value of `α` lies in the domain. -/
def E! (freshx : Nat) (α : Term) : Formula := ex freshx (eq (Term.var freshx) α)

end Formula

/-- The canonical *improper* description `⋇ := I v. ¬ v = v` (line 342). -/
def improper (v : Nat) : Term := Term.descr v (Formula.neg (Formula.eq (Term.var v) (Term.var v)))

/-! ### Free variables and (naive) substitution

    Substitution `Φ(x/α)` is capture-avoiding in Scott's text (bound variables
    are renamed as needed, line 278).  We implement the standard *naive*
    substitution that refuses to descend under a binder of the same variable;
    faithful use assumes the side condition that `α` is free for `x`. -/

mutual
/-- `x` does not occur free in the term. -/
def Term.notFree (x : Nat) : Term → Prop
  | .var i     => x ≠ i
  | .descr i φ => x = i ∨ Formula.notFree x φ
/-- `x` does not occur free in the formula. -/
def Formula.notFree (x : Nat) : Formula → Prop
  | .rel a b => Term.notFree x a ∧ Term.notFree x b
  | .eq a b  => Term.notFree x a ∧ Term.notFree x b
  | .neg φ   => Formula.notFree x φ
  | .imp φ ψ => Formula.notFree x φ ∧ Formula.notFree x ψ
  | .all i φ => x = i ∨ Formula.notFree x φ
end

mutual
/-- Naive substitution `t(x/α)` of the term `α` for the variable `x`. -/
def Term.subst (x : Nat) (α : Term) : Term → Term
  | .var i     => if x = i then α else .var i
  | .descr i φ => if x = i then .descr i φ else .descr i (Formula.subst x α φ)
/-- Naive substitution `Φ(x/α)`. -/
def Formula.subst (x : Nat) (α : Term) : Formula → Formula
  | .rel a b => .rel (Term.subst x α a) (Term.subst x α b)
  | .eq a b  => .eq (Term.subst x α a) (Term.subst x α b)
  | .neg φ   => .neg (Formula.subst x α φ)
  | .imp φ ψ => .imp (Formula.subst x α φ) (Formula.subst x α ψ)
  | .all i φ => if x = i then .all i φ else .all i (Formula.subst x α φ)
end

/-! ## 2. Semantics (Section 1, lines 137-263) -/

/-- A structure `𝔄 = ⟨A, R⟩`.  `M` is the type of *all* values; `dom` picks out
    the domain `A` of properly existing individuals (allowed to be empty,
    Principle 2); `star` is the null entity `*_𝔄` with `¬ dom star`. -/
structure Structure (M : Type) where
  dom  : M → Prop
  R    : M → M → Prop
  star : M
  star_not_dom : ¬ dom star

/-- Update an assignment `s` at index `i`. -/
def upd {M : Type} (s : Nat → M) (i : Nat) (a : M) : Nat → M :=
  fun j => if j = i then a else s j

variable {M : Type}

mutual
/-- Satisfaction `⊨_𝔄 Φ[s]` (lines 251-260). -/
def sat (A : Structure M) (s : Nat → M) : Formula → Prop
  | .rel a b => ∃ x y, tval A s a x ∧ tval A s b y ∧ A.R x y
  | .eq a b  => ∃ x y, tval A s a x ∧ tval A s b y ∧ x = y
  | .neg φ   => ¬ sat A s φ
  | .imp φ ψ => sat A s φ → sat A s ψ
  | .all i φ => ∀ a, A.dom a → sat A (upd s i a) φ
/-- Relational term-value `‖α[s]‖_𝔄 = m`.  For a description `I vᵢ φ`: `m` is
    the unique domain element making `φ` true (`upd s i m`), and otherwise
    `m = star` (lines 257-260). -/
def tval (A : Structure M) (s : Nat → M) : Term → M → Prop
  | .var i, m => m = s i
  | .descr i φ, m =>
      (A.dom m ∧ sat A (upd s i m) φ ∧ ∀ b, A.dom b → sat A (upd s i b) φ → b = m)
      ∨ ((¬ ∃ a, A.dom a ∧ sat A (upd s i a) φ ∧ ∀ b, A.dom b → sat A (upd s i b) φ → b = a)
          ∧ m = A.star)
end

/-- Validity in a structure: true under every assignment (line 261). -/
def validIn (A : Structure M) (φ : Formula) : Prop := ∀ s, sat A s φ

/-- Universal validity `⊨ Φ`: valid in every structure over every value type
    (lines 262-263). -/
def Valid (φ : Formula) : Prop := ∀ (M : Type) (A : Structure M), validIn A φ

/-! ## 3. Deductive system (Section 1, lines 267-346)

    Rules (MP), (UG); axiom schemata (S0)-(S4), (I1), (I2).  Scott states (S0)
    as "any tautology"; we present the standard Łukasiewicz axioms for classical
    propositional logic (over the primitives `¬`, `→`), which — with (MP) —
    axiomatize exactly the tautologies. -/

open Term Formula in
/-- The provable (universally valid) formulas. -/
inductive Prov : Formula → Prop
  -- (S0) tautologies, via the Łukasiewicz basis for classical propositional logic
  | pk (φ ψ : Formula)   : Prov (imp φ (imp ψ φ))
  | ps (φ ψ χ : Formula) : Prov (imp (imp φ (imp ψ χ)) (imp (imp φ ψ) (imp φ χ)))
  | pdn (φ ψ : Formula)  : Prov (imp (imp (neg φ) (neg ψ)) (imp ψ φ))
  -- (S1)  ∀x[Φ → Ψ] → [∀x Φ → ∀x Ψ]
  | s1 (i : Nat) (φ ψ : Formula) :
      Prov (imp (all i (imp φ ψ)) (imp (all i φ) (all i ψ)))
  -- (S2)  ∀y ∃x[x = y]
  | s2 (y x : Nat) (h : x ≠ y) : Prov (all y (ex x (eq (var x) (var y))))
  -- (S3)  α = α
  | s3 (α : Term) : Prov (eq α α)
  -- (S4)  Φ(x/α) ∧ α = β → Φ(x/β)
  | s4 (x : Nat) (α β : Term) (φ : Formula) :
      Prov (imp (and (φ.subst x α) (eq α β)) (φ.subst x β))
  -- (I1)  ∀y[y = I x φ ↔ ∀x[x = y ↔ φ]]   (y not free in φ)
  | i1 (x y : Nat) (φ : Formula) (hy : φ.notFree y) :
      Prov (all y (iff (eq (var y) (descr x φ))
                       (all x (iff (eq (var x) (var y)) φ))))
  -- (I2)  ¬∃y[y = I x φ] → ⋇ = I x φ
  | i2 (x y v : Nat) (φ : Formula) :
      Prov (imp (neg (ex y (eq (var y) (descr x φ))))
                (eq (improper v) (descr x φ)))
  -- (MP)  modus ponens
  | mp {φ ψ : Formula} : Prov (imp φ ψ) → Prov φ → Prov ψ
  -- (UG)  from Φ → Ψ (x not free in Φ) infer Φ → ∀x Ψ
  | ug {x : Nat} {φ ψ : Formula} (h : φ.notFree x) :
      Prov (imp φ ψ) → Prov (imp φ (all x ψ))

/-! ## 4. The optional theory-specific axiom (line 380)

    (I3)  ⋇ = α ∨ ⋇ = β → ¬ αRβ   — valid exactly in structures with R ⊆ A × A.
    We record it as a schema; it is NOT universally valid. -/
def I3 (v : Nat) (α β : Term) : Formula :=
  Formula.imp (Formula.or (Formula.eq (improper v) α) (Formula.eq (improper v) β))
              (Formula.neg (Formula.rel α β))

/-! ## 5. Metatheorems (Section 1, completeness at lines 419-422) -/

/-- Soundness: every provable formula is universally valid. -/
theorem soundness {φ : Formula} (h : Prov φ) : Valid φ := by
  sorry -- TODO: induction on `Prov`; validity of (S0)-(S4),(I1),(I2) and rules.

/-- Completeness (Scott, Section 3, lines 748-751, specialized): every
    universally valid formula is provable. -/
theorem completeness {φ : Formula} (h : Valid φ) : Prov φ := by
  sorry -- TODO: Henkin-style term-model construction over a maximal consistent set.

end Scott1967ExistenceAndDescription
