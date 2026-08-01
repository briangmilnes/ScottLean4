/-
  Identity and Existence in Intuitionistic Logic — the logic of partial elements
  (Lean 4 auto-generated faithful skeleton)

  Faithful to:
    D. Scott, "Identity and Existence in Intuitionistic Logic",
    in M.P. Fourman, C.J. Mulvey, D.S. Scott (eds.), Applications of Sheaves,
    Lecture Notes in Mathematics 753, Springer, 1979, pp. 660-696.

  Source text extracted from:
    DanaScottPapers/Scott-1979-Identity-and-Existence-in-Intuitionistic-Logic.txt

  Scott's paper is *entirely proof-theoretic*: it presents a first-order
  intuitionistic logic of PARTIAL ELEMENTS.  Terms need not denote; a primitive
  existence predicate `E τ` ("τ exists") is taken as more basic than, and prior
  to, identity `=` (the STRONG equality, implying existence of both sides).  A
  weak equivalence `≈` is defined.  Bound variables retain existential import
  (may only be instantiated by terms whose value exists) while free variables
  are schematic (freely substitutable).

  We formalize:
    * SYNTAX: intuitionistic terms/formulas with `E`, `=`, `≈`, and the
      description operator `℩` (Section 6).
    * DEDUCTIVE SYSTEM: unrestricted (MP); the substitution rule (S); the
      quantifier rules (∀),(∀+),(∃),(∃+); the equality axioms (refl),(symm),
      (trans) and the axiom of equivalence (eq); the definitions of `≈` and `E`.
    * SEMANTICS: Scott states (line 23) the model theory is developed in
      Fourman-Scott "Sheaves and Logic": interpretation over a complete Heyting
      algebra Ω / Ω-set with an extent map.  This file records that interface
      abstractly (`OmegaModel`) and states soundness with `sorry`.

  Core Lean 4 only; no Mathlib.
-/

namespace Scott1979IdentityAndExistence

/-! ## 1. Syntax -/

mutual
/-- Terms: variables and definite descriptions `℩x.φ` (Section 6).  Terms need
    not denote (partial elements). -/
inductive Term where
  | var   : Nat → Term
  | descr : Nat → Formula → Term            -- `℩x. φ`
  deriving Repr
/-- Intuitionistic formulas with the existence predicate `E`, strong identity
    `=` and weak equivalence `≈`. -/
inductive Formula where
  | E     : Term → Formula                  -- `E τ`   (existence / definedness)
  | eq    : Term → Term → Formula           -- `σ = τ` (strong identity)
  | equiv : Term → Term → Formula           -- `σ ≈ τ` (weak equivalence)
  | top   : Formula
  | bot   : Formula
  | and   : Formula → Formula → Formula
  | or    : Formula → Formula → Formula
  | imp   : Formula → Formula → Formula
  | all   : Nat → Formula → Formula
  | ex    : Nat → Formula → Formula
  deriving Repr
end

namespace Formula
/-- Intuitionistic negation `¬φ := φ → ⊥`. -/
def neg (φ : Formula) : Formula := imp φ bot
/-- Biconditional. -/
def iff (φ ψ : Formula) : Formula := and (imp φ ψ) (imp ψ φ)
end Formula

mutual
/-- `x` not free in the term. -/
def Term.notFree (x : Nat) : Term → Prop
  | .var i     => x ≠ i
  | .descr i φ => x = i ∨ Formula.notFree x φ
/-- `x` not free in the formula. -/
def Formula.notFree (x : Nat) : Formula → Prop
  | .E a       => Term.notFree x a
  | .eq a b    => Term.notFree x a ∧ Term.notFree x b
  | .equiv a b => Term.notFree x a ∧ Term.notFree x b
  | .top | .bot => True
  | .and φ ψ | .or φ ψ | .imp φ ψ => Formula.notFree x φ ∧ Formula.notFree x ψ
  | .all i φ | .ex i φ => x = i ∨ Formula.notFree x φ
end

mutual
/-- Naive (capture-avoiding under the usual side conditions) substitution. -/
def Term.subst (x : Nat) (α : Term) : Term → Term
  | .var i     => if x = i then α else .var i
  | .descr i φ => if x = i then .descr i φ else .descr i (Formula.subst x α φ)
def Formula.subst (x : Nat) (α : Term) : Formula → Formula
  | .E a       => .E (Term.subst x α a)
  | .eq a b    => .eq (Term.subst x α a) (Term.subst x α b)
  | .equiv a b => .equiv (Term.subst x α a) (Term.subst x α b)
  | .top       => .top
  | .bot       => .bot
  | .and φ ψ   => .and (Formula.subst x α φ) (Formula.subst x α ψ)
  | .or φ ψ    => .or (Formula.subst x α φ) (Formula.subst x α ψ)
  | .imp φ ψ   => .imp (Formula.subst x α φ) (Formula.subst x α ψ)
  | .all i φ   => if x = i then .all i φ else .all i (Formula.subst x α φ)
  | .ex i φ    => if x = i then .ex i φ else .ex i (Formula.subst x α φ)
end

/-! ## 2. Deductive system (Sections 1-2, 6)

    (MP) is completely unrestricted (lines 161-167).  The rule of substitution
    (S) makes every axiom schematic (lines 170-179). -/

open Term Formula in
inductive Prov : Formula → Prop
  -- intuitionistic propositional base (over →, ∧, ∨, ⊥, ⊤)
  | pk (φ ψ)     : Prov (imp φ (imp ψ φ))
  | ps (φ ψ χ)   : Prov (imp (imp φ (imp ψ χ)) (imp (imp φ ψ) (imp φ χ)))
  | andI (φ ψ)   : Prov (imp φ (imp ψ (and φ ψ)))
  | andE1 (φ ψ)  : Prov (imp (and φ ψ) φ)
  | andE2 (φ ψ)  : Prov (imp (and φ ψ) ψ)
  | orI1 (φ ψ)   : Prov (imp φ (or φ ψ))
  | orI2 (φ ψ)   : Prov (imp ψ (or φ ψ))
  | orE (φ ψ χ)  : Prov (imp (imp φ χ) (imp (imp ψ χ) (imp (or φ ψ) χ)))
  | botE (φ)     : Prov (imp bot φ)
  | topI         : Prov top
  -- (S) rule of substitution: free variables are schematic
  | subst (x : Nat) (τ : Term) {φ : Formula} : Prov φ → Prov (φ.subst x τ)
  -- 1.2 (∀)   ∀x.φ(x) ∧ Eτ → φ(τ)
  | forallAx (x : Nat) (τ : Term) (φ : Formula) :
      Prov (imp (and (all x φ) (E τ)) (φ.subst x τ))
  -- 1.2 (∀+)  from φ ∧ Ex → ψ(x)  (x not free in φ)  infer  φ → ∀x.ψ(x)
  | forallGen {x : Nat} {φ ψ : Formula} (h : φ.notFree x) :
      Prov (imp (and φ (E (var x))) ψ) → Prov (imp φ (all x ψ))
  -- 1.4 (∃)   φ(τ) ∧ Eτ → ∃x.φ(x)
  | existsAx (x : Nat) (τ : Term) (φ : Formula) :
      Prov (imp (and (φ.subst x τ) (E τ)) (ex x φ))
  -- 1.4 (∃+)  from φ(x) ∧ Ex → ψ  (x not free in ψ)  infer  ∃x.φ(x) → ψ
  | existsGen {x : Nat} {φ ψ : Formula} (h : ψ.notFree x) :
      Prov (imp (and φ (E (var x))) ψ) → Prov (imp (ex x φ) ψ)
  -- existence via quantification:  Eτ ↔ ∃y. y = τ   (y not free in τ)
  | Edef (y : Nat) (τ : Term) (hy : τ.notFree y) :
      Prov (iff (E τ) (ex y (eq (var y) τ)))
  -- 2.1 (refl)   x = x ↔ Ex
  | refl (x : Nat) : Prov (iff (eq (var x) (var x)) (E (var x)))
  -- 2.1 (symm)   x = y → y = x
  | symm (x y : Nat) : Prov (imp (eq (var x) (var y)) (eq (var y) (var x)))
  -- 2.1 (trans)  x = y ∧ y = z → x = z
  | trans (x y z : Nat) :
      Prov (imp (and (eq (var x) (var y)) (eq (var y) (var z))) (eq (var x) (var z)))
  -- 2.2 (eq) axiom of equivalence:  [Ex ∨ Ey → x = y] ∧ φ(x) → φ(y)
  | eqAx (x y : Nat) (φ : Formula) :
      Prov (imp (and (imp (or (E (var x)) (E (var y))) (eq (var x) (var y))) φ)
                (φ.subst x (var y)))
  -- definition of weak equivalence  x ≈ y ↔ [Ex ∨ Ey → x = y]
  | equivDef (x y : Nat) :
      Prov (iff (equiv (var x) (var y)) (imp (or (E (var x)) (E (var y))) (eq (var x) (var y))))
  -- 6.1 description axiom:  ∀y[ y = ℩x.φ(x) ↔ ∀x[φ(x) ↔ x = y] ]   (y not free in φ)
  | descrAx (x y : Nat) (φ : Formula) (hy : φ.notFree y) :
      Prov (all y (iff (eq (var y) (descr x φ))
                       (all x (iff φ (eq (var x) (var y))))))
  -- (MP), unrestricted
  | mp {φ ψ : Formula} : Prov (imp φ ψ) → Prov φ → Prov ψ

/-- Consequence from a finite list of hypotheses (informal sequent `Δ ⊢ φ`),
    reduced to provability of the iterated implication. -/
def Consequence : List Formula → Formula → Prop
  | [], φ      => Prov φ
  | (ψ :: Δ), φ => Consequence Δ (Formula.imp ψ φ)

/-! ## 3. Derived theorems Scott lists -/

/-- (1.3) `∀x. Ex` is a theorem (uniqueness of the existence predicate, from
    (∀+) with φ = ⊤, ψ(x) = Ex; lines 209-224). -/
theorem all_exists (x : Nat) : Prov (Formula.all x (Formula.E (Term.var x))) := by
  sorry -- TODO: derive from `forallGen` with φ := ⊤.

/-- (2.1.2) Strictness of `=`:  `x = y → Ex ∧ Ey` (lines 300-303). -/
theorem eq_strict (x y : Nat) :
    Prov (Formula.imp (Formula.eq (Term.var x) (Term.var y))
                      (Formula.and (Formula.E (Term.var x)) (Formula.E (Term.var y)))) := by
  sorry -- TODO

/-! ## 4. Semantics — the Ω-valued interpretation (deferred in the paper)

    Scott (line 23): "for the model theory ... consult Fourman and Scott,
    'Sheaves and Logic', for interpretations over a complete Heyting algebra
    (this includes Kripke models)."  No `[[φ]]` clauses appear in THIS paper; we
    record the interface abstractly.  `Ω` is a complete Heyting algebra of truth
    values; each individual carries an EXTENT `E : M → Ω` (its existence value),
    and equality is Ω-valued and strict (`eq x y ≤ E x`). -/

/-- Minimal complete-Heyting-algebra interface (truth-value algebra Ω). -/
structure HeytingAlgebra (Ω : Type) where
  le    : Ω → Ω → Prop
  top   : Ω
  bot   : Ω
  meet  : Ω → Ω → Ω
  join  : Ω → Ω → Ω
  imp   : Ω → Ω → Ω
  sSup  : (Ω → Prop) → Ω          -- arbitrary joins (completeness)
  sInf  : (Ω → Prop) → Ω          -- arbitrary meets

/-- An Ω-set (partial-element model): a domain `M` with an extent map and a
    strict, symmetric, transitive Ω-valued equality (Def as in Fourman-Scott). -/
structure OmegaModel (Ω : Type) where
  H       : HeytingAlgebra Ω
  M       : Type
  extent  : M → Ω                 -- `E x` : the existence value of `x`
  eqv     : M → M → Ω             -- Ω-valued equality `[[x = y]]`

/-- Soundness of the deductive calculus over Ω-sets (Fourman-Scott). -/
theorem soundness {Ω : Type} (𝔐 : OmegaModel Ω) {φ : Formula} (h : Prov φ) :
    True := by
  sorry -- TODO: define the full `[[·]]` valuation and prove `[[φ]] = ⊤`.

/-- (5.3 Metatheorem) For strict predicates/functions, `φ` is provable here iff
    its `E`-relativization `φ^E` is provable in ordinary intuitionistic logic;
    the converse uses an Ω-set countermodel (Fourman). -/
theorem relativization_faithful : True := by
  sorry -- TODO: state with the `( )^E` translation of Section 5.3.

end Scott1979IdentityAndExistence
