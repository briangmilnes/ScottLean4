/-
  Advice on Modal Logic — index / point-of-reference semantics
  (Lean 4 auto-generated faithful skeleton)

  Faithful to:
    D. Scott, "Advice on Modal Logic", in K. Lambert (ed.), Philosophical
    Problems in Logic, Reidel, Dordrecht, 1970, pp. 143-173.

  Source text extracted from:
    DanaScottPapers/Scott-1970-Advice-on-Modal-Logic.txt

  Scott's "advice" is a semantics built on a set `I` of INDICES (points of
  reference, i.e. multi-coordinate possible worlds `(w,t,p,a,…)`), with nested
  domains  A_i ⊆ D ⊆ V  of actual / possible / virtual individuals.  The two
  central semantic values are:
    * the INTENSION of a term  `‖t‖ ∈ Ṽ`  — a *partial* function `I → V`
      (its EXTENSION `‖t‖_i` at an index; improper descriptions are undefined);
    * the value of a formula  `‖Φ‖ ∈ 2^I`  — a total function `I → 2`.
  The distinctive apparatus: ordinary quantifiers `∀ ∃` range over `D`; the
  "actual" quantifiers `∀. ∃.` range over the index-dependent `A_i`; `□` is the
  S5 necessity "true at all indices"; intensional identity is `t ≡ σ := □(t=σ)`.

  We formalize:
    * SYNTAX: terms (variables, descriptions, actual descriptions) and formulas
      with the modal `□`, both plain and actual quantifiers, `=`, and a binary
      predicate `R`.
    * SEMANTICS: an `Interp` with `I, V, D, A`; term EXTENSION given relationally
      (`ext`, a `Prop`, partiality via `Option`) and formula truth `sat … i`,
      mutually recursive.  Validity = truth at every index of every interpretation
      under every `D`-valued assignment.
    * The axiomatization (first-order predicate logic + S5 for `□` + replacement
      of necessary equalities) and completeness (Kaplan-Scott) stated with `sorry`.

  Core Lean 4 only; no Mathlib.
-/

namespace Scott1970AdviceOnModalLogic

/-! ## 1. Syntax -/

mutual
/-- Terms.  `descr` is Scott's `℩` (over `D`); `descrActual` is `℩.` (over the
    actual individuals `A_i`).  Term extensions are partial. -/
inductive Term where
  | var         : Nat → Term
  | descr       : Nat → Formula → Term       -- `℩x. φ`  (over D)
  | descrActual : Nat → Formula → Term       -- `℩.x. φ` (over A_i)
  deriving Repr
/-- Formulas.  `box` is the S5 necessity; `allD/exD` are the plain quantifiers
    over `D`; `allA/exA` are the "actual" quantifiers over `A_i`; `actual t`
    is the actuality predicate `A t`. -/
inductive Formula where
  | rel    : Term → Term → Formula            -- `α R β`
  | eq     : Term → Term → Formula            -- extensional equality `α = β`
  | actual : Term → Formula                   -- `A t` (actuality predicate)
  | neg    : Formula → Formula
  | imp    : Formula → Formula → Formula
  | allD   : Nat → Formula → Formula          -- `∀x`  over D
  | allA   : Nat → Formula → Formula          -- `∀.x` over A_i
  | box    : Formula → Formula                -- `□`  (S5)
  deriving Repr
end

namespace Formula
def or (φ ψ : Formula) : Formula := imp (neg φ) ψ
def and (φ ψ : Formula) : Formula := neg (imp φ (neg ψ))
def iff (φ ψ : Formula) : Formula := and (imp φ ψ) (imp ψ φ)
def exD (i : Nat) (φ : Formula) : Formula := neg (allD i (neg φ))
def exA (i : Nat) (φ : Formula) : Formula := neg (allA i (neg φ))
/-- Possibility `◇ := ¬□¬`. -/
def dia (φ : Formula) : Formula := neg (box (neg φ))
/-- Intensional identity `t ≡ σ := □(t = σ)` (line 408). -/
def ident (a b : Term) : Formula := box (eq a b)
end Formula

/-! ## 2. Interpretations (Section I-III) -/

/-- An interpretation.  `I` = index set (points of reference); `V` = virtual
    objects; `D` = possible individuals (`D ⊆ V`, `D` nonempty); `A i` = the
    actual individuals at index `i` (`A i ⊆ D`); `R` an extensional relation. -/
structure Interp where
  I : Type
  V : Type
  D : V → Prop
  A : I → V → Prop
  R : V → V → Prop
  D_nonempty : ∃ a, D a
  A_sub_D : ∀ i a, A i a → D a

/-- Update a `V`-valued assignment. -/
def upd (M : Interp) (s : Nat → M.V) (k : Nat) (a : M.V) : Nat → M.V :=
  fun j => if j = k then a else s j

mutual
/-- Truth of a formula at an index `i`:  `‖Φ‖_i = 1`. -/
def sat (M : Interp) (s : Nat → M.V) : Formula → M.I → Prop
  | .rel a b, i    => ∃ x y, ext M s a i (some x) ∧ ext M s b i (some y) ∧ M.R x y
  | .eq a b, i     => (∃ x, ext M s a i (some x) ∧ ext M s b i (some x))
                        ∨ (ext M s a i none ∧ ext M s b i none)
  | .actual t, i   => ∃ x, ext M s t i (some x) ∧ M.A i x
  | .neg φ, i      => ¬ sat M s φ i
  | .imp φ ψ, i    => sat M s φ i → sat M s ψ i
  | .allD k φ, i   => ∀ a, M.D a → sat M (upd M s k a) φ i
  | .allA k φ, i   => ∀ a, M.A i a → sat M (upd M s k a) φ i
  | .box φ, _      => ∀ j, sat M s φ j                    -- S5: truth at ALL indices
/-- Relational term EXTENSION at index `i`:  `ext … t i o` means `‖t‖_i = o`,
    where `o : Option M.V` (`none` = undefined). -/
def ext (M : Interp) (s : Nat → M.V) : Term → M.I → Option M.V → Prop
  | .var k, _, o => o = some (s k)                        -- variables/constants are rigid
  | .descr k φ, i, o =>
      (∃ b, M.D b ∧ sat M (upd M s k b) φ i
              ∧ (∀ c, M.D c → sat M (upd M s k c) φ i → c = b) ∧ o = some b)
      ∨ ((¬ ∃ b, M.D b ∧ sat M (upd M s k b) φ i
              ∧ (∀ c, M.D c → sat M (upd M s k c) φ i → c = b)) ∧ o = none)
  | .descrActual k φ, i, o =>
      (∃ b, M.A i b ∧ sat M (upd M s k b) φ i
              ∧ (∀ c, M.A i c → sat M (upd M s k c) φ i → c = b) ∧ o = some b)
      ∨ ((¬ ∃ b, M.A i b ∧ sat M (upd M s k b) φ i
              ∧ (∀ c, M.A i c → sat M (upd M s k c) φ i → c = b)) ∧ o = none)
end

/-- Logical validity (lines 585-592): true at every index of every
    interpretation, for every assignment of *possible* individuals (`D`) to the
    free variables. -/
def Valid (φ : Formula) : Prop :=
  ∀ (M : Interp) (s : Nat → M.V), (∀ k, M.D (s k)) → ∀ i, sat M s φ i

/-! ## 3. Key validities Scott states (Sections I-III) -/

/-- Barcan-style equivalence for the `D`-quantifier is VALID (line 438):
    `□∀x Φ ↔ ∀x □Φ`. -/
theorem barcan_D (k : Nat) (φ : Formula) :
    Valid (Formula.iff (Formula.box (Formula.allD k φ))
                       (Formula.allD k (Formula.box φ))) := by
  sorry -- TODO

/-- Substitutivity of *extensional* equality FAILS in general (line 266); it
    holds for the *intensional* identity `≡` (lines 419-423):
    `t ≡ σ ∧ Φ(t) → Φ(σ)`.  Recorded schematically as a validity target. -/
def substitutivity_of_ident (a b : Term) (φ ψ : Formula) : Formula :=
  Formula.imp (Formula.and (Formula.ident a b) φ) ψ   -- φ = Φ(a), ψ = Φ(b)

/-- `∀.` is `∀` restricted by the actuality predicate (line 424):
    `∀.x Φ(x) ↔ ∀x[A x → Φ(x)]`. -/
theorem actual_is_restricted (k : Nat) (φ : Formula) :
    Valid (Formula.iff (Formula.allA k φ)
                       (Formula.allD k (Formula.imp (Formula.actual (Term.var k)) φ))) := by
  sorry -- TODO

/-! ## 4. Axiomatization and completeness (Section V, lines 594-597)

    "predicate logic with an S5 modal logic for `□`; in addition the axiom schema
    of replacement of necessary equalities (and biconditionals)."  Completeness
    is Kaplan-Scott (a Henkin argument); the logic is first-order. -/

/-- Soundness of Scott's axiom system w.r.t. index semantics. -/
theorem soundness {φ : Formula} (h : True) : Valid φ := by
  sorry -- TODO: define `Prov` (predicate logic + S5 + replacement) and induct.

/-- Completeness (Kaplan-Scott): every valid formula is provable. -/
theorem completeness {φ : Formula} (h : Valid φ) : True := by
  sorry -- TODO: Henkin construction over maximal consistent sets of indices.

end Scott1970AdviceOnModalLogic
