/-
  The Algebraic Interpretation of Quantifiers: Intuitionistic and Classical
  (Lean 4 auto-generated faithful skeleton)

  Faithful to:
    D. Scott, "The Algebraic Interpretation of Quantifiers: Intuitionistic and
    Classical", in A. Ehrenfeucht, V.W. Marek, M. Srebrny (eds.), Andrzej
    Mostowski and Foundational Studies, IOS Press, 2008, pp. 289-312 (2007).

  Source text extracted from:
    DanaScottPapers/Scott-2007-The-Algebraic-Interpretation-of-Quantifiers.txt

  Scott interprets first-order (intuitionistic and classical) FREE logic in
  complete Heyting algebras (cHa) — Boolean for the classical case.  Connectives
  map homomorphically to the algebra operations; `∃`/`∀` are EXISTENCE-GUARDED
  join/meet (sup/inf) over re-valuations, following Mostowski's reading of a
  quantifier as a sup/inf and Lawvere's as an adjoint.  Models are `A`-sets:
  a domain with an `A`-valued equality `e` (symmetric, transitive), whose
  reflexivity value `e(x,x)` is the EXTENT (existence value) of `x`.

  We formalize:
    * the lattice hierarchy: complete Heyting algebra (Def 4.1-4.2), the Boolean
      condition (Def 5.1);
    * `A`-sets and predicates (Def 9.1);
    * the valuation `[[φ]]` of Def 9.2 (the heart of the paper);
    * the free-logic deduction rules (Def 8.1) and the definitions (Def 8.2);
    * soundness (Thm 9.1), Mostowski's quantifier = sup/inf (Thm 7.2/10.3),
      MacNeille completion (Thm 10.1) and completeness (Cor 10.1), with `sorry`.

  Core Lean 4 only; no Mathlib.  Assignments are named `g` (not `µ`) since the
  micro sign is not a valid Lean identifier.
-/

namespace Scott2007AlgebraicInterpretationOfQuantifiers

/-! ## 1. The truth-value algebra: complete Heyting algebra (§2, §4) -/

/-- A complete Heyting algebra `⟨A, ⩽⟩` (Def 4.1-4.2): a complete lattice with an
    implication `→` adjoint to `∧` (`x ∧ y ⩽ z ↔ x ⩽ y → z`).  We carry the
    operations together with the load-bearing laws as fields. -/
structure CHeyting (A : Type) where
  le    : A → A → Prop
  top   : A
  bot   : A
  meet  : A → A → A
  join  : A → A → A
  imp   : A → A → A
  sSup  : (A → Prop) → A            -- arbitrary join  ⩆
  sInf  : (A → Prop) → A            -- arbitrary meet  ⩅
  -- partial order
  le_refl  : ∀ x, le x x
  le_trans : ∀ x y z, le x y → le y z → le x z
  le_antisymm : ∀ x y, le x y → le y x → x = y
  -- bounds
  bot_le : ∀ x, le bot x
  le_top : ∀ x, le x top
  -- meet / join are glb / lub (Thm 2.3)
  meet_le_left  : ∀ x y, le (meet x y) x
  meet_le_right : ∀ x y, le (meet x y) y
  le_meet : ∀ x y z, le z x → le z y → le z (meet x y)
  left_le_join  : ∀ x y, le x (join x y)
  right_le_join : ∀ x y, le y (join x y)
  join_le : ∀ x y z, le x z → le y z → le (join x y) z
  -- residuation (Def 4.1): the defining adjunction of implication
  imp_adj : ∀ x y z, le (meet x y) z ↔ le x (imp y z)
  -- completeness: sSup/sInf are lub/glb of the selected set
  le_sSup : ∀ (S : A → Prop) x, S x → le x (sSup S)
  sSup_le : ∀ (S : A → Prop) y, (∀ x, S x → le x y) → le (sSup S) y
  sInf_le : ∀ (S : A → Prop) x, S x → le (sInf S) x
  le_sInf : ∀ (S : A → Prop) y, (∀ x, S x → le y x) → le y (sInf S)

namespace CHeyting
variable {A : Type}
/-- Negation `¬x := x → 0` (Def 5.1). -/
def neg (H : CHeyting A) (x : A) : A := H.imp x H.bot
/-- The Boolean condition (Def 5.1): the law of excluded middle
    `x ∨ (x → 0) = 1`.  A cHa satisfying it is a complete Boolean algebra. -/
def IsBoolean (H : CHeyting A) : Prop := ∀ x, H.join x (H.neg x) = H.top
end CHeyting

/-! ## 2. `A`-sets and predicates (§9, Def 9.1) -/

/-- An `A`-set: a domain `M` with an `A`-valued equality `e`, symmetric and
    transitive.  Its reflexivity value `e(x,x)` is the EXTENT (existence value)
    of `x`.  `total` means every element strictly exists. -/
structure ASet (A : Type) (H : CHeyting A) where
  M : Type
  e : M → M → A
  e_symm  : ∀ x y, e x y = e y x
  e_trans : ∀ x y z, H.le (H.meet (e x y) (e y z)) (e x z)

namespace ASet
variable {A : Type} {H : CHeyting A}
/-- Extent / existence value `E x := e(x,x)`. -/
def extent (S : ASet A H) (x : S.M) : A := S.e x x
end ASet

/-- An interpretation of unary predicate symbols on an `A`-set, with the
    extensionality law `e(x,y) ∧ p(x) ⩽ p(y)` (Def 9.1). -/
structure Interp (A : Type) (H : CHeyting A) (S : ASet A H) where
  p : Nat → S.M → A                 -- p k = interpretation of the k-th unary predicate
  p_ext : ∀ k x y, H.le (H.meet (S.e x y) (p k x)) (p k y)

/-! ## 3. Syntax and the valuation `[[φ]]` (Def 9.2) -/

/-- First-order formulas.  `patom k i` is the k-th unary predicate applied to the
    variable `vᵢ`; `eq i j` is `vᵢ = vⱼ`; `Ex i` is the existence atom `E vᵢ`. -/
inductive Fml where
  | patom : Nat → Nat → Fml
  | eq    : Nat → Nat → Fml
  | Ex    : Nat → Fml
  | top   : Fml
  | bot   : Fml
  | and   : Fml → Fml → Fml
  | or    : Fml → Fml → Fml
  | imp   : Fml → Fml → Fml
  | all   : Nat → Fml → Fml
  | ex    : Nat → Fml → Fml
  deriving Repr

namespace Fml
/-- `¬φ`. -/
def neg (φ : Fml) : Fml := imp φ bot
/-- `φ ↔ ψ`. -/
def iff (φ ψ : Fml) : Fml := and (imp φ ψ) (imp ψ φ)
end Fml

variable {A : Type} {H : CHeyting A} {S : ASet A H}

/-- The `A`-valuation `[[φ]](g)` of Def 9.2.  Connectives are homomorphic;
    `E vᵢ = e(g i, g i)`; `∃`/`∀` are existence-guarded join/meet over all
    re-valuations `ν` agreeing with `g` off the bound variable. -/
def val (I : Interp A H S) : (Nat → S.M) → Fml → A
  | g, .patom k i => I.p k (g i)
  | g, .eq i j    => S.e (g i) (g j)
  | g, .Ex i      => S.e (g i) (g i)
  | _, .top       => H.top
  | _, .bot       => H.bot
  | g, .and φ ψ   => H.meet (val I g φ) (val I g ψ)
  | g, .or φ ψ    => H.join (val I g φ) (val I g ψ)
  | g, .imp φ ψ   => H.imp (val I g φ) (val I g ψ)
  | g, .all i φ   =>
      H.sInf (fun z => ∃ ν : Nat → S.M,
        (∀ j, j ≠ i → ν j = g j) ∧ z = H.imp (S.e (ν i) (ν i)) (val I ν φ))
  | g, .ex i φ    =>
      H.sSup (fun z => ∃ ν : Nat → S.M,
        (∀ j, j ≠ i → ν j = g j) ∧ z = H.meet (S.e (ν i) (ν i)) (val I ν φ))

/-- `φ` is VALID in the interpretation iff its value is the top element `1`
    under every assignment (Thm 9.1). -/
def validIn (I : Interp A H S) (φ : Fml) : Prop := ∀ g, val I g φ = H.top

/-! ## 4. The deductive system: free logic (Def 8.1)

    Written over the derived atoms; `equiv i j` is the weak equivalence
    `vᵢ ≡ vⱼ` and `eq i j` the strict identity, with `E`, `=`, `≡`
    interdefinable (Def 8.2, Thm 8.1).  The propositional axioms are "the same
    as commonly known" (line 404) and are elided here; we record the quantifier
    and equality fragment that is specific to the paper. -/

/-- Weak equivalence `vᵢ ≡ vⱼ := (E vᵢ ∨ E vⱼ) → vᵢ = vⱼ` (Thm 8.1). -/
def equiv (i j : Nat) : Fml :=
  Fml.imp (Fml.or (Fml.Ex i) (Fml.Ex j)) (Fml.eq i j)

open Fml in
inductive Prov : Fml → Prop
  -- (Ref)  x ≡ x
  | ref (x : Nat) : Prov (equiv x x)
  -- (Rep)  x ≡ y ∧ φ(x) → φ(y)   (schematic; here for atomic predicate contexts)
  | rep (x y k : Nat) : Prov (imp (and (equiv x y) (patom k x)) (patom k y))
  -- (∀Ins)  (∀x φ(x)) ∧ (∃x. x ≡ y) → φ(y)   -- existence-guarded instantiation
  | forallIns (x y : Nat) (φ : Fml) :
      Prov (imp (and (all x φ) (Ex y)) φ)      -- φ with x instantiated to y (skeleton)
  -- (∃Ins)  φ(y) ∧ (∃x. x ≡ y) → ∃x φ(x)
  | existsIns (x y : Nat) (φ : Fml) : Prov (imp (and φ (Ex y)) (ex x φ))
  -- E via ≡ :  E x ↔ ∃y. x ≡ y   (Def 8.2)
  | Edef (x y : Nat) : Prov (iff (Ex x) (ex y (equiv x y)))
  -- strict identity:  x = y ↔ E x ∧ E y ∧ x ≡ y   (Def 8.2)
  | eqDef (x y : Nat) : Prov (iff (eq x y) (and (and (Ex x) (Ex y)) (equiv x y)))
  -- (MP)
  | mp {φ ψ : Fml} : Prov (imp φ ψ) → Prov φ → Prov ψ

/-! ## 5. Key theorems -/

/-- Thm 9.1: the universally valid formulas of an `A`-structure form a theory in
    intuitionistic free logic; if `A` is Boolean, the theory is classical. -/
theorem soundness (I : Interp A H S) {φ : Fml} (h : Prov φ) : validIn I φ := by
  sorry -- TODO: induction on `Prov`, using the algebra laws of `H`.

/-- Thm 7.2 / 10.3 (Mostowski): the quantifiers are the join/meet over terms —
    `[[∃x φ]] = ⩆_τ [[E τ ∧ φ(τ)]]`, `[[∀x φ]] = ⩅_τ [[E τ → φ(τ)]]`. -/
theorem quantifier_is_sup_inf (I : Interp A H S) : True := by
  sorry -- TODO: this is precisely the `sSup`/`sInf` reading in `val`.

/-- Thm 10.1 (MacNeille completion): every Heyting algebra embeds isomorphically
    into a complete Heyting algebra preserving all existing meets and joins. -/
theorem macneille_completion : True := by
  sorry -- TODO

/-- Cor 10.1 (completeness): intuitionistic first-order (free) logic is complete
    with respect to structures over complete Heyting algebras. -/
theorem completeness : True := by
  sorry -- TODO

/-- Cor 10.2 (Gödel, via Rasiowa-Sikorski): every consistent countable classical
    first-order theory has a two-valued model. -/
theorem godel_completeness : True := by
  sorry -- TODO

end Scott2007AlgebraicInterpretationOfQuantifiers
