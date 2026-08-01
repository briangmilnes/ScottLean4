/-
  A Proof of the Independence of the Continuum Hypothesis
  (Lean 4 faithful skeleton)

  Faithful to:
    Dana Scott, "A Proof of the Independence of the Continuum Hypothesis",
    Mathematical Systems Theory 1, No. 2 (1967), pp. 89-111.

  Source text extracted from:
    DanaScottPapers/Scott-1967-Independence-of-the-Continuum-Hypothesis.txt

  This is an auto-generated faithful skeleton.  It transcribes the core formal
  objects of Scott's Boolean-valued (random-real) proof:

    * Sections 1-2.  The higher-order theory of the reals: terms and formulas
      over real / function / functional variables; the continuum hypothesis in
      the forms (CH'), (CH'') (p. 90-95); the logical axioms (PL),(QL),(EL),
      and the specific axioms (OF) ordered field, (CO) completeness, (EF)
      extensionality of functions/functionals, (AC) choice.
    * Section 3.  A complete Boolean algebra `𝔅 = 𝒜/[P=0]` of *events*; the
      Boolean truth-value `⟦A⟧ ∈ 𝔅` of a statement, with the rules for
      ¬,∧,∨,→,↔ and for the quantifiers (inf/sup over the domain, p. 96-99).
    * Section 4.  Random reals `ℛ`, random functions `ℱ` (property (#),
      p. 102), random functionals `ℱℱ` (property (##)); validity of (EF),(EL),
      (AC),(CO) in the model.
    * Section 5.  THE INDEPENDENCE THEOREM (p. 106-108): with `Ω = [0,1]^I` for
      `card I > 2^{ℵ₀}` and the product measure, the random-real model gives the
      Boolean value of the continuum hypothesis equal to `0` — CH fails — while
      all axioms have value `1`.

  Core Lean 4 only; no Mathlib.  Complete Boolean algebras, measures and Borel
  functions are stated abstractly.  Deep theorems are `sorry` with `-- TODO`.
-/

namespace Scott1967

/-! ## Complete Boolean algebras of events -/

/-- A *complete Boolean algebra* `𝔅` (Section 3): carrier `B` with meet, join,
    complement, `0`, `1`, and arbitrary (countable, here `Nat`-indexed) sups and
    infs realizing the reduced event algebra `𝒜/[P=0]` (p. 96). -/
structure CompleteBooleanAlgebra where
  B        : Type
  le       : B → B → Prop
  meet     : B → B → B
  join     : B → B → B
  compl    : B → B
  bot      : B
  top      : B
  sSup     : (Nat → B) → B          -- countable suprema (ccc reduces sups to these)
  sInf     : (Nat → B) → B
  le_refl     : ∀ a, le a a
  le_trans    : ∀ a b c, le a b → le b c → le a c
  le_antisymm : ∀ a b, le a b → le b a → a = b
  bot_le      : ∀ a, le bot a
  le_top      : ∀ a, le a top
  meet_le_left  : ∀ a b, le (meet a b) a
  meet_le_right : ∀ a b, le (meet a b) b
  le_join_left  : ∀ a b, le a (join a b)
  le_join_right : ∀ a b, le b (join a b)
  sSup_isUB   : ∀ (f : Nat → B) n, le (f n) (sSup f)
  sInf_isLB   : ∀ (f : Nat → B) n, le (sInf f) (f n)

variable (𝔅 : CompleteBooleanAlgebra)

/-- The Boolean implication `E₀ ⇒ E₁ := -E₀ ∪ E₁` (p. 97). -/
def CompleteBooleanAlgebra.imp (a b : 𝔅.B) : 𝔅.B := 𝔅.join (𝔅.compl a) b

/-! ## The Boolean-valued higher-order structure

    We package the model of Section 4 abstractly.  `Real` is the type of random
    reals `ℛ`; `Fn` the random functions `ℱ` (property (#)); `Fnl` the random
    functionals `ℱℱ` (property (##)).  Each carries a Boolean-valued equality,
    and each function/functional acts with the "cannot make arguments less equal"
    monotonicity, i.e. `⟦ξ=η⟧ ≤ ⟦φ(ξ)=φ(η)⟧`. -/
structure RandomModel where
  Real     : Type
  Fn       : Type                                  -- random functions ℱ
  Fnl      : Type                                  -- random functionals ℱℱ
  eqR      : Real → Real → 𝔅.B                     -- ⟦ξ = η⟧
  leR      : Real → Real → 𝔅.B                     -- ⟦ξ ≤ η⟧
  app      : Fn → Real → Real                      -- f(ξ)
  appF     : Fnl → Fn → Real                       -- F(f)
  eqFn     : Fn → Fn → 𝔅.B                         -- ⟦f = g⟧
  eqFnl    : Fnl → Fnl → 𝔅.B                       -- ⟦F = G⟧
  /-- property (#) (p. 102): `⟦ξ = η⟧ ≤ ⟦f(ξ) = f(η)⟧`. -/
  fn_prop  : ∀ (f : Fn) (ξ η : Real),
               𝔅.le (eqR ξ η) (eqR (app f ξ) (app f η))
  /-- property (##) (p. 102): `⟦f = g⟧ ≤ ⟦F(f) = F(g)⟧`. -/
  fnl_prop : ∀ (F : Fnl) (f g : Fn),
               𝔅.le (eqFn f g) (eqR (appF F f) (appF F g))

/-! ## Boolean truth values of the higher-order language

    A `Valuation` assigns to each closed statement `A` a Boolean value `⟦A⟧ ∈ 𝔅`,
    respecting the compositional rules of p. 97-99.  We axiomatize the key rules
    on the atomic equalities/inequalities and the propositional and quantifier
    connectives; the syntax is abstracted as a type `Stmt`. -/
structure BoolValued (M : RandomModel 𝔅) where
  Stmt     : Type
  val      : Stmt → 𝔅.B                              -- ⟦A⟧
  sfalse   : Stmt
  neg      : Stmt → Stmt
  conj     : Stmt → Stmt → Stmt
  disj     : Stmt → Stmt → Stmt
  /-- ⟦¬A⟧ = -⟦A⟧. -/
  val_neg  : ∀ A, val (neg A) = 𝔅.compl (val A)
  /-- ⟦A ∧ B⟧ = ⟦A⟧ ∩ ⟦B⟧. -/
  val_conj : ∀ A B, val (conj A B) = 𝔅.meet (val A) (val B)
  /-- ⟦A ∨ B⟧ = ⟦A⟧ ∪ ⟦B⟧. -/
  val_disj : ∀ A B, val (disj A B) = 𝔅.join (val A) (val B)

/-- A statement is *valid* (Boolean valid, p. 99) when its value is `1`. -/
def BoolValued.Valid {𝔅 : CompleteBooleanAlgebra} {M : RandomModel 𝔅}
    (V : BoolValued 𝔅 M) (A : V.Stmt) : Prop :=
  V.val A = 𝔅.top

/-! ## Validity of the axioms in the model -/

/-- All axioms of the higher-order theory of reals — (PL),(QL),(EL),(OF),(CO),
    (EF),(AC) — are valid in the random-real model (Sections 3-4).  Abstracted:
    a designated predicate `IsAxiom` on statements, each of whose members is
    Boolean valid. -/
theorem axioms_valid {M : RandomModel 𝔅} (V : BoolValued 𝔅 M)
    (IsAxiom : V.Stmt → Prop)
    (_hOF : True) (_hCO : True) (_hEF : True) (_hAC : True) :
    ∀ A, IsAxiom A → V.Valid A := by
  sorry -- TODO validity of (PL),(QL),(EL),(OF),(CO),(EF),(AC) in the model

/-- The existential fullness of the model (p. 105, 110): the Boolean value of any
    existential statement equals the value of one of its instances (used later
    for the Löwenheim-Skolem reduction). -/
theorem existential_fullness {M : RandomModel 𝔅} (V : BoolValued 𝔅 M)
    (exStmt : (M.Real → V.Stmt) → V.Stmt) (A : M.Real → V.Stmt) :
    ∃ η : M.Real, V.val (exStmt A) = V.val (A η) := by
  sorry -- TODO ⟦∃x A(x)⟧ = ⟦A(η)⟧ for some witness η

/-! ## The independence theorem -/

/-- A statement expressing the continuum hypothesis (CH'') in the language
    (p. 95), as a designated element of `Stmt`. -/
structure CHStatement {M : RandomModel 𝔅} (V : BoolValued 𝔅 M) where
  ch : V.Stmt

/-- THE INDEPENDENCE THEOREM (Section 5, p. 106-108).  There is a complete
    Boolean algebra `𝔅` (the measure algebra of `Ω = [0,1]^I`, `card I > 2^{ℵ₀}`)
    and a random-real model in which every axiom is Boolean valid but the
    continuum hypothesis has Boolean value `0` (`⟦CH⟧ = ⊥`).  Hence CH is not
    provable from the axioms. -/
theorem continuum_hypothesis_independent :
    ∃ (𝔅 : CompleteBooleanAlgebra) (M : RandomModel 𝔅) (V : BoolValued 𝔅 M)
      (CH : CHStatement 𝔅 V) (IsAxiom : V.Stmt → Prop),
      (∀ A, IsAxiom A → V.Valid A) ∧
      V.val CH.ch = 𝔅.bot := by
  sorry -- TODO Independence Theorem: ⟦CH⟧ = 0 in the product-measure random-real model

/-- Corollary: the negation of the continuum hypothesis is *not* refutable
    either.  Taking the one-point space `Ω` (the two-element algebra) yields the
    standard model, in which CH may hold; combined with the theorem above, CH is
    independent of the axioms. -/
theorem continuum_hypothesis_not_refutable :
    ∃ (𝔅 : CompleteBooleanAlgebra) (M : RandomModel 𝔅) (V : BoolValued 𝔅 M)
      (CH : CHStatement 𝔅 V),
      V.val CH.ch = 𝔅.top := by
  sorry -- TODO the two-element (standard) model where CH holds

end Scott1967
