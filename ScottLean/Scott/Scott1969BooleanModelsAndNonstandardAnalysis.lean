/-
  Boolean Models and Nonstandard Analysis — Boolean-valued semantics
  for analysis

  Faithful to:
    D. Scott, "Boolean Models and Nonstandard Analysis",
    in Applications of Model Theory to Algebra, Analysis, and Probability
    (W. A. J. Luxemburg, ed.), Holt, Rinehart & Winston, 1969, pp. 87-92.

  Source text extracted from:
    DanaScottPapers/Scott-1969-Boolean-Models-and-Nonstandard-Analysis.txt

  Auto-generated faithful skeleton (core Lean 4 only; no Mathlib).

  Scott builds models of analysis by assigning to every formula a value in a
  complete Boolean algebra ℬ.  Starting from Boolean values on atomic formulas,
  the value extends to all formulas by the rules (p. 88):

        ⟦¬φ⟧      = −⟦φ⟧                      (Boolean complement)
        ⟦φ ∨ ψ⟧   = ⟦φ⟧ ⊔ ⟦ψ⟧                 (join)
        ⟦∃x φ(x)⟧ = ⨆ₐ ⟦φ(a)⟧                 (supremum)

  A formula is *(Boolean) valid* iff its value is ⊤ = 1.  With ℬ a *nonstandard*
  complete algebra (e.g. the Lebesgue measure algebra, so that ℬ becomes the
  space of random variables) the model satisfies all the higher-order axioms of
  real analysis, yet the continuum hypothesis can fail to be valid — this is the
  Boolean-valued independence method.

  We formalize: a complete Boolean algebra, a HOAS deep embedding of first-order
  formulas over a domain `D` with ℬ-valued atoms, the value map `bval`, the
  notion of validity, and the shape of the CH sentence.  We prove that the law
  of excluded middle is valid — a consequence of the Boolean axiom `a ⊔ aᶜ = ⊤`.
-/

namespace BooleanModels

/-! ## Complete Boolean algebras

    Meet `⊓`, join `⊔`, complement `ᶜ`, bounds `⊥, ⊤`, and arbitrary suprema
    `sSup` (completeness).  The induced order is `a ≤ b := a ⊓ b = a`. -/
class CompleteBooleanAlgebra (B : Type) where
  meet : B → B → B
  join : B → B → B
  compl : B → B
  bot : B
  top : B
  join_comm : ∀ a b, join a b = join b a
  meet_comm : ∀ a b, meet a b = meet b a
  join_assoc : ∀ a b c, join (join a b) c = join a (join b c)
  meet_assoc : ∀ a b c, meet (meet a b) c = meet a (meet b c)
  join_absorb : ∀ a b, join a (meet a b) = a
  meet_absorb : ∀ a b, meet a (join a b) = a
  join_bot : ∀ a, join a bot = a
  meet_top : ∀ a, meet a top = a
  meet_distrib : ∀ a b c, meet a (join b c) = join (meet a b) (meet a c)
  /-- `a ⊔ aᶜ = ⊤` — the law grounding excluded middle. -/
  join_compl : ∀ a, join a (compl a) = top
  /-- `a ⊓ aᶜ = ⊥`. -/
  meet_compl : ∀ a, meet a (compl a) = bot
  /-- Supremum of a set of Boolean values (completeness). -/
  sSup : (B → Prop) → B
  /-- Each member is below the supremum (`≤` unfolded as `b ⊓ sSup S = b`). -/
  le_sSup : ∀ (S : B → Prop) b, S b → meet b (sSup S) = b
  /-- The supremum is least among upper bounds. -/
  sSup_le : ∀ (S : B → Prop) c, (∀ b, S b → meet b c = b) → meet (sSup S) c = sSup S

namespace CompleteBooleanAlgebra
variable {B : Type} [CompleteBooleanAlgebra B]

/-- The induced Boolean order `a ≤ b`. -/
def le (a b : B) : Prop := meet a b = a

end CompleteBooleanAlgebra

/-! ## First-order formulas with ℬ-valued atoms

    A HOAS deep embedding over a domain `D`: quantifiers bind by meta-level
    functions `D → Formula`.  Atomic formulas already carry a ℬ-value (this is
    how Scott's Borel relations enter, as ℬ-valued relations on the model). -/
inductive Formula (D B : Type) where
  | atom : B → Formula D B
  | fls  : Formula D B
  | neg  : Formula D B → Formula D B
  | or   : Formula D B → Formula D B → Formula D B
  | and  : Formula D B → Formula D B → Formula D B
  | ex   : (D → Formula D B) → Formula D B
  | all  : (D → Formula D B) → Formula D B

/-- The Boolean value `⟦φ⟧ ∈ ℬ` of a formula (Scott's extension rules).
    `⟦∀x φ⟧` is the De Morgan dual of `⟦∃x ¬φ⟧`, so only `sSup` is needed. -/
def bval {D B : Type} [C : CompleteBooleanAlgebra B] : Formula D B → B
  | .atom b   => b
  | .fls      => C.bot
  | .neg φ    => C.compl (bval φ)
  | .or φ ψ   => C.join (bval φ) (bval ψ)
  | .and φ ψ  => C.meet (bval φ) (bval ψ)
  | .ex f     => C.sSup (fun b => ∃ d, bval (f d) = b)
  | .all f    => C.compl (C.sSup (fun b => ∃ d, C.compl (bval (f d)) = b))

/-- A formula is *(Boolean) valid* iff its value is the top element ⊤. -/
def Valid {D B : Type} [CompleteBooleanAlgebra B] (φ : Formula D B) : Prop :=
  bval φ = CompleteBooleanAlgebra.top

/-! ## Excluded middle is valid

    `⟦φ ∨ ¬φ⟧ = ⟦φ⟧ ⊔ (⟦φ⟧)ᶜ = ⊤`, directly from the Boolean axiom. -/
theorem valid_em {D B : Type} [C : CompleteBooleanAlgebra B] (φ : Formula D B) :
    Valid (Formula.or φ (Formula.neg φ)) := by
  show C.join (bval φ) (C.compl (bval φ)) = C.top
  exact C.join_compl (bval φ)

/-! ## The continuum hypothesis as a formula shape

    Scott gives CH in the very simple higher-order form (p. 91):

      ∀h[ ∃f ∀y[ h(y)=0 → ∃x(N(x) ∧ y=f(x)) ]
          ∨ ∃g ∀y ∃x( h(x)=0 ∧ y=g(x) ) ]

    which, for a suitable nonstandard ℬ, is *not* valid — even though the
    axiom of choice holds.  A faithful transcription needs the ℬ-valued
    higher-order structure of the model (functions f : ℝ → ℝ with
    `⟦a=b⟧ ≤ ⟦f(a)=f(b)⟧`), which is beyond this first-order skeleton. -/

/-- The ℬ-valued real structure of the model (`⟦=⟧`, `⟦<⟧`, `⟦+⟧`, …) makes ℬ a
    ℬ-valued real-closed field: e.g. trichotomy `a<b ∨ a=b ∨ a>b` is valid.
    Kept as a target; see the paper's "ℛ is a (ℬ-valued) real-closed field". -/
def realClosedField_valid : Prop := True  -- placeholder for the model's axioms
-- TODO: build the ℬ-valued structure ℛ of measurable functions and show every
-- ordered-field / real-closure axiom is valid, then exhibit ℬ with CH invalid.

/-- The *maximum principle* Scott notes for the model: an existential value is
    actually attained, `⟦∃x φ(x)⟧ = ⟦φ(a)⟧` for some `a`.  (True for
    ultraproducts and the measure-algebra model; false for general ℬ.) -/
def maximum_principle {D B : Type} [CompleteBooleanAlgebra B]
    (f : D → Formula D B) : Prop :=
  ∃ a : D, bval (Formula.ex f) = bval (f a)
-- TODO: holds for the specific random-variable model, not for arbitrary ℬ.

end BooleanModels
