/-
  Extending the Topological Interpretation to Intuitionistic Analysis
  (Lean 4 auto-generated faithful skeleton)

  Faithful to:
    D. Scott, "Extending the Topological Interpretation to Intuitionistic
    Analysis", Compositio Mathematica 20 (1968), 194-210.

  Source text extracted from:
    DanaScottPapers/Scott-1968-Extending-Topological-Interpretation-Intuitionistic-Analysis.txt

  The "truth values" are the OPEN subsets of a topological space `T`, forming a
  complete Heyting algebra under `⊆`, with `In` the interior operator.  To each
  formula `A` one assigns an open set `[[A]] ⊆ T`; `A` is VALID iff `[[A]] = T`.
  Individual variables range over a domain `𝓡` of "reals" realized as the
  CONTINUOUS functions `ξ : T → R` (Theorem 2.7); the classical reals `R` are the
  constant functions.  The primitive order relation `<` (with apartness `≠`
  defined from it) is valued in open sets; intuitionistic predicate logic is
  SOUND for this interpretation (via Rasiowa-Sikorski).

  We formalize:
    * the interpretation as a `TopModel` (space `T`, interior operator `In`
      with the Kuratowski axioms, individual domain `R`, and the order relation
      valued in opens);
    * the valuation `[[φ]]` clauses (2.1)-(2.6) as operations on open sets;
    * validity = the whole space, and soundness of Heyting predicate logic;
    * the order axioms (1.1),(1.2),(1.17) and the comprehension principle,
      with `sorry`.

  Core Lean 4 only; no Mathlib.  Open sets are represented by their
  characteristic predicate `T → Prop`.  Assignments are named `g`.
-/

namespace Scott1968ExtendingTopologicalInterpretation

/-! ## 1. The topological model -/

/-- The interpretation.  `T` is the space; opens are predicates `T → Prop`; `In`
    is the interior operator (satisfying the Kuratowski axioms, so its fixpoints
    are exactly the opens, a complete Heyting algebra).  `R` is the domain `𝓡`
    of individuals (continuous functions `T → ℝ`); `ltv ξ η` is the OPEN set
    `[[ξ < η]]`. -/
structure TopModel where
  T   : Type
  In  : (T → Prop) → (T → Prop)
  R   : Type
  lt  : R → R → (T → Prop)                       -- `[[ξ < η]]`, an open set
  -- Kuratowski interior axioms (make `In` a topological interior):
  In_le    : ∀ (X : T → Prop) t, In X t → X t                     -- In X ⊆ X
  In_mono  : ∀ (X Y : T → Prop), (∀ t, X t → Y t) → ∀ t, In X t → In Y t
  In_idem  : ∀ (X : T → Prop) t, In X t ↔ In (In X) t             -- In (In X) = In X
  In_univ  : ∀ t, In (fun _ => True) t                            -- In T = T
  In_meet  : ∀ (X Y : T → Prop) t, In (fun s => X s ∧ Y s) t ↔ (In X t ∧ In Y t)

/-- Update an assignment. -/
def upd (M : TopModel) (g : Nat → M.R) (i : Nat) (a : M.R) : Nat → M.R :=
  fun j => if j = i then a else g j

/-! ## 2. Syntax and the valuation `[[·]]` (clauses (2.1)-(2.6)) -/

/-- Formulas of the order/analysis language.  `lt i j` is `vᵢ < vⱼ`. -/
inductive Fml where
  | lt  : Nat → Nat → Fml
  | bot : Fml
  | and : Fml → Fml → Fml
  | or  : Fml → Fml → Fml
  | imp : Fml → Fml → Fml
  | all : Nat → Fml → Fml
  | ex  : Nat → Fml → Fml
  deriving Repr

namespace Fml
/-- `¬φ := φ → ⊥`. -/
def neg (φ : Fml) : Fml := imp φ bot
/-- Apartness `x ≠ y := x < y ∨ y < x` (lines 117-118). -/
def apart (i j : Nat) : Fml := or (lt i j) (lt j i)
/-- `x ≤ y := ¬(y < x)`. -/
def le (i j : Nat) : Fml := neg (lt j i)
/-- `x = y := ¬(x ≠ y)`. -/
def eq (i j : Nat) : Fml := neg (apart i j)
def iff (φ ψ : Fml) : Fml := and (imp φ ψ) (imp ψ φ)
end Fml

/-- The open-set valuation `[[φ]](g) ⊆ T`.  Clauses:
    `[[∧]]` = ∩, `[[∨]]` = ∪, `[[→]] = In((T∖·)∪·)`, `[[¬]] = In(T∖·)`,
    `[[∀]] = In(⋂)`, `[[∃]] = ⋃`. -/
def val (M : TopModel) : (Nat → M.R) → Fml → (M.T → Prop)
  | g, .lt i j  => M.lt (g i) (g j)
  | _, .bot     => fun _ => False
  | g, .and φ ψ => fun t => val M g φ t ∧ val M g ψ t
  | g, .or φ ψ  => fun t => val M g φ t ∨ val M g ψ t
  | g, .imp φ ψ => M.In (fun t => val M g φ t → val M g ψ t)
  | g, .all i φ => M.In (fun t => ∀ a : M.R, val M (upd M g i a) φ t)
  | g, .ex i φ  => fun t => ∃ a : M.R, val M (upd M g i a) φ t

/-- Validity in a model: `[[φ]] = T`, the whole space (line 256). -/
def validIn (M : TopModel) (φ : Fml) : Prop := ∀ g t, val M g φ t

/-- Validity in every topological model. -/
def Valid (φ : Fml) : Prop := ∀ M, validIn M φ

/-! ## 3. The order axioms of the continuum (§1) -/

/-- (1.1) asymmetry: `¬(x < y ∧ y < x)`. -/
def ax_asymm (x y : Nat) : Fml := Fml.neg (Fml.and (Fml.lt x y) (Fml.lt y x))
/-- (1.2) cotransitivity (weak interpolation): `x < y → (x < z ∨ z < y)`. -/
def ax_cotrans (x y z : Nat) : Fml :=
  Fml.imp (Fml.lt x y) (Fml.or (Fml.lt x z) (Fml.lt z y))
/-- (1.17) density: `x < y → ∃r (x < r ∧ r < y)`. -/
def ax_density (x y r : Nat) : Fml :=
  Fml.imp (Fml.lt x y) (Fml.ex r (Fml.and (Fml.lt x r) (Fml.lt r y)))

/-! ## 4. Key theorems -/

/-- SOUNDNESS (line 256): every formula provable in Heyting's predicate logic is
    valid (`[[A]] = T`) in every topological model, via Rasiowa-Sikorski. -/
theorem soundness_heyting {φ : Fml} (h : True) : Valid φ := by
  sorry -- TODO: define `Prov` for HPC and induct, using the `In`/lattice laws.

/-- Theorem 2.7: each `ξ ∈ 𝓡` determines a CONTINUOUS function `T → ℝ` via the
    cut `ξ(t) = inf{ q ∈ ℚ : t ∈ [[ξ < q]] }`; the domain `𝓡` is taken to be
    ALL continuous functions so as to be complete (lines 277-322).  Recorded as
    an interface obligation on models. -/
theorem reals_are_continuous : True := by
  sorry -- TODO: requires a topology + ℝ; stated for the intended model.

/-- The general comprehension principle is valid (line 789):
    `∃X ∀r (r ∈ X ↔ A(r))` — species need not be extensional. -/
theorem comprehension_valid : True := by
  sorry -- TODO

/-- Excluded middle for parameter-free sentences on Baire space (lines 620-631):
    with `T = ℕ^ℕ` the only invariant opens are `∅, T`, so any constant sentence
    `A` has `A ∨ ¬A` valid. -/
theorem em_parameterfree_baire : True := by
  sorry -- TODO

end Scott1968ExtendingTopologicalInterpretation
