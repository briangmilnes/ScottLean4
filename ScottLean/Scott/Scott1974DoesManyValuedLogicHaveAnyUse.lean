/-
  Does Many-Valued Logic Have Any Use?  (Lean 4 auto-generated faithful skeleton)

  Faithful to:
    D. Scott, "Does Many-Valued Logic Have Any Use?", in S. Körner (ed.),
    Philosophy of Logic, Blackwell, Oxford, 1976, pp. 64-74 (1974 lecture).

  Source text extracted from:
    DanaScottPapers/Scott-1974-Does-Many-Valued-Logic-Have-Any-Use.txt

  HONEST SCOPE NOTE.  This paper is a short, deliberately provocative and largely
  PHILOSOPHICAL essay; roughly 80-85% is prose.  Scott is openly skeptical of
  taking intermediate fractional "truth values" at face value and argues instead
  for reading many-valued logic through an ORDERED / METRIC algebra of "degrees
  of error" (0 = truth), reducing it to something two-valued at the meta-level.
  He explicitly rejects the probabilistic reading of implication.

  Moreover, in the source scan every printed TRUTH TABLE is destroyed by OCR, so
  we deliberately do NOT transcribe fabricated tables.  What we CAN faithfully
  encode is the one clean, load-bearing formal kernel that survives in running
  text: Łukasiewicz implication as TRUNCATED SUBTRACTION on the error scale
  (lines 216-224:  #(A→B) = #B − #A if #B ≥ #A, else 0), the designated value 0,
  and the two entailment characterizations (the degree-based one, line 195, and
  Giles's real-valued summed-inequality one, lines 229-239).

  Everything below is honest: it is the algebra Scott describes, not an invented
  formalism, and the one genuine theorem is actually PROVED (no `sorry`).

  Core Lean 4 only; no Mathlib.
-/

namespace Scott1974DoesManyValuedLogicHaveAnyUse

/-! ## 1. The algebra of "degrees of error"

    Truth values are DEGREES OF ERROR, here the natural numbers, with `0`
    the minimal error = truth (the sole DESIGNATED value).  The natural ordering
    `i ≤ j` reads "i is less in error than j". -/

/-- The designated value: `0` = truth (minimal error). -/
def designated (a : Nat) : Prop := a = 0

/-- Łukasiewicz implication as TRUNCATED SUBTRACTION (lines 216-224):
    `#(A→B) = #B − #A` when `#B ≥ #A`, else `0`.  On `Nat`, ordinary truncated
    subtraction `b - a` already computes `max 0 (b − a)`. -/
def luk (a b : Nat) : Nat := b - a

/-- Bounded negation on a scale with top `N`:  `#(¬A) = N − #A` (Łukasiewicz
    negation, reoriented so that `¬` of truth `0` is the maximal error `N`). -/
def lnot (N a : Nat) : Nat := N - a

/-- Łukasiewicz conjunction / disjunction on the error scale read off the order:
    the value of `A ∧ B` is the WORSE (larger) error, of `A ∨ B` the better. -/
def land (a b : Nat) : Nat := max a b
def lor  (a b : Nat) : Nat := min a b

/-! ## 2. The one genuine theorem (PROVED)

    The metalinguistic implication "A ⊃ B" (line 120: "whenever i ≥ A then
    i ≥ B") holds exactly when the object connective `A → B` is designated
    (line 133: `A→B` is true iff `0 ≥ (A→B)`), and this happens exactly when
    `#A ≥ #B` ("A is at least as much in error as B"). -/

/-- `A → B` is designated (true) iff `A` is at least as much in error as `B`. -/
theorem luk_designated (a b : Nat) : designated (luk a b) ↔ b ≤ a := by
  unfold designated luk
  exact Nat.sub_eq_zero_iff_le

/-- Truth (`0`) implies everything to the value of that thing:
    `#(⊤ → B) = #B`. -/
theorem luk_top (b : Nat) : luk 0 b = b := by
  unfold luk; simp

/-- Modus-ponens soundness on the scale:  if `A` and `A → B` are both designated
    then so is `B`. -/
theorem luk_mp {a b : Nat} (hA : designated a) (hAB : designated (luk a b)) :
    designated b := by
  unfold designated at *
  have : b ≤ a := (luk_designated a b).1 hAB
  subst hA; exact Nat.le_zero.1 this

/-! ## 3. Entailment characterizations -/

/-- The DEGREE-BASED multiple-conclusion entailment (line 195):
    `A₀,…,A_{n-1} ⊢ B₀,…,B_{m-1}` holds iff for every degree `i`, if `i` bounds
    every premise (`Aₜ ≤ i`) then it bounds some conclusion (`Bᵤ ≤ i`). -/
def entails (prem concl : List Nat) : Prop :=
  ∀ i : Nat, (∀ a ∈ prem, a ≤ i) → (∃ b ∈ concl, b ≤ i)

/-- GILES's "logic of risk" characterization (lines 229-239): the sequent is
    safe iff, for every evaluation `#`, the summed premise error is at least the
    summed conclusion error.  Here (with fixed values) that is the numeric
    inequality `Σ prem ≥ Σ concl`. -/
def gilesSafe (prem concl : List Nat) : Prop := concl.sum ≤ prem.sum

/-- A sanity theorem: the empty sequent `⊢ B` (no premises) is degree-valid iff
    some conclusion is truth (`0`), matching "there is nothing to discharge". -/
theorem entails_nil (concl : List Nat) :
    entails [] concl ↔ (∃ b ∈ concl, b = 0) := by
  constructor
  · intro h
    obtain ⟨b, hb, hle⟩ := h 0 (by intro a ha; cases ha)
    exact ⟨b, hb, Nat.le_zero.1 hle⟩
  · intro ⟨b, hb, h0⟩ i _
    exact ⟨b, hb, by subst h0; exact Nat.zero_le i⟩

/-! ## 4. A reconstructed three-valued fragment (clearly labeled)

    The paper's printed 3-valued table {1, ½, 0} is OCR-destroyed and NOT
    transcribed here.  For illustration ONLY, we RECONSTRUCT it from the
    truncated-subtraction formula on the reoriented error scale `{0, 1, 2}`
    (0 = truth, 1 = ½, 2 = false).  This is a derivation from Scott's algebra,
    not a verbatim artifact of the source. -/
def three : List Nat := [0, 1, 2]

/-- The reconstructed 3-valued implication table as a function on `{0,1,2}`. -/
def luk3 (a b : Nat) : Nat := luk a b

end Scott1974DoesManyValuedLogicHaveAnyUse
