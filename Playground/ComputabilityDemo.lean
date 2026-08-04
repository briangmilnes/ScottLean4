import Mathlib.Data.Real.Basic

/-!
# ℚ computes, ℝ does not — a live demonstration

Standalone scratch (NOT imported into the Playground library, since it contains
intentional errors). Run with:
    lake env lean ComputabilityDemo.lean
The ℚ `#eval`s print values; the ℝ lines are *expected* to error.
-/

/-! ## ℚ is computable: exact arithmetic + decidable equality -/

#eval (2/3 + 5/6 : ℚ)              -- 3/2
#eval (5/6 - 2/3 : ℚ)              -- 1/6
#eval decide ((1/3 : ℚ) = 2/6)     -- true
#eval decide ((1/3 : ℚ) = 1/2)     -- false

/-! ## ℝ is noncomputable -/

-- OK: with the keyword the definition is accepted (but still not runnable).
noncomputable def r : ℝ := 2/3 + 5/6
#check r

-- REJECTED (intentional): without `noncomputable`, ℝ division won't compile.
def rBad : ℝ := 2/3 + 5/6

-- REJECTED (intentional): ℝ has no runnable evaluation.
#eval (2/3 + 5/6 : ℝ)

-- REJECTED (intentional): ℝ equality is undecidable (no Decidable instance).
#eval decide ((1/3 : ℝ) = 2/6)
