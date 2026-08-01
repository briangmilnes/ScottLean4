import Mathlib.Tactic

-- Smoke test: confirms the Mathlib dependency resolves and its tactics load.
example : 1 + 1 = 2 := by norm_num

example (p q : Prop) (h : p ∧ q) : q ∧ p := by tauto
