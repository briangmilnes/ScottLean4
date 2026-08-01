/-
ScottLean.Basic — a first module.

Every declaration below is checked by the Lean kernel. Open this file in VS Code,
place the cursor inside a proof, and read the goal state in the Lean Infoview
(the panel on the right). Move the cursor line by line to watch each tactic
transform the goal until it reads "No goals".

These proofs use only Lean's core library — no Mathlib — so the first build only
needs the Lean toolchain.
-/

namespace ScottLean

/-- Conjunction commutes: from a proof of `p ∧ q`, construct a proof of `q ∧ p`.
    `obtain` splits the hypothesis `h` into its two components; the anonymous
    constructor `⟨_, _⟩` builds the swapped pair. -/
theorem and_comm_example (p q : Prop) (h : p ∧ q) : q ∧ p := by
  obtain ⟨hp, hq⟩ := h
  exact ⟨hq, hp⟩

/-- `0 + n = n`, by induction on `n`. Nat addition recurses on its second
    argument, so `n + 0 = n` holds by `rfl` but `0 + n = n` needs induction.
    Put the cursor on each branch to see the base case and the step case. -/
theorem zero_add_eq (n : Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ k ih => rw [Nat.add_succ, ih]

/-- An existential statement: some natural number is greater than three. The
    witness is `4`; `decide` checks the decidable proposition `4 > 3`. -/
theorem exists_gt_three : ∃ n : Nat, n > 3 := by
  exact ⟨4, by decide⟩

end ScottLean
