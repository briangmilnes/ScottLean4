import ScottDomains.Domain

/-!
# Theorem 1: the Fixed-Point Theorem for a cpo

Gunter & Scott, *Semantic Domains*, §2.1:

> **Theorem 1** … given a cpo `D`, the function `fix_D : (D → D) → D` given by
> `fix_D(f) = ⨆ₙ fⁿ(⊥)` … `f` continuous ⟹ least fixed point `⨆ₙ fⁿ(⊥)`.

## Why this is not reuse from Mathlib

`docs/PaperInventory.md` marked Theorem 1 `✓ OrderHom.lfp`. That is the wrong
theorem. `OrderHom.lfp` (`Mathlib/Order/FixedPoints.lean:49`) is Knaster–Tarski:
it needs a **complete lattice** and only monotonicity, and it produces the least
pre-fixed point as an infimum of pre-fixed points. Theorem 1 is Kleene's: it
needs only a **cpo** with `⊥` and a **continuous** `f`, and it produces the fixed
point as the supremum of the ascending chain of iterates. Neither implies the
other — a cpo need not be a lattice, and Knaster–Tarski does not exhibit the
fixed point as a limit of approximations, which is the whole point in a semantics
of recursion.

Mathlib's nearest cpo-side result, `OmegaCompletePartialOrder.ωSup_iterate_mem_fixedPoint`,
is stated for ω-cpos and ω-continuity. The paper is directed throughout, and the
rest of this development is stated over `CompletePartialOrder` and
`ScottContinuous`, so Theorem 1 is proved here in that setting.

## The construction

`kleeneChain f = {fⁿ(⊥) | n : ℕ}` is nonempty and directed because it is an
ascending chain, and `kleeneFix f` is its supremum. Continuity gives
`f (⨆ chain) = ⨆ (f '' chain)`, and the image has the same supremum as the chain
itself: it is the chain minus its first element, and that element is `⊥`.
-/

namespace ScottDomains

variable {α : Type*} [CompletePartialOrder α] {f : α → α}

/-- The ascending chain `⊥ ⊑ f(⊥) ⊑ f²(⊥) ⊑ …` of finite approximations. -/
def kleeneChain (f : α → α) : Set α := Set.range fun n : ℕ => f^[n] ⊥

theorem mem_kleeneChain (n : ℕ) : f^[n] ⊥ ∈ kleeneChain f := ⟨n, rfl⟩

theorem kleeneChain_nonempty : (kleeneChain f).Nonempty := ⟨⊥, mem_kleeneChain 0⟩

/-- The iterates ascend: `⊥ ⊑ f ⊥` starts it, and monotonicity propagates it. -/
theorem monotone_iterate_bot (hf : Monotone f) : Monotone fun n : ℕ => f^[n] ⊥ := by
  refine monotone_nat_of_le_succ fun n => ?_
  induction n with
  | zero => exact bot_le
  | succ k ih =>
    have hk : f^[k + 1] ⊥ = f (f^[k] ⊥) := Function.iterate_succ_apply' f k ⊥
    have hk1 : f^[k + 2] ⊥ = f (f^[k + 1] ⊥) := Function.iterate_succ_apply' f (k + 1) ⊥
    rw [hk1, hk]
    exact hf (hk ▸ ih)

/-- A chain is directed. -/
theorem directedOn_kleeneChain (hf : Monotone f) : DirectedOn (· ≤ ·) (kleeneChain f) := by
  rintro _ ⟨m, rfl⟩ _ ⟨n, rfl⟩
  exact ⟨f^[max m n] ⊥, mem_kleeneChain _, monotone_iterate_bot hf (le_max_left m n),
    monotone_iterate_bot hf (le_max_right m n)⟩

/-- `fix(f) = ⨆ₙ fⁿ(⊥)`. -/
noncomputable def kleeneFix (f : α → α) : α := sSup (kleeneChain f)

theorem le_kleeneFix (hf : Monotone f) (n : ℕ) : f^[n] ⊥ ≤ kleeneFix f :=
  (directedOn_kleeneChain hf).le_sSup (mem_kleeneChain n)

/-- `fix(f)` is a fixed point. Continuity moves `f` through the supremum, and the
image chain has the same supremum as the chain — it is the chain without its
first element, which is `⊥`. -/
theorem map_kleeneFix (hf : ScottContinuous f) : f (kleeneFix f) = kleeneFix f := by
  have hmono := hf.monotone
  have hdir := directedOn_kleeneChain hmono
  have hcont := hf kleeneChain_nonempty hdir hdir.isLUB_sSup
  refine hcont.unique ?_
  constructor
  · rintro _ ⟨_, ⟨n, rfl⟩, rfl⟩
    rw [← Function.iterate_succ_apply' f n]
    exact le_kleeneFix hmono (n + 1)
  · intro u hu
    refine hdir.sSup_le ?_
    rintro _ ⟨n, rfl⟩
    cases n with
    | zero => exact bot_le
    | succ k =>
      exact le_of_eq_of_le (Function.iterate_succ_apply' f k ⊥)
        (hu ⟨f^[k] ⊥, mem_kleeneChain k, rfl⟩)

/-- Every iterate is below every pre-fixed point, by induction. -/
theorem iterate_bot_le (hf : Monotone f) {b : α} (hb : f b ≤ b) : ∀ n, f^[n] ⊥ ≤ b := by
  intro n
  induction n with
  | zero => exact bot_le
  | succ k ih =>
    rw [Function.iterate_succ_apply' f k]
    exact (hf ih).trans hb

/-- `fix(f)` is below every pre-fixed point. -/
theorem kleeneFix_le (hf : Monotone f) {b : α} (hb : f b ≤ b) : kleeneFix f ≤ b := by
  refine (directedOn_kleeneChain hf).sSup_le ?_
  rintro _ ⟨n, rfl⟩
  exact iterate_bot_le hf hb n

/-- **Theorem 1 (Fixed-Point Theorem).** For a continuous `f` on a cpo,
`⨆ₙ fⁿ(⊥)` is the least fixed point of `f`. -/
theorem theorem_1 (hf : ScottContinuous f) : IsLeast {a | f a = a} (kleeneFix f) :=
  ⟨map_kleeneFix hf, fun _ hb => kleeneFix_le hf.monotone (le_of_eq hb)⟩

alias theorem1 := theorem_1

/-- The same statement for pre-fixed points, which is what recursion arguments
usually need. -/
theorem isLeast_kleeneFix_le (hf : ScottContinuous f) :
    IsLeast {a | f a ≤ a} (kleeneFix f) :=
  ⟨le_of_eq (map_kleeneFix hf), fun _ hb => kleeneFix_le hf.monotone hb⟩

end ScottDomains
