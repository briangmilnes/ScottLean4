import Playground.LambdaSmallStep

/-!
# Metatheory of full-β reduction

The standard "common theorems" for a full-β (βη) untyped λ-calculus, and where each
stands here. `↝` and `↝*` are from `Playground.LambdaSmallStep`.

| Theorem | Status |
|---------|--------|
| `↝*` reflexive and transitive | by construction (`Relation.ReflTransGen`) |
| **Compatibility / congruence** of `↝*` (under `app`-left, `app`-right, `lam`) | proved: `MultiStep.appL/appR/app/lam` |
| A normal term reduces only to itself | proved: `Normal.eq_of_multistep` |
| Variables are normal | proved: `normal_var` |
| **Not strongly normalizing** (`Ω` loops) | proved: `Ω_step`, `not_normal_Ω` |
| **Church–Rosser / confluence** | `confluent` — the one proof hole (see note) |
| **Uniqueness of normal forms** | proved *given* `confluent`: `normal_unique` |

There is deliberately **no determinism theorem**: full β is non-deterministic (a term
may have several redexes). Determinism is a property of call-by-value / call-by-name.

### Note on `confluent`

Church–Rosser is the deep theorem. Single-step β does **not** satisfy the diamond
property, so `Relation.church_rosser` (which reduces confluence to a one-step diamond)
cannot be applied to `↝` directly. The standard proof (Tait–Martin-Löf, sharpened by
Takahashi) introduces **parallel reduction** `⇉`, proves *it* has the diamond property
via the maximal-parallel-reduct `t*`, and uses `↝ ⊆ ⇉ ⊆ ↝*` to transfer confluence
back to `↝*`. That development (with its de Bruijn substitution lemmas) is left as the
single `sorry` here — a self-contained next step.
-/

namespace Playground.Lambda
open Term

/-! ## Reflexivity and transitivity (by construction) -/

-- `MultiStep = Relation.ReflTransGen Step`, so reflexivity is `Relation.ReflTransGen.refl`
-- and transitivity is `Relation.ReflTransGen.trans`.
example (t : Term) : t ↝* t := Relation.ReflTransGen.refl
example {t u v : Term} (h₁ : t ↝* u) (h₂ : u ↝* v) : t ↝* v := h₁.trans h₂

/-! ## Compatibility (congruence): `↝*` reduces in every position -/

/-- Reduce under a `lam`. -/
theorem MultiStep.lam {b b' : Term} (h : b ↝* b') : lam b ↝* lam b' := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact ih.tail (Step.lam hstep)

/-- Reduce the function part of an application. -/
theorem MultiStep.appL {f f' : Term} (a : Term) (h : f ↝* f') :
    app f a ↝* app f' a := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact ih.tail (Step.appL a hstep)

/-- Reduce the argument part of an application. -/
theorem MultiStep.appR (f : Term) {a a' : Term} (h : a ↝* a') :
    app f a ↝* app f a' := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact ih.tail (Step.appR f hstep)

/-- Reduce both parts of an application. -/
theorem MultiStep.app {f f' a a' : Term} (hf : f ↝* f') (ha : a ↝* a') :
    app f a ↝* app f' a' :=
  (MultiStep.appL a hf).trans (MultiStep.appR f' ha)

/-! ## Normal forms -/

/-- `t` is a **normal form** if no β/η step applies to it. -/
def Normal (t : Term) : Prop := ¬ ∃ t', t ↝ t'

/-- Variables are normal (no rule fires on a bare `var`). -/
theorem normal_var (n : Nat) : Normal (var n) := by
  rintro ⟨t', h⟩
  cases h

/-- A normal term reduces only to itself: if `t` is normal and `t ↝* u` then `u = t`. -/
theorem Normal.eq_of_multistep {t u : Term} (hn : Normal t) (h : t ↝* u) : t = u := by
  rcases h.cases_head with rfl | ⟨c, hc, _⟩
  · rfl
  · exact absurd ⟨c, hc⟩ hn

/-! ## Non-termination: the untyped λ-calculus is not strongly normalizing -/

/-- `Ω = Δ Δ` β-reduces to itself. -/
theorem Ω_step : Ω ↝ Ω := by
  simpa [Ω, Δ, subst] using Step.beta (app (var 0) (var 0)) Δ

/-- Consequently `Ω` is not a normal form — it has an infinite reduction sequence. -/
theorem not_normal_Ω : ¬ Normal Ω := fun h => h ⟨Ω, Ω_step⟩

/-! ## Church–Rosser and uniqueness of normal forms -/

/-- **Church–Rosser / confluence.** Any two reducts of a term have a common reduct.
The single proof hole in this file — see the module note for the parallel-reduction
method that discharges it. -/
theorem confluent {t t₁ t₂ : Term} (h₁ : t ↝* t₁) (h₂ : t ↝* t₂) :
    ∃ u, t₁ ↝* u ∧ t₂ ↝* u := by
  sorry

/-- **Uniqueness of normal forms.** A term has at most one normal form. This is a
corollary of confluence: it is proved *given* `confluent`. -/
theorem normal_unique {t u₁ u₂ : Term}
    (h₁ : t ↝* u₁) (h₂ : t ↝* u₂) (n₁ : Normal u₁) (n₂ : Normal u₂) : u₁ = u₂ := by
  obtain ⟨u, hu₁, hu₂⟩ := confluent h₁ h₂
  rw [n₁.eq_of_multistep hu₁, n₂.eq_of_multistep hu₂]

end Playground.Lambda
