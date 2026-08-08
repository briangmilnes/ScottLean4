import ScottDomains.FixedPoint
import ScottDomains.StrictHom

/-!
# §2.2's first application: the factorial function

Gunter & Scott, *Semantic Domains*, §2.2 (printed p. 5):

> **The factorial function.** As a first illustration of the use of the Fixed
> Point Theorem, let us consider how one might define the *factorial function*
> `fact : N⊥ → N⊥`. … But how do we know that there *is* a function `fact` which
> satisfies this equation? Define a function
> `F : (N⊥ ⊸ N⊥) → (N⊥ ⊸ N⊥)` by setting
> `F(f)(n) = 1` if `n = 0`, `n * f(n − 1)` if `n > 0`, `⊥` if `n = ⊥`.
> The definition of `F` is *not* recursive (`F` appears only on the left side of
> the equation) so `F` certainly exists. Moreover, it is easy to check that `F`
> is continuous (but not strict). Hence, by the Fixed Point Theorem, `F` has a
> least fixed point `fix(F)` and this solution will satisfy the equation for
> `fact`.

The r0040 audit recorded this as row 39 / N11: `factorial` and `recursive
equation` grep to 0 over the package, and the paper's running example `N⊥` is not
constructed anywhere. This file supplies both, and proves more than the paper
claims — not only that `fix(F)` satisfies the recursion, but that its value at
`n` *is* `n!`.

## `N⊥` is built here, minimally and on purpose

The flat cpo in general — `Flat X` for arbitrary `X`, with `T` and `ω⊤` beside it
— is a separate construction. What this file needs is one instance of it, so
`NatBot` is defined here as the two-constructor inductive type with the order
`x ⊑ y ↔ x = ⊥ ∨ x = y`, and nothing is claimed about flat cpos in general. When
the general construction lands, `NatBot` should be replaced by its instance at
`ℕ` and every proof below should go through unchanged: none of them touches the
representation except through `NatBot.le_iff` and the two constructors.

`NatBot.scottContinuous_of_monotone` is the one general fact the construction
buys, and it is §2.1's own remark: *any monotone function `f : N⊥ → E` is
continuous*. The reason is `NatBot.mem_of_isLUB` — in a flat cpo a **nonempty
directed set contains its own least upper bound**, so there is no limit for a
monotone map to fail to preserve.

## What "continuous but not strict" means here

`F` is continuous as a map on the cpo `N⊥ ⊸ N⊥`, and `factFun_ne_bot` is the
paper's parenthesis: `F(⊥) ≠ ⊥`, because `F(⊥)(0) = 1` however undefined the
argument function is. That is exactly why `fix(F)` is not `⊥`.
-/

namespace ScottDomains.Kleene

/-! ### `N⊥`, the flat naturals -/

/-- `N⊥`: the natural numbers with a bottom element adjoined, ordered flatly. -/
inductive NatBot where
  /-- The undefined value. -/
  | bot : NatBot
  /-- A defined natural number. -/
  | of (n : ℕ) : NatBot
  deriving DecidableEq

namespace NatBot

/-- The flat order: `x ⊑ y` iff `x` is undefined or `x` and `y` are the same. -/
protected def le (x y : NatBot) : Prop := x = NatBot.bot ∨ x = y

instance : PartialOrder NatBot where
  le := NatBot.le
  le_refl _ := Or.inr rfl
  le_trans _ _ _ hxy hyz := by
    rcases hxy with h | h
    · exact Or.inl h
    · subst h; exact hyz
  le_antisymm _ _ hxy hyx := by
    rcases hxy with h | h
    · rcases hyx with h' | h'
      · rw [h, h']
      · exact h'.symm
    · exact h

theorem le_iff {x y : NatBot} : x ≤ y ↔ x = NatBot.bot ∨ x = y := Iff.rfl

theorem bot_le' (x : NatBot) : NatBot.bot ≤ x := Or.inl rfl

/-- `s` contains a defined value. This is the condition `sSup` splits on. -/
def HasVal (s : Set NatBot) : Prop := ∃ n : ℕ, NatBot.of n ∈ s

open Classical in
/-- Suprema in `N⊥`: the unique defined value if there is one, `⊥` otherwise. On
a directed set the choice is forced, since two defined values in a directed set
are equal. -/
noncomputable instance : SupSet NatBot where
  sSup s := if h : HasVal s then NatBot.of h.choose else NatBot.bot

theorem sSup_of_hasVal {s : Set NatBot} (h : HasVal s) : sSup s = NatBot.of h.choose := by
  classical
  simp only [SupSet.sSup, dif_pos h]

theorem sSup_of_not_hasVal {s : Set NatBot} (h : ¬ HasVal s) : sSup s = NatBot.bot := by
  classical
  simp only [SupSet.sSup, dif_neg h]

/-- Every element of a directed set is below any defined element of it: a
directed set has at most one defined value. -/
theorem le_of_directed {s : Set NatBot} (hd : DirectedOn (· ≤ ·) s) {m : ℕ}
    (hm : NatBot.of m ∈ s) : ∀ x ∈ s, x ≤ NatBot.of m := by
  intro x hx
  obtain ⟨z, _, hxz, hmz⟩ := hd x hx _ hm
  rcases hmz with h | h
  · exact absurd h (by simp)
  · exact h ▸ hxz

/-- Elements of a set with no defined value are `⊥`. -/
theorem eq_bot_of_not_hasVal {s : Set NatBot} (h : ¬ HasVal s) {x : NatBot} (hx : x ∈ s) :
    x = NatBot.bot := by
  cases x with
  | bot => rfl
  | of n => exact absurd ⟨n, hx⟩ h

noncomputable instance : CompletePartialOrder NatBot :=
  { (inferInstance : PartialOrder NatBot), (inferInstance : SupSet NatBot) with
    bot := NatBot.bot
    bot_le := bot_le'
    lubOfDirected := fun s hs => by
      classical
      by_cases h : HasVal s
      · rw [sSup_of_hasVal h]
        exact ⟨fun x hx => le_of_directed hs h.choose_spec x hx, fun _ hu => hu h.choose_spec⟩
      · rw [sSup_of_not_hasVal h]
        exact ⟨fun x hx => le_of_eq (eq_bot_of_not_hasVal h hx), fun u _ => bot_le' u⟩ }

@[simp] theorem bot_eq : (⊥ : NatBot) = NatBot.bot := rfl

/-- **A nonempty directed set in a flat cpo contains its own least upper bound.**
This is the whole reason monotone maps out of `N⊥` are continuous. -/
theorem mem_of_isLUB {s : Set NatBot} (hne : s.Nonempty) (hd : DirectedOn (· ≤ ·) s)
    {a : NatBot} (ha : IsLUB s a) : a ∈ s := by
  classical
  by_cases h : HasVal s
  · obtain ⟨m, hm⟩ := h
    have h2 : a ≤ NatBot.of m := ha.2 fun x hx => le_of_directed hd hm x hx
    rw [le_antisymm h2 (ha.1 hm)]
    exact hm
  · obtain ⟨x, hx⟩ := hne
    have hb : NatBot.bot ∈ s := eq_bot_of_not_hasVal h hx ▸ hx
    have h2 : a ≤ NatBot.bot := ha.2 fun y hy => le_of_eq (eq_bot_of_not_hasVal h hy)
    rw [le_antisymm h2 (ha.1 hb)]
    exact hb

/-- **Any monotone function `f : N⊥ → E` is continuous** — §2.1's remark, and the
tool the rest of this file runs on. -/
theorem scottContinuous_of_monotone {β : Type*} [Preorder β] {g : NatBot → β}
    (hg : Monotone g) : ScottContinuous g := by
  intro s hne hd a ha
  refine ⟨?_, fun u hu => hu ⟨a, mem_of_isLUB hne hd ha, rfl⟩⟩
  rintro _ ⟨x, hx, rfl⟩
  exact hg (ha.1 hx)

/-- `n * ·` on `N⊥`, undefined on `⊥`. -/
def mulNat (n : ℕ) : NatBot → NatBot
  | NatBot.bot => NatBot.bot
  | NatBot.of m => NatBot.of (n * m)

theorem monotone_mulNat (n : ℕ) : Monotone (mulNat n) := by
  intro x y h
  rcases le_iff.mp h with h | h
  · subst h; exact bot_le' _
  · subst h; exact le_rfl

theorem scottContinuous_mulNat (n : ℕ) : ScottContinuous (mulNat n) :=
  scottContinuous_of_monotone (monotone_mulNat n)

end NatBot

/-! ### The functional `F` -/

open NatBot

/-- The paper's `F(f)`, as a function `N⊥ → N⊥`. -/
def factStep (f : NatBot → NatBot) : NatBot → NatBot
  | NatBot.bot => NatBot.bot
  | NatBot.of 0 => NatBot.of 1
  | NatBot.of (n + 1) => mulNat (n + 1) (f (NatBot.of n))

theorem monotone_factStep (f : NatBot → NatBot) : Monotone (factStep f) := by
  intro x y h
  rcases le_iff.mp h with h | h
  · subst h; exact bot_le' _
  · subst h; exact le_rfl

/-- **`F : (N⊥ ⊸ N⊥) → (N⊥ ⊸ N⊥)`.** `F(f)` is continuous because every
monotone map out of `N⊥` is, and strict by its first clause. -/
noncomputable def factFun (f : StrictHom NatBot NatBot) : StrictHom NatBot NatBot :=
  ⟨⟨factStep ⇑f.val, scottContinuous_of_monotone (monotone_factStep _)⟩, rfl⟩

@[simp] theorem factFun_apply (f : StrictHom NatBot NatBot) (x : NatBot) :
    (factFun f).val x = factStep (⇑f.val) x := rfl

theorem monotone_factFun : Monotone factFun := by
  intro f g h x
  cases x with
  | bot => exact bot_le' _
  | of n =>
    cases n with
    | zero => exact le_rfl
    | succ k => exact monotone_mulNat (k + 1) (h (NatBot.of k))

/-! ### Least upper bounds in `N⊥ ⊸ N⊥` are pointwise -/

section Eval

variable {α β : Type*} [Preorder α] [OrderBot α] [CompletePartialOrder β]

theorem directedOn_val_image_strict {s : Set (StrictHom α β)} (hd : DirectedOn (· ≤ ·) s) :
    DirectedOn (· ≤ ·) (Subtype.val '' s) := by
  rintro _ ⟨f, hf, rfl⟩ _ ⟨g, hg, rfl⟩
  obtain ⟨k, hk, hfk, hgk⟩ := hd f hf g hg
  exact ⟨k.val, ⟨k, hk, rfl⟩, hfk, hgk⟩

theorem isLUB_val_image_strict {s : Set (StrictHom α β)} (hd : DirectedOn (· ≤ ·) s)
    {F : StrictHom α β} (hF : IsLUB s F) : IsLUB (Subtype.val '' s) F.val := by
  have heq : F = sSup s := hF.unique (CompletePartialOrder.lubOfDirected s hd)
  rw [heq]
  exact (directedOn_val_image_strict hd).isLUB_sSup

/-- Evaluation of a least upper bound in `D ⊸ E` is a least upper bound in `E`. -/
theorem isLUB_eval_strict {s : Set (StrictHom α β)} (hd : DirectedOn (· ≤ ·) s)
    {F : StrictHom α β} (hF : IsLUB s F) (x : α) :
    IsLUB ((fun f : StrictHom α β => f.val x) '' s) (F.val x) := by
  have h := ScottHom.isLUB_eval_image_of_isLUB (directedOn_val_image_strict hd)
    (isLUB_val_image_strict hd hF) x
  rwa [Set.image_image] at h

end Eval

/-- **`F` is continuous.** The value at `⊥` and at `0` does not depend on the
argument function at all; at `n+1` the argument is evaluated at `n`, where
suprema in `N⊥ ⊸ N⊥` are pointwise, and `n+1 * ·` is continuous. -/
theorem scottContinuous_factFun : ScottContinuous factFun := by
  intro s hne hd F hF
  refine ⟨?_, ?_⟩
  · rintro _ ⟨f, hf, rfl⟩
    exact monotone_factFun (hF.1 hf)
  · intro u hu x
    obtain ⟨f₀, hf₀⟩ := id hne
    cases x with
    | bot => exact bot_le' _
    | of n =>
      cases n with
      | zero => exact hu ⟨f₀, hf₀, rfl⟩ (NatBot.of 0)
      | succ k =>
        have hE : DirectedOn (· ≤ ·)
            ((fun f : StrictHom NatBot NatBot => f.val (NatBot.of k)) '' s) := by
          rintro _ ⟨f, hf, rfl⟩ _ ⟨g, hg, rfl⟩
          obtain ⟨m, hm, hfm, hgm⟩ := hd f hf g hg
          exact ⟨m.val (NatBot.of k), ⟨m, hm, rfl⟩, hfm (NatBot.of k), hgm (NatBot.of k)⟩
        have hcont := scottContinuous_mulNat (k + 1) (hne.image _) hE
          (isLUB_eval_strict hd hF (NatBot.of k))
        refine hcont.2 ?_
        rintro _ ⟨_, ⟨f, hf, rfl⟩, rfl⟩
        exact hu ⟨f, hf, rfl⟩ (NatBot.of (k + 1))

/-- **`F` is not strict**: `F(⊥)(0) = 1`, so `F(⊥) ≠ ⊥`. The paper's
parenthesis, and the reason `fix(F)` is a total function rather than `⊥`. -/
theorem factFun_ne_bot : factFun ⊥ ≠ (⊥ : StrictHom NatBot NatBot) := by
  intro h
  have h0 : (factFun ⊥).val (NatBot.of 0) = (⊥ : StrictHom NatBot NatBot).val (NatBot.of 0) := by
    rw [h]
  simp only [factFun_apply, factStep] at h0
  exact NatBot.noConfusion h0

/-! ### `fix(F)` exists and is the factorial function -/

/-- The Fixed Point Theorem applied to `F`: the recursion has a least solution. -/
theorem isLeast_kleeneFix_factFun :
    IsLeast {f : StrictHom NatBot NatBot | factFun f = f} (kleeneFix factFun) :=
  theorem1 scottContinuous_factFun

/-- **`fix(F)` satisfies the equation for `fact`** — and its value at `n` is
`n!`, which is more than the paper asserts. -/
theorem kleeneFix_factFun_apply (n : ℕ) :
    (kleeneFix factFun).val (NatBot.of n) = NatBot.of n.factorial := by
  have hfix : factFun (kleeneFix factFun) = kleeneFix factFun :=
    map_kleeneFix scottContinuous_factFun
  induction n with
  | zero =>
    conv_lhs => rw [← hfix]
    rfl
  | succ k ih =>
    conv_lhs => rw [← hfix]
    show mulNat (k + 1) ((kleeneFix factFun).val (NatBot.of k)) = _
    rw [ih, Nat.factorial_succ]
    rfl

/-- `fix(F)` is undefined on `⊥`, because every member of `N⊥ ⊸ N⊥` is. -/
theorem kleeneFix_factFun_bot : (kleeneFix factFun).val NatBot.bot = NatBot.bot :=
  (kleeneFix factFun).2

/-- The factorial function as an element of `N⊥ ⊸ N⊥`. -/
def factVal : NatBot → NatBot
  | NatBot.bot => NatBot.bot
  | NatBot.of n => NatBot.of n.factorial

theorem monotone_factVal : Monotone factVal := by
  intro x y h
  rcases le_iff.mp h with h | h
  · subst h; exact bot_le' _
  · subst h; exact le_rfl

/-- `fact : N⊥ ⊸ N⊥`. -/
def factHom : StrictHom NatBot NatBot :=
  ⟨⟨factVal, scottContinuous_of_monotone monotone_factVal⟩, rfl⟩

/-- **`fix(F) = fact`.** The paper stops at "this solution will satisfy the
equation for `fact`"; this identifies the solution outright. -/
theorem kleeneFix_factFun_eq : kleeneFix factFun = factHom := by
  refine Subtype.ext (ScottHom.ext fun x => ?_)
  cases x with
  | bot => exact kleeneFix_factFun_bot
  | of n => exact kleeneFix_factFun_apply n

end ScottDomains.Kleene
