import ScottDomains.UniformFixedPoint
import ScottDomains.Kleene.FixContinuous

/-!
# `fix` **is** a uniform fixed point operator — the existence half of Theorem 3

Gunter & Scott, *Semantic Domains*, §2.3 (printed p. 7):

> … we have `h(F_D(f)) = F_E(g)`. We leave it to the reader to show that `fix` is
> a uniform fixed point operator. What is less obvious, and somewhat more
> surprising, is the following:
>
> **Theorem 3** `fix` is *the* unique *uniform fixed point operator*.

## Why this file exists

`UniformFixedPoint.lean` proves `theorem_3`: *every* uniform fixed point operator
equals `fix`. That is the uniqueness half. The existence half — that `fix` is
itself uniform — the paper leaves to the reader, and the development left it
undone: the r0040 property audit found that the docstring at
`UniformFixedPoint.lean:168` *declines to assert* the claim rather than asserting
it, so `theorem_3` was a uniqueness theorem with its existence half missing. A
uniqueness statement about a class that has not been shown nonempty is
vacuous-safe but says strictly less than the paper's theorem, which asserts that
`fix` *is* the unique uniform operator.

`kleeneOperator_isUniform` supplies existence, and `theorem_3_existsUnique` is
then the paper's sentence in one statement: `∃! F, F.IsUniform`.

## The proof of uniformity

Let `h : D ⊸ E` be strict and continuous with `h ∘ f = g ∘ h`. Induction on `n`
gives `h(fⁿ(⊥_D)) = gⁿ(⊥_E)`: the base case is strictness, and the step is the
commuting square. Hence `h` carries the Kleene chain of `f` onto the Kleene chain
of `g` as sets (`image_kleeneChain`), and continuity of `h` carries the supremum
of the first to the supremum of the second. Uniqueness of least upper bounds
finishes it.

Note which hypotheses do the work: strictness is used exactly once, at `n = 0`,
and it is indispensable — without it `h(⊥)` need not be `⊥` and the two chains
need not start together.

## Conformance to the paper's definition

The paper's definition asks a fixed point operator to be a class of *continuous*
functions `F_D : (D → D) → D`. `FixedPointOperator` deliberately omits that
hypothesis, because `theorem_3`'s uniqueness proof does not use it and dropping it
strengthens the theorem. `scottContinuous_kleeneOperator_op` records that `fix`
satisfies it anyway, by `Kleene.scottContinuous_kleeneFix` — so the existence
witness meets the paper's definition in full, not only the weakened one.
-/

namespace ScottDomains.Kleene

universe u

section Commuting

variable {α β : Type*} [CompletePartialOrder α] [CompletePartialOrder β]

/-- A strict `h` making the square commute carries iterates to iterates:
`h(fⁿ(⊥)) = gⁿ(⊥)`. The base case is strictness; the step is the square. -/
theorem map_iterate_bot {f : α → α} {g : β → β} {h : α → β} (hbot : h ⊥ = ⊥)
    (hsq : ∀ x, h (f x) = g (h x)) : ∀ n : ℕ, h (f^[n] ⊥) = g^[n] ⊥ := by
  intro n
  induction n with
  | zero => simpa using hbot
  | succ k ih =>
    rw [Function.iterate_succ_apply' f k, Function.iterate_succ_apply' g k, hsq, ih]

/-- `h` carries the Kleene chain of `f` **onto** the Kleene chain of `g`. -/
theorem image_kleeneChain {f : α → α} {g : β → β} {h : α → β} (hbot : h ⊥ = ⊥)
    (hsq : ∀ x, h (f x) = g (h x)) : h '' kleeneChain f = kleeneChain g := by
  ext y
  constructor
  · rintro ⟨_, ⟨n, rfl⟩, rfl⟩
    exact ⟨n, (map_iterate_bot hbot hsq n).symm⟩
  · rintro ⟨n, rfl⟩
    exact ⟨f^[n] ⊥, ⟨n, rfl⟩, map_iterate_bot hbot hsq n⟩

/-- **`fix` is uniform**, on the underlying functions: a strict continuous `h`
with `h ∘ f = g ∘ h` satisfies `h(fix f) = fix g`. -/
theorem map_kleeneFix_of_commutes {f : α → α} {g : β → β} {h : α → β}
    (hf : Monotone f) (hg : Monotone g) (hh : ScottContinuous h)
    (hbot : h ⊥ = ⊥) (hsq : ∀ x, h (f x) = g (h x)) :
    h (kleeneFix f) = kleeneFix g := by
  have hlub : IsLUB (h '' kleeneChain f) (h (kleeneFix f)) :=
    hh kleeneChain_nonempty (directedOn_kleeneChain hf) (directedOn_kleeneChain hf).isLUB_sSup
  rw [image_kleeneChain hbot hsq] at hlub
  exact hlub.unique (directedOn_kleeneChain hg).isLUB_sSup

end Commuting

/-- Each `fix_D` is continuous, so `fix` satisfies the paper's own definition of
a fixed point operator in full — `FixedPointOperator` omits the continuity
requirement because `theorem_3` does not need it. -/
theorem scottContinuous_kleeneOperator_op (D : Type u) [CompletePartialOrder D] :
    ScottContinuous (kleeneOperator.op D) :=
  scottContinuous_kleeneFix

/-- **`fix` is a uniform fixed point operator** — the claim §2.3 leaves to the
reader, and the existence half of Theorem 3. -/
theorem kleeneOperator_isUniform : (kleeneOperator.{u}).IsUniform := by
  intro D E _ _ f g h hbot hsq
  exact map_kleeneFix_of_commutes f.monotone g.monotone h.scottContinuous hbot hsq

/-- Two uniform fixed point operators are equal. `theorem_3` sends each to `fix`
pointwise, and a `FixedPointOperator` is determined by its `op` field. -/
theorem eq_of_isUniform {F G : FixedPointOperator.{u}} (hF : F.IsUniform)
    (hG : G.IsUniform) : F = G := by
  obtain ⟨opF, hopF⟩ := F
  obtain ⟨opG, hopG⟩ := G
  have h : opF = opG := by
    funext D inst f
    letI := inst
    exact (theorem_3 ⟨opF, hopF⟩ hF D f).trans (theorem_3 ⟨opG, hopG⟩ hG D f).symm
  subst h
  rfl

/-- **Theorem 3, both halves.** `fix` is *the* unique uniform fixed point
operator: the class of uniform fixed point operators has exactly one member, and
`kleeneOperator` is it.

`UniformFixedPoint.theorem_3` alone gives only the uniqueness half; the existence
half is `kleeneOperator_isUniform`. -/
theorem theorem_3_existsUnique : ∃! F : FixedPointOperator.{u}, F.IsUniform :=
  ⟨kleeneOperator, kleeneOperator_isUniform, fun _ hG => eq_of_isUniform hG kleeneOperator_isUniform⟩

end ScottDomains.Kleene
