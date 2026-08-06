import ScottDomains.ScottHom

/-!
# Step functions

Gunter & Scott, *Semantic Domains*, in the proof of Theorem 7:

> Suppose `N ⊆ K(D)` is finite and `s : N → K(E)` is monotone. Then the function
> `step(s) : D → E` given by `step(s)(x) = ⨆{s(y) | y ∈ N ∩ ↓x}` is continuous
> and compact in the ordering on `D → E`. These are called step functions and it
> is possible to show that they form a basis for `D → E`.

This file treats the case `N = {k}`, written `step k e`: the function sending `x`
to `e` when `k ⊑ x` and to `⊥` otherwise. The general `step(s)` is the join of
these over `y ∈ N`, which needs `E` bounded complete and needs joins of compacts
to be compact — two obligations independent of anything here, and separated from
it deliberately.

## What each result costs

* **Continuity uses compactness of `k`, and nothing else does.** If `k ⊑ ⨆M` for
  directed `M`, compactness produces `y ∈ M` with `k ⊑ y`, so the value `e` is
  already attained in the image; otherwise `k` is below no member of `M` and the
  image is `{⊥}`.
* **The adjunction `step k e ≤ f ↔ e ≤ f k` costs nothing at all** — no
  compactness, no completeness. It is the workhorse: every statement about a step
  function becomes a statement about one value of `f`.
* **Compactness of `step k e` needs `e` compact, not `k`.** The proof runs
  entirely through the adjunction and the fact that suprema in `ScottHom` are
  computed pointwise.
-/

namespace ScottDomains

namespace ScottHom

variable {α β : Type*}

section StepFun

variable [PartialOrder α] [Preorder β] [OrderBot β] {k : α} {e : β}

open Classical in
/-- The underlying function of a single step function: `e` above `k`, `⊥`
elsewhere. `k ≤ x` is not decidable in general, so the branch is classical. -/
noncomputable def stepFun (k : α) (e : β) : α → β := fun x => if k ≤ x then e else ⊥

theorem stepFun_of_le {x : α} (h : k ≤ x) : stepFun k e x = e := by
  classical simp only [stepFun, if_pos h]

theorem stepFun_of_not_le {x : α} (h : ¬ k ≤ x) : stepFun k e x = ⊥ := by
  classical simp only [stepFun, if_neg h]

@[simp] theorem stepFun_self : stepFun k e k = e := stepFun_of_le le_rfl

theorem monotone_stepFun : Monotone (stepFun k e) := by
  intro x y hxy
  by_cases hx : k ≤ x
  · rw [stepFun_of_le hx, stepFun_of_le (hx.trans hxy)]
  · rw [stepFun_of_not_le hx]
    exact bot_le

end StepFun

section Continuity

variable [PartialOrder α] [CompletePartialOrder β] {k : α} {e : β}

/-- A step function is Scott continuous exactly because `k` is compact: if the
least upper bound of a directed set lies above `k`, some member of the set
already does, so the value `e` is attained in the image. This is the only use of
`IsCompactElement k` in the file. -/
theorem scottContinuous_stepFun (hk : IsCompactElement k) (e : β) :
    ScottContinuous (stepFun k e) := by
  intro s hne hs a ha
  by_cases hka : k ≤ a
  · obtain ⟨y, hy, hky⟩ := hk s a hne hs ha hka
    refine ⟨?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact monotone_stepFun (ha.1 hx)
    · intro u hu
      rw [stepFun_of_le hka, ← stepFun_of_le (e := e) hky]
      exact hu ⟨y, hy, rfl⟩
  · have himg : ∀ x ∈ s, stepFun k e x = ⊥ := fun x hx =>
      stepFun_of_not_le fun hkx => hka (hkx.trans (ha.1 hx))
    refine ⟨?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩
      rw [himg x hx]
      exact bot_le
    · intro u _
      rw [stepFun_of_not_le hka]
      exact bot_le

/-- The single step function as an element of the function space. -/
noncomputable def step (hk : IsCompactElement k) (e : β) : ScottHom α β :=
  ⟨stepFun k e, scottContinuous_stepFun hk e⟩

@[simp] theorem coe_step (hk : IsCompactElement k) : ⇑(step hk e) = stepFun k e := rfl

@[simp] theorem step_self (hk : IsCompactElement k) : step hk e k = e := stepFun_self

/-- The defining adjunction: a step function sits below `f` exactly when its
value sits below `f`'s value at `k`. Every later fact about step functions is
proved through this rather than by unfolding `stepFun`. -/
theorem step_le_iff (hk : IsCompactElement k) {f : ScottHom α β} :
    step hk e ≤ f ↔ e ≤ f k := by
  constructor
  · intro h
    have hk' := h k
    dsimp only at hk'
    rwa [coe_step, stepFun_self] at hk'
  · intro h x
    dsimp only
    rw [coe_step]
    by_cases hkx : k ≤ x
    · rw [stepFun_of_le hkx]
      exact h.trans (f.monotone hkx)
    · rw [stepFun_of_not_le hkx]
      exact bot_le

/- UNUSED — commented out, kept for reading. Monotonicity of `step` in its value.
Written on the assumption that comparing step functions would come up; it never
did — every later use goes through `step_le_iff` against an arbitrary `f`, which
is strictly more general. Instructive as the shortest possible demonstration that
the adjunction is the only tool needed: the whole proof is one `mpr` and a
rewrite.

/-- Step functions are monotone in their value. -/
theorem step_mono (hk : IsCompactElement k) {e₁ e₂ : β} (h : e₁ ≤ e₂) :
    step hk e₁ ≤ step hk e₂ :=
  (step_le_iff hk).mpr (by rw [step_self]; exact h)
-/

/-- A step function with a compact value is compact in the function space.

Note which compactness is used where: `IsCompactElement e` drives this proof,
while `IsCompactElement k` appears only because `step` needs it to be continuous.
The argument is entirely through `step_le_iff` and the fact that suprema in
`ScottHom` are pointwise. -/
theorem isCompactElement_step (hk : IsCompactElement k) (he : IsCompactElement e) :
    IsCompactElement (step hk e) := by
  intro d F hne hd hF hstep
  have hFsSup : F = sSup d := hF.unique (DirectedOn.isLUB_sSup hd)
  have hlub : IsLUB ((fun f : ScottHom α β => f k) '' d) (F k) := by
    rw [hFsSup, coe_sSup_of_directed hd]
    exact (directedOn_eval_image hd k).isLUB_sSup
  obtain ⟨_, ⟨f, hf, rfl⟩, hef⟩ :=
    he ((fun f : ScottHom α β => f k) '' d) (F k) (hne.image _)
      (directedOn_eval_image hd k) hlub ((step_le_iff hk).mp hstep)
  exact ⟨f, hf, (step_le_iff hk).mpr hef⟩

end Continuity

end ScottHom

end ScottDomains
