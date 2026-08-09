/-
r0044, Class 1, agent1 — row 45 probe.

NOT part of the package. This file lives in `scripts/`, outside
`ScottDomains/ScottDomains/`, so `lake build` never sees it and `scripts/counts.sh`
never counts it. Run it with `scripts/a1-probe.sh scripts/a1-probe45.lean`.

**What it decides.** `ScottDomains.Kleene.sSup_recoverAt` states Gunter & Scott's
recovery equation (printed p. 9) under `[IsAlgebraic α] [IsAlgebraic β]
[BoundedComplete β]`. The paper imposes no bounded-completeness condition — its
sentence is about arbitrary domains `D` and `E` — so the Lean statement is a
strict weakening unless the hypothesis is forced. `Kleene/Graph.lean:36-45` asserts
it is forced: "bounded completeness of `E` — which the paper does not mention here
but which the argument cannot do without."

This probe refutes that assertion. `IsAlgebraic β` already carries
`directedOn_compactsBelow`, so an upper bound for the two values can be drawn from
`compactsBelow (f x₃)` instead of built as a join. The kernel accepts both
theorems below with `[BoundedComplete β]` deleted.
-/
import ScottDomains.Kleene.Graph

namespace A1Probe45

open ScottDomains ScottDomains.Kleene

variable {α β : Type*} [CompletePartialOrder α] [CompletePartialOrder β]

/-- Directedness of the recovering set with **no** `[BoundedComplete β]`. -/
theorem directedOn_recoverAt_bcFree [IsAlgebraic α] [IsAlgebraic β]
    {f : α → β} (hf : Monotone f) (x : α) :
    DirectedOn (· ≤ ·) (recoverAt f x) := by
  rintro y₁ ⟨x₁, ⟨hx₁c, hy₁c, hy₁⟩, hx₁x⟩ y₂ ⟨x₂, ⟨hx₂c, hy₂c, hy₂⟩, hx₂x⟩
  -- algebraicity of `D` merges the two compact arguments into one compact `x₃ ⊑ x`
  obtain ⟨x₃, hx₃, h13, h23⟩ :=
    IsAlgebraic.directedOn_compactsBelow x x₁ ⟨hx₁c, hx₁x⟩ x₂ ⟨hx₂c, hx₂x⟩
  -- both values are compact and below `f x₃`, so they lie in `compactsBelow (f x₃)`
  have hm₁ : y₁ ∈ compactsBelow (f x₃) := ⟨hy₁c, hy₁.trans (hf h13)⟩
  have hm₂ : y₂ ∈ compactsBelow (f x₃) := ⟨hy₂c, hy₂.trans (hf h23)⟩
  -- algebraicity of `E` — not bounded completeness — supplies the upper bound,
  -- and it is compact, so it is itself a member of `recoverAt f x` via `x₃`
  obtain ⟨y₃, hy₃, h₁, h₂⟩ :=
    IsAlgebraic.directedOn_compactsBelow (f x₃) y₁ hm₁ y₂ hm₂
  exact ⟨y₃, ⟨x₃, ⟨hx₃.1, hy₃.1, hy₃.2⟩, hx₃.2⟩, h₁, h₂⟩

/-- The paper's recovery equation itself, with **no** `[BoundedComplete β]`.
Body identical to `ScottDomains.Kleene.sSup_recoverAt`; only the directedness
lemma it calls has changed. -/
theorem sSup_recoverAt_bcFree [IsAlgebraic α] [IsAlgebraic β]
    {f : α → β} (hf : ScottContinuous f) (x : α) :
    sSup (recoverAt f x) = f x := by
  have hdir := directedOn_recoverAt_bcFree hf.monotone x
  refine le_antisymm (hdir.sSup_le ?_) ?_
  · rintro y ⟨x₀, ⟨_, _, hy⟩, hx₀⟩
    exact hy.trans (hf.monotone hx₀)
  · refine (hf (compactsBelow_nonempty x) (IsAlgebraic.directedOn_compactsBelow x)
      (IsAlgebraic.isLUB_compactsBelow x)).2 ?_
    rintro _ ⟨x₀, hx₀, rfl⟩
    refine (IsAlgebraic.isLUB_compactsBelow (f x₀)).2 ?_
    intro y₀ hy₀
    exact hdir.le_sSup ⟨x₀, ⟨hx₀.1, hy₀.1, hy₀.2⟩, hx₀.2⟩

#print axioms sSup_recoverAt_bcFree
#check @sSup_recoverAt_bcFree

end A1Probe45
