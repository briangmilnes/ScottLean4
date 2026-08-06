import ScottDomains.StepFunction

/-!
# `D → E` is algebraic

Gunter & Scott, *Semantic Domains*, Theorem 7's proof: "it is possible to show
that they form a basis for `D → E`". This file proves it, in the form
`IsAlgebraic (ScottHom α β)` for `D` algebraic and `E` algebraic and bounded
complete.

## Where each hypothesis is spent

The paper's hypotheses arrive as one block — "`D` and `E` bounded complete
domains" — but the two halves of `IsAlgebraic` use disjoint parts of it, and the
section boundaries below record which:

| # | Result | Needs |
| -- | ------ | ----- |
| 1 | `directedOn_image` | nothing but monotonicity |
| 2 | `directedOn_compactsBelow_scottHom` | `E` **bounded complete** only — not algebraicity of either |
| 3 | `isLUB_compactsBelow_scottHom` | `D` and `E` **algebraic** only — not bounded completeness |
| 4 | the `IsAlgebraic` instance | all of the above |

Result 2 holds because two compact functions below `f` are bounded by `f`, so
they have a least upper bound — that is r0007's `BoundedComplete (ScottHom α β)` —
and a least upper bound of two compacts is compact
(`Domain.lean`'s `isCompactElement_of_isLUB_pair`, which is not special to
function spaces).

Result 3 spends `E`'s algebraicity to reduce `f x ≤ u x` to the compact
approximants of `f x`, and `D`'s to produce from a compact `e ≤ f x` a compact
`k ≤ x` with `e ≤ f k`. The step functions of `StepFunction.lean` then convert
that pair `(k, e)` into a compact element of the function space below `f` — which
is what makes enough compact functions exist for the least upper bound to be `f`
itself.
-/

namespace ScottDomains

namespace ScottHom

variable {α β : Type*}

section Monotone

variable [Preorder α] [Preorder β]

/-- A monotone image of a directed set is directed. Needs no completeness at all;
the section boundaries in this file mark exactly what each group of results
uses. -/
theorem directedOn_image (f : ScottHom α β) {s : Set α} (hs : DirectedOn (· ≤ ·) s) :
    DirectedOn (· ≤ ·) (⇑f '' s) := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  obtain ⟨c, hc, hac, hbc⟩ := hs a ha b hb
  exact ⟨f c, ⟨c, hc, rfl⟩, f.monotone hac, f.monotone hbc⟩

end Monotone

section Directed

variable [Preorder α] [CompletePartialOrder β] [BoundedComplete β]

/-- The compact functions below `f` are directed: a pair of them is bounded by
`f`, so it has a least upper bound, which is compact by
`isCompactElement_of_isLUB_pair` and still below `f`. -/
theorem directedOn_compactsBelow_scottHom (f : ScottHom α β) :
    DirectedOn (· ≤ ·) (compactsBelow f) := by
  rintro g₁ ⟨hc₁, hf₁⟩ g₂ ⟨hc₂, hf₂⟩
  have hbdd : BddAbove ({g₁, g₂} : Set (ScottHom α β)) := by
    refine ⟨f, ?_⟩
    rintro h (rfl | rfl)
    · exact hf₁
    · exact hf₂
  have hlub := isLUB_sSup_of_bddAbove hbdd
  refine ⟨sSup ({g₁, g₂} : Set (ScottHom α β)),
    ⟨isCompactElement_of_isLUB_pair hc₁ hc₂ hlub, hlub.2 ?_⟩,
    hlub.1 (Set.mem_insert _ _), hlub.1 (Set.mem_insert_of_mem _ rfl)⟩
  rintro h (rfl | rfl)
  · exact hf₁
  · exact hf₂

end Directed

section Algebraic

variable [CompletePartialOrder α] [IsAlgebraic α]
variable [CompletePartialOrder β] [IsAlgebraic β]

/-- Every continuous function is the least upper bound of the compact functions
below it. The step functions of `StepFunction.lean` are what supply enough
compact functions for this to be true. -/
theorem isLUB_compactsBelow_scottHom (f : ScottHom α β) :
    IsLUB (compactsBelow f) f := by
  refine ⟨fun _ hg => hg.2, ?_⟩
  intro u hu x
  dsimp only
  -- `E` algebraic: reduce to the compact approximants of `f x`.
  refine (IsAlgebraic.isLUB_compactsBelow (f x)).2 ?_
  rintro e ⟨he, hef⟩
  -- `D` algebraic and `f` continuous: `f x` is the lub of `f '' compactsBelow x`.
  have hdir := IsAlgebraic.directedOn_compactsBelow (α := α) x
  have hfx : IsLUB (⇑f '' compactsBelow x) (f x) :=
    f.scottContinuous (compactsBelow_nonempty x) hdir (IsAlgebraic.isLUB_compactsBelow x)
  -- `e` is compact, so it is already below `f k` for some compact `k ≤ x`.
  obtain ⟨_, ⟨k, hk, rfl⟩, hek⟩ :=
    he (⇑f '' compactsBelow x) (f x) ((compactsBelow_nonempty x).image _)
      (directedOn_image f hdir) hfx hef
  -- The step function `step k e` is compact, lies below `f`, and takes value `e` at `x`.
  have hstep : step hk.1 e ∈ compactsBelow f :=
    ⟨isCompactElement_step hk.1 he, (step_le_iff hk.1).mpr hek⟩
  have := hu hstep x
  dsimp only at this
  rwa [coe_step, stepFun_of_le hk.2] at this

variable [BoundedComplete β]

/-- **`D → E` is algebraic.** With `Domain.lean`'s countability condition this is
Theorem 7 for the algebraic half; the countability of `K(D → E)` is separate.

This is the only declaration in the file needing all four hypotheses at once. -/
instance : IsAlgebraic (ScottHom α β) where
  directedOn_compactsBelow := directedOn_compactsBelow_scottHom
  isLUB_compactsBelow := isLUB_compactsBelow_scottHom

end Algebraic

end ScottHom

end ScottDomains
