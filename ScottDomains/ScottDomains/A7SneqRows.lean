import Mathlib.Data.Set.Card
import ScottDomains.Kleene.Graph
import ScottDomains.MinimalUpperBounds

/-!
# r0049, agent7 — two of the thirteen `S≠` rows, restated as the paper states them

`docs/Status.md` row 9 counts 18 `S≠` rows, 13 of them defects of ours: a Lean
statement that is not the paper's. r0044's two Class-1 streams
(`reports/r0044-report-from-agent{1,2}-to-orchestrator-sneq-*.md`) enumerate them.
This file closes two, by the method r0047's agent4 proved out: state the paper's
sentence in a fresh namespace, prove it, and record an implication showing the
existing statement is not stronger.

## Row 45 — the recovery equation without `[BoundedComplete β]`

Gunter & Scott, printed p. 9:

> Let `G_f` be the set of pairs `(x₀, y₀)` such that `x₀ ∈ K(D)` and `y₀ ∈ K(E)`
> and `y₀ ⊑ f(x₀)`. If `x ∈ D`, then one may recover from `G_f` the value of `f`
> on `x` as `f(x) = ⨆{y₀ | (x₀, y₀) ∈ G_f and x₀ ⊑ x}`.

The sentence quantifies over all domains `D` and `E`.
`Kleene.sSup_recoverAt` carries `[BoundedComplete β]`, and `Kleene/Graph.lean`
used to assert the argument "cannot do without" it. r0044's agent1 refuted the
assertion with an out-of-package probe (`scripts/a1-probe45.lean`) and r0046
re-ran it; neither round landed the result **in** the package, so the row is
still `S≠`. `sSup_recoverAt_bcFree` is that statement inside the build, with
`sSup_recoverAt_imp_old` recording that the binder-free form implies the one the
development already had.

The mechanism, in one line: `IsAlgebraic β` carries `directedOn_compactsBelow`,
so an upper bound for two members of the recovering set can be **drawn from**
`compactsBelow (f x₃)` instead of **built** as a join. Bounded completeness built
the join; algebraicity already supplies a member above both, and it is compact,
so it lies in the recovering set itself.

## Row p9b — the stabilizing index

Gunter & Scott, printed p. 31, verbatim from `pdftotext -layout -f 32 -l 32`:

> Now, if `u ⊆ N ◁ A`, then `U(u) ⊆ N`. Hence, `Uⁿ(u) ⊆ N` for each `n`. If `N`
> is finite, then there must be an `n` for which `Uⁿ(u) = Uⁿ⁺¹(u)`. This is a
> third fact about Plotkin orders: for each finite `u ⊆ A`,
> `U^∞(u) = ⋃ₙ Uⁿ(u)` is finite.

r0044's agent2 classified this row **kind 2** — "incorrectly specified" — because
the nearest declaration, `JungFinite.mubDiff_nonempty`, states a different
proposition: its hypotheses are "every stage is finite" plus "`U^∞(u)` is
infinite", and its conclusion is that every successive difference is nonempty. It
is a true theorem serving the same end by a different route, and it does not
produce the paper's stabilizing index.

Sentences 1 and 2 were already stated and proved, at
`ScottDomains.mubClosure_subset_of_isNormalIn`. **The third sentence — the
stabilizing index — was the one nothing stated**, and it is what this file adds.
The proof is the counting argument the sentence elides: the stages are an
increasing chain inside a finite `N`, so `n ≤ |Uⁿ(u)| ≤ |N|` for every `n` if no
stage repeats, which fails at `n = |N| + 1`.
-/

namespace ScottDomains.R49.Agent7

/-! ## Row 45 -/

section Row45

open ScottDomains.Kleene

variable {α β : Type*} [CompletePartialOrder α] [CompletePartialOrder β]
variable [IsAlgebraic α] [IsAlgebraic β]

/-- Directedness of `{y₀ | (x₀,y₀) ∈ G_f, x₀ ⊑ x}` from algebraicity of `α` and
`β` — `Kleene.directedOn_recoverAt`'s statement with `[BoundedComplete β]`
deleted. The existing proof spends `[BoundedComplete β]` and *omits*
`[IsAlgebraic β]`; this one trades one for the other, which is the whole content
of the deletion. -/
theorem directedOn_recoverAt_bcFree {f : α → β} (hf : Monotone f) (x : α) :
    DirectedOn (· ≤ ·) (recoverAt f x) := by
  rintro y₁ ⟨x₁, ⟨hx₁c, hy₁c, hy₁⟩, hx₁x⟩ y₂ ⟨x₂, ⟨hx₂c, hy₂c, hy₂⟩, hx₂x⟩
  obtain ⟨x₃, hx₃, h13, h23⟩ :=
    IsAlgebraic.directedOn_compactsBelow x x₁ ⟨hx₁c, hx₁x⟩ x₂ ⟨hx₂c, hx₂x⟩
  have hm₁ : y₁ ∈ compactsBelow (f x₃) := ⟨hy₁c, hy₁.trans (hf h13)⟩
  have hm₂ : y₂ ∈ compactsBelow (f x₃) := ⟨hy₂c, hy₂.trans (hf h23)⟩
  obtain ⟨y₃, hy₃, h₁, h₂⟩ :=
    IsAlgebraic.directedOn_compactsBelow (f x₃) y₁ hm₁ y₂ hm₂
  exact ⟨y₃, ⟨x₃, ⟨hx₃.1, hy₃.1, hy₃.2⟩, hx₃.2⟩, h₁, h₂⟩

/-- **The paper's recovery equation, at the paper's hypotheses.**
`f(x) = ⨆{y₀ | (x₀,y₀) ∈ G_f, x₀ ⊑ x}` for algebraic `α` and `β`, with no
bounded-completeness condition on either. -/
theorem sSup_recoverAt_bcFree {f : α → β} (hf : ScottContinuous f) (x : α) :
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

/-- `G_f` determines `f`, likewise without `[BoundedComplete β]` —
`Kleene.eq_of_graphPairs_eq`'s statement, which spent the binder only through the
recovery equation. -/
theorem eq_of_graphPairs_eq_bcFree {f g : α → β} (hf : ScottContinuous f)
    (hg : ScottContinuous g) (h : graphPairs f = graphPairs g) : f = g := by
  funext x
  rw [← sSup_recoverAt_bcFree hf x, ← sSup_recoverAt_bcFree hg x]
  congr 1
  ext y₀
  constructor
  · rintro ⟨x₀, hmem, hx₀⟩
    exact ⟨x₀, h ▸ hmem, hx₀⟩
  · rintro ⟨x₀, hmem, hx₀⟩
    exact ⟨x₀, h ▸ hmem, hx₀⟩

/-- The binder-free statement implies `Kleene.sSup_recoverAt`'s: the bar was not
lowered, only a hypothesis dropped. -/
theorem sSup_recoverAt_imp_old [BoundedComplete β] {f : α → β} (hf : ScottContinuous f)
    (x : α) : sSup (recoverAt f x) = f x :=
  sSup_recoverAt_bcFree hf x

/-- Likewise for the determination statement. -/
theorem eq_of_graphPairs_eq_imp_old [BoundedComplete β] {f g : α → β}
    (hf : ScottContinuous f) (hg : ScottContinuous g) (h : graphPairs f = graphPairs g) :
    f = g :=
  eq_of_graphPairs_eq_bcFree hf hg h

end Row45

/-! ## Row p9b -/

section P9b

variable {α : Type*} [PartialOrder α] {A N u : Set α}

/-- The paper's "Hence, `Uⁿ(u) ⊆ N` for each `n`", read off
`mubClosure_subset_of_isNormalIn`. -/
theorem mubIter_subset_of_isNormalIn (hN : N ◁ A) (huN : u ⊆ N) (n : ℕ) :
    mubIter A u n ⊆ N :=
  (mubIter_subset_mubClosure A u n).trans (mubClosure_subset_of_isNormalIn hN huN)

/-- **The paper's stabilizing index**: "If `N` is finite, then there must be an
`n` for which `Uⁿ(u) = Uⁿ⁺¹(u)`."

The stages increase (`mubIter_subset_succ`) and all sit inside the finite `N`. If
no stage repeated, `n ↦ |Uⁿ(u)|` would be strictly increasing, hence `n ≤ |Uⁿ(u)|`
for every `n`, while `|Uⁿ(u)| ≤ |N|` throughout. Taking `n = |N| + 1` is the
contradiction. -/
theorem exists_mubIter_eq_succ_of_isNormalIn (hN : N ◁ A) (hfin : N.Finite) (huN : u ⊆ N) :
    ∃ n, mubIter A u n = mubIter A u (n + 1) := by
  by_contra hno'
  have hno : ∀ n, mubIter A u n ≠ mubIter A u (n + 1) := fun n h => hno' ⟨n, h⟩
  have hsub : ∀ n, mubIter A u n ⊆ N := mubIter_subset_of_isNormalIn hN huN
  have hlt : ∀ n, (mubIter A u n).ncard < (mubIter A u (n + 1)).ncard := fun n =>
    Set.ncard_lt_ncard
      (ssubset_iff_subset_ne.mpr ⟨mubIter_subset_succ A u n, hno n⟩)
      (hfin.subset (hsub (n + 1)))
  have hgrow : ∀ n, n ≤ (mubIter A u n).ncard := by
    intro n
    induction n with
    | zero => exact Nat.zero_le _
    | succ n ih => exact Nat.succ_le_of_lt (lt_of_le_of_lt ih (hlt n))
  have h₁ := hgrow (N.ncard + 1)
  have h₂ : (mubIter A u (N.ncard + 1)).ncard ≤ N.ncard :=
    Set.ncard_le_ncard (hsub _) hfin
  omega

/-- The paper's "third fact about Plotkin orders", which the previous two
sentences are stated in order to reach: `U^∞(u)` is finite. -/
theorem finite_mubClosure_of_isNormalIn (hN : N ◁ A) (hfin : N.Finite) (huN : u ⊆ N) :
    (mubClosure A u).Finite :=
  hfin.subset (mubClosure_subset_of_isNormalIn hN huN)

end P9b

end ScottDomains.R49.Agent7
