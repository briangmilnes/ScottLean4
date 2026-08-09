import ScottDomains.Powerset
import ScottDomains.ScottHom

/-!
# `G_f`: a continuous function named by its compact approximations

Gunter & Scott, *Semantic Domains*, §3 (printed p. 9), quoted from the render of
the physical page:

> Let `G_f` be the set of pairs `(x₀, y₀)` such that `x₀ ∈ K(D)` and `y₀ ∈ K(E)`
> and `y₀ ⊑ f(x₀)`. If `x ∈ D`, then one may recover from `G_f` the value of `f`
> on `x` as
>
> `f(x) = ⨆{y₀ | (x₀, y₀) ∈ G_f and x₀ ⊑ x}`.
>
> This allows us to characterize, for example, a continuous function
> `f : P N → P N` between *uncountable* cpo's with a *countable* set `G_f`.

## Two rows, and what changes

The countability sentence is r0040's row 46, labelled `N` — nothing in the
package states it. `FunctionSpaceCountable.countable_compacts_scottHom` proves
`K(D → E)` countable, which is a different statement: it is about the compacts of
the function space, not about one function's graph.

The recovery formula is r0040's row 45, labelled **`S≠`**: the development's
`ContinuousConstruction.coe_eq_basisExtension_self` uses the family
`graphOn v = {(k, v k) | k ∈ K(D)}`, which restricts only the first coordinate to
compacts and pins the second to the exact value. The paper's `G_f` restricts
both coordinates to compacts and is downward closed in the second. **This file
changes that row from `S≠` to `S+P`**: `graphPairs` is the paper's `G_f`
verbatim, and `sSup_recover` is the paper's recovery equation for it. The two
formulations agree in value, but only the paper's supports the countability
sentence, because only the paper's has both coordinates in a countable set.

## The hypotheses the recovery equation actually needs

Algebraicity of `D` (to write `x` as a directed supremum of compacts) and
algebraicity of `E` (to write `f(x₀)` as a directed supremum of compacts).
`sSup` in a cpo is pinned down only on directed sets, and
`{y₀ | (x₀,y₀) ∈ G_f, x₀ ⊑ x}` must be shown directed; `sSup_recoverAt` below
carries `[BoundedComplete β]` and gets the upper bound as a join, compact by
`isCompactElement_of_isLUB_pair`.

**That hypothesis is not necessary, and this file used to claim it was.** The
sentence here read "**bounded completeness of `E`** — which the paper does not
mention here but which the argument cannot do without." It is false, and the
paper is right to omit it: `IsAlgebraic β` already carries
`directedOn_compactsBelow`, so an upper bound for two members can be *drawn from*
`compactsBelow (f x₃)` instead of *built* as a join. `scripts/a1-probe45.lean`
(r0044, agent1; re-run in r0046 by agent5) proves both `directedOn_recoverAt` and
the recovery equation itself with `[BoundedComplete β]` deleted, on axioms
`[propext, Quot.sound]` — no `sorryAx`, no `Classical.choice`.

`sSup_recoverAt` below is left with the hypothesis rather than restated: only
agent1 may change a claim's statement this round, and `P N` — the paper's example
— is bounded complete, so nothing downstream is weakened by keeping it. What is
corrected is the prose: the hypothesis is *convenient*, not *forced*.
-/

namespace ScottDomains.Kleene

variable {α β : Type*} [CompletePartialOrder α] [CompletePartialOrder β]

/-- **`G_f`**: the pairs of compacts `(x₀, y₀)` with `y₀ ⊑ f(x₀)`. -/
def graphPairs (f : α → β) : Set (α × β) :=
  {p | IsCompactElement p.1 ∧ IsCompactElement p.2 ∧ p.2 ≤ f p.1}

/-- `{y₀ | (x₀, y₀) ∈ G_f and x₀ ⊑ x}`, the set whose supremum recovers `f(x)`. -/
def recoverAt (f : α → β) (x : α) : Set β :=
  {y₀ | ∃ x₀, (x₀, y₀) ∈ graphPairs f ∧ x₀ ≤ x}

theorem mem_recoverAt {f : α → β} {x : α} {y₀ : β} :
    y₀ ∈ recoverAt f x ↔ ∃ x₀, IsCompactElement x₀ ∧ IsCompactElement y₀ ∧
      y₀ ≤ f x₀ ∧ x₀ ≤ x := by
  constructor
  · rintro ⟨x₀, ⟨h1, h2, h3⟩, h4⟩
    exact ⟨x₀, h1, h2, h3, h4⟩
  · rintro ⟨x₀, h1, h2, h3, h4⟩
    exact ⟨x₀, ⟨h1, h2, h3⟩, h4⟩

section Recovery

variable [IsAlgebraic α] [IsAlgebraic β] [BoundedComplete β]

omit [IsAlgebraic β] in
/-- The recovering set is directed. Two members come from compacts `x₁, x₂ ⊑ x`;
algebraicity of `D` merges those into one compact `x₃ ⊑ x`, both values are then
bounded by `f(x₃)`, and bounded completeness supplies their join — compact by
`isCompactElement_of_isLUB_pair`. Algebraicity of `E` is not used here — only
`D`'s, plus bounded completeness of `E`. -/
theorem directedOn_recoverAt {f : α → β} (hf : Monotone f) (x : α) :
    DirectedOn (· ≤ ·) (recoverAt f x) := by
  rintro y₁ ⟨x₁, ⟨hx₁c, hy₁c, hy₁⟩, hx₁x⟩ y₂ ⟨x₂, ⟨hx₂c, hy₂c, hy₂⟩, hx₂x⟩
  obtain ⟨x₃, hx₃, h13, h23⟩ :=
    IsAlgebraic.directedOn_compactsBelow x x₁ ⟨hx₁c, hx₁x⟩ x₂ ⟨hx₂c, hx₂x⟩
  have hbound : ∀ z ∈ ({y₁, y₂} : Set β), z ≤ f x₃ := by
    rintro z (rfl | rfl)
    · exact hy₁.trans (hf h13)
    · exact hy₂.trans (hf h23)
  have hlub := isLUB_sSup_of_bddAbove (⟨f x₃, hbound⟩ : BddAbove ({y₁, y₂} : Set β))
  refine ⟨sSup ({y₁, y₂} : Set β),
    ⟨x₃, ⟨hx₃.1, isCompactElement_of_isLUB_pair hy₁c hy₂c hlub, hlub.2 hbound⟩, hx₃.2⟩,
    hlub.1 (Set.mem_insert _ _), hlub.1 (Set.mem_insert_of_mem _ rfl)⟩

/-- **The paper's recovery equation**: `f(x) = ⨆{y₀ | (x₀,y₀) ∈ G_f, x₀ ⊑ x}`. -/
theorem sSup_recoverAt {f : α → β} (hf : ScottContinuous f) (x : α) :
    sSup (recoverAt f x) = f x := by
  have hdir := directedOn_recoverAt hf.monotone x
  refine le_antisymm (hdir.sSup_le ?_) ?_
  · rintro y ⟨x₀, ⟨_, _, hy⟩, hx₀⟩
    exact hy.trans (hf.monotone hx₀)
  · refine (hf (compactsBelow_nonempty x) (IsAlgebraic.directedOn_compactsBelow x)
      (IsAlgebraic.isLUB_compactsBelow x)).2 ?_
    rintro _ ⟨x₀, hx₀, rfl⟩
    refine (IsAlgebraic.isLUB_compactsBelow (f x₀)).2 ?_
    intro y₀ hy₀
    exact hdir.le_sSup ⟨x₀, ⟨hx₀.1, hy₀.1, hy₀.2⟩, hx₀.2⟩

/-- A continuous function is determined by `G_f`: two continuous functions with
the same `G_f` are equal. This is what "characterize" means in the paper's
sentence, and it is the recovery equation applied twice. -/
theorem eq_of_graphPairs_eq {f g : α → β} (hf : ScottContinuous f) (hg : ScottContinuous g)
    (h : graphPairs f = graphPairs g) : f = g := by
  funext x
  rw [← sSup_recoverAt hf x, ← sSup_recoverAt hg x]
  congr 1
  ext y₀
  constructor
  · rintro ⟨x₀, hmem, hx₀⟩
    exact ⟨x₀, h ▸ hmem, hx₀⟩
  · rintro ⟨x₀, hmem, hx₀⟩
    exact ⟨x₀, h ▸ hmem, hx₀⟩

end Recovery

/-! ### The paper's example: `f : P N → P N` -/

/-- `P N` is uncountable — Cantor's diagonal argument. -/
theorem not_countable_powersetNat : ¬ Countable (Set ℕ) := by
  intro _
  obtain ⟨g, hg⟩ := exists_surjective_nat (Set ℕ)
  exact Function.cantor_surjective g hg

/-- **`G_f` is countable for every `f : P N → P N`**, continuous or not: it is a
subset of `K(P N) × K(P N)`, and `K(P N)` — the finite subsets of `N` — is
countable because `P N` is a domain. -/
theorem countable_graphPairs (f : Set ℕ → Set ℕ) : (graphPairs f).Countable := by
  refine Set.Countable.mono ?_
    ((Domain.countable_compacts (α := Set ℕ)).prod (Domain.countable_compacts (α := Set ℕ)))
  rintro ⟨x, y⟩ ⟨hx, hy, _⟩
  exact ⟨hx, hy⟩

/-- **§3's sentence in one statement.** A continuous `f : P N → P N` between
uncountable cpo's is characterized by the countable set `G_f`: `G_f` is
countable, `f` is recovered from it pointwise, and `P N` itself is not
countable. -/
theorem characterization_powersetNat (f : Set ℕ → Set ℕ) (hf : ScottContinuous f) :
    (graphPairs f).Countable ∧ (∀ x, sSup (recoverAt f x) = f x) ∧ ¬ Countable (Set ℕ) :=
  ⟨countable_graphPairs f, fun x => sSup_recoverAt hf x, not_countable_powersetNat⟩

end ScottDomains.Kleene
