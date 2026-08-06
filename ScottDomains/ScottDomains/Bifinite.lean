import ScottDomains.NormalSubposet
import ScottDomains.Domain

/-!
# §6.1: Plotkin orders and bifinite domains

Gunter & Scott, *Semantic Domains*, §6.1:

> **Definition:** A poset `A` is a **Plotkin order** if, for every finite subset
> `u ⊆ A`, there is a finite set `N ◁ A` with `u ⊆ N`.

A domain is **bifinite** (or SFP) when its basis `K(D)` is a Plotkin order — the
condition on the basis that characterizes the domain as a bilimit of finite
pointed posets.

## Why this definition costs almost nothing here

Everything it quantifies over already exists: `◁` is `IsNormalIn` from r0012 and
`K(D)` is `compacts` from r0004. The definition is one line, and the two sanity
results below are the only content — that the condition is inherited by the
finite sets it produces, and that it is nontrivial in the sense of always
containing `⊥`.

The §6 results themselves (Proposition 15, Theorems 16 and 18, Lemmas 17, 19 and
20) all quantify over this predicate; none is proved here.
-/

namespace ScottDomains

variable {α : Type*}

section PlotkinOrder

variable [Preorder α]

/-- A **Plotkin order**: every finite subset is contained in a finite normal
subposet. -/
def IsPlotkinOrder (A : Set α) : Prop :=
  ∀ u : Set α, u.Finite → u ⊆ A → ∃ N : Set α, N.Finite ∧ N ◁ A ∧ u ⊆ N

/-- The witness for a finite `u` is itself finite and normal, so a Plotkin order
supplies a finite normal subposet above any finite set of interest — which is how
§6 uses it. -/
theorem IsPlotkinOrder.exists_finite_normal {A : Set α} (h : IsPlotkinOrder A)
    {u : Set α} (hu : u.Finite) (hsub : u ⊆ A) :
    ∃ N : Set α, N.Finite ∧ N ◁ A ∧ u ⊆ N := h u hu hsub

/-- Applied to the empty set, a Plotkin order still yields a finite normal
subposet — the base case §6's inductions start from. -/
theorem IsPlotkinOrder.exists_finite_normal_empty {A : Set α} (h : IsPlotkinOrder A) :
    ∃ N : Set α, N.Finite ∧ N ◁ A :=
  let ⟨N, hfin, hnorm, _⟩ := h ∅ Set.finite_empty (Set.empty_subset A)
  ⟨N, hfin, hnorm⟩

end PlotkinOrder

section Bifinite

variable [CompletePartialOrder α]

/-- A **bifinite** (SFP) domain: one whose basis is a Plotkin order. -/
def IsBifinite (α : Type*) [CompletePartialOrder α] : Prop :=
  IsPlotkinOrder (compacts α)

/-- In a bifinite domain, the finite normal subposet produced for any finite set
of compacts contains `⊥` — by Lemma 4.3, since `⊥` is compact. -/
theorem IsBifinite.bot_mem_of_normal (_h : IsBifinite α) {N : Set α}
    (hN : N ◁ compacts α) : (⊥ : α) ∈ N :=
  hN.bot_mem isCompactElement_bot

end Bifinite

end ScottDomains
