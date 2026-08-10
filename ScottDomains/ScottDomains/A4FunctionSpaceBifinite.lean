import ScottDomains.A4Lemma17Fun
-- `PRepFun.isStrict_of_le` and `PRepFun.val_image_compactsBelow`, the two
-- binder-free ingredients of `Domain (D →⊥ E)`; not reachable from the import above.
import ScottDomains.PRepFun

/-!
# `D → E` is a domain when `D` and `E` are bifinite — no bounded completeness

`FunctionSpaceDomain.lean:121` and `FunctionSpaceCountable.lean:122` build
`IsAlgebraic (ScottHom α β)` and `Domain (ScottHom α β)` under
`[Domain α] [Domain β] [BoundedComplete β]`. Both go through the step-function
decomposition, so both inherit the binder that `A4Lemma17Fun.lean` removed from
Lemma 17's conjunct.

This file rebuilds both from bifiniteness instead, using the same directed family
of finitary projections:

* **Algebraic.** `approx f ⊆ compactsBelow f` (`approx_subset_compactsBelow`) and
  `IsLUB (approx f) f` (`isLUB_approx`) together give `IsLUB (compactsBelow f) f`
  immediately. Directedness of `compactsBelow f` is the same two facts plus
  compactness: a compact `g ≤ f` is below some member of `approx f`, and
  `approx f` is directed.
* **Countable basis.** Every compact `f` is `(p_{N₂}, p_{N₁})(f)` for finite
  normal `N₁ ◁ K(D)`, `N₂ ◁ K(E)` (`exists_normal_fixing`), so `K(D → E)` is
  covered by the images of those projections. Each image is finite
  (`finite_range_compHom`) and the pairs `(N₁, N₂)` are drawn from the finite
  subsets of the countable `K(D)` and `K(E)`, so the cover is a countable union
  of finite sets.

Why this matters beyond tidiness: `LemThirty.Theorem29SecondAtDomains` quantifies over
`[Domain E]`, and `Theorem29Second` — the form without that binder — is refuted
(`R45.Agent3.not_thm29Second`). So `Retracts (ScottHom V V)` is reachable only
through the `Domain` form, and `Domain (ScottHom V V)` was itself unavailable
because `V` is not bounded complete (`R45.Agent3.not_boundedComplete_V`).
`domain_scottHom` below supplies it.
-/

namespace ScottDomains.R47.Agent4

open ScottDomains ScottHom

variable {α β : Type*} [CompletePartialOrder α] [CompletePartialOrder β]

section Algebraic

variable [Domain α] [Domain β]

/-- **`D → E` is algebraic when `D` and `E` are bifinite.** Compare
`ScottHom.instIsAlgebraic` (`FunctionSpaceDomain.lean:121`), which needs
`[BoundedComplete β]`. Both fields are read off `approx f`: it is a directed set
of compacts below `f` with least upper bound `f`, and every compact below `f` is
dominated by one of its members. -/
theorem isAlgebraic_scottHom (h₁ : IsBifinite α) (h₂ : IsBifinite β) :
    IsAlgebraic (ScottHom α β) :=
  { directedOn_compactsBelow := by
      intro f g₁ hg₁ g₂ hg₂
      obtain ⟨a₁, ha₁, hle₁⟩ :=
        hg₁.1 (approx f) f (approx_nonempty h₁ h₂ f) (directedOn_approx h₁ h₂ f)
          (isLUB_approx h₁ h₂ f) hg₁.2
      obtain ⟨a₂, ha₂, hle₂⟩ :=
        hg₂.1 (approx f) f (approx_nonempty h₁ h₂ f) (directedOn_approx h₁ h₂ f)
          (isLUB_approx h₁ h₂ f) hg₂.2
      obtain ⟨c, hc, hac₁, hac₂⟩ := directedOn_approx h₁ h₂ f a₁ ha₁ a₂ ha₂
      exact ⟨c, approx_subset_compactsBelow f hc, hle₁.trans hac₁, hle₂.trans hac₂⟩
    isLUB_compactsBelow := fun f =>
      ⟨fun _ hg => hg.2, fun _ hv =>
        (isLUB_approx h₁ h₂ f).2 fun _ ha => hv (approx_subset_compactsBelow f ha)⟩ }

/-! ### The countable cover of `K(D → E)` -/

/-- The functions fixed by `(p_{N₂}, p_{N₁})`, as a predicate on the two *sets*
alone. The normality proofs are existentially bound, so this is a function of
data only — which is what a countable cover has to be indexed by — and it is
empty unless both sets are normal. `IsNormalIn` is a `Prop`, so the bound proofs
are the ones any use site already has. -/
def fixedBy (N₁ : Set α) (N₂ : Set β) : Set (ScottHom α β) :=
  {f | ∃ (hN₁ : N₁ ◁ compacts α) (hN₂ : N₂ ◁ compacts β),
    compHom (normalHom hN₁) (normalHom hN₂) f = f}

/-- `fixedBy N₁ N₂` is finite when the two sets are: a fixed point of a
projection lies in its image, and `finite_range_compHom` bounds that image. -/
theorem finite_fixedBy {N₁ : Set α} {N₂ : Set β} (hfin₁ : N₁.Finite) (hfin₂ : N₂.Finite) :
    (fixedBy N₁ N₂).Finite := by
  by_cases hN₁ : N₁ ◁ compacts α
  · by_cases hN₂ : N₂ ◁ compacts β
    · refine Set.Finite.subset
        (finite_range_compHom (isProjection_normalHom hN₁) (isProjection_normalHom hN₂)
          (finite_range_normalHom hN₁ hfin₁) (finite_range_normalHom hN₂ hfin₂)) ?_
      rintro f ⟨ha, hb, hfix⟩
      exact ⟨f, hfix⟩
    · refine Set.finite_empty.subset ?_
      rintro f ⟨-, hb, -⟩
      exact absurd hb hN₂
  · refine Set.finite_empty.subset ?_
    rintro f ⟨ha, -, -⟩
    exact absurd ha hN₁

/-- **`K(D → E)` is countable when `D` and `E` are bifinite domains.** Compare
`ScottHom.countable_compacts_scottHom` (`FunctionSpaceCountable.lean:113`), which
needs `[BoundedComplete β]`. -/
theorem countable_compacts_scottHom (h₁ : IsBifinite α) (h₂ : IsBifinite β) :
    (compacts (ScottHom α β)).Countable := by
  have hI : ({S : Set α | S.Finite ∧ S ⊆ compacts α} ×ˢ
      {T : Set β | T.Finite ∧ T ⊆ compacts β}).Countable :=
    (Set.countable_setOf_finite_subset (Domain.countable_compacts (α := α))).prod
      (Set.countable_setOf_finite_subset (Domain.countable_compacts (α := β)))
  have hcov : (⋃ P ∈ ({S : Set α | S.Finite ∧ S ⊆ compacts α} ×ˢ
      {T : Set β | T.Finite ∧ T ⊆ compacts β}), fixedBy P.1 P.2).Countable := by
    refine hI.biUnion ?_
    rintro ⟨N₁, N₂⟩ ⟨⟨hfin₁, -⟩, ⟨hfin₂, -⟩⟩
    exact (finite_fixedBy hfin₁ hfin₂).countable
  refine Set.Countable.mono ?_ hcov
  intro f hf
  obtain ⟨N₁, N₂, hN₁, hN₂, hfin₁, hfin₂, hfix⟩ := exists_normal_fixing h₁ h₂ hf
  exact Set.mem_biUnion
    (show ((N₁, N₂) : Set α × Set β) ∈ _ from ⟨⟨hfin₁, hN₁.subset⟩, ⟨hfin₂, hN₂.subset⟩⟩)
    ⟨hN₁, hN₂, hfix⟩

/-- **`D → E` is a domain when `D` and `E` are bifinite domains.** Compare
`ScottHom.instDomain` (`FunctionSpaceCountable.lean:122`), whose binders are
`[Domain α] [Domain β] [BoundedComplete β]`. `Domain` is a `Prop`-valued class,
so supplying a second proof at a carrier the existing instance does not reach
creates no diamond. -/
theorem domain_scottHom (h₁ : IsBifinite α) (h₂ : IsBifinite β) : Domain (ScottHom α β) :=
  { isAlgebraic_scottHom h₁ h₂ with
    countable_compacts := countable_compacts_scottHom h₁ h₂ }

/-- **`D →⊥ E` is a domain when `D` and `E` are bifinite domains.** Compare
`PRepFun.strictHomDomain`, whose `[BoundedComplete β]` is spent only on
`Domain (ScottHom α β)`; the script below is that theorem's verbatim, with
`domain_scottHom` supplying the ambient domain instead. `PRepFun.isStrict_of_le`
and `PRepFun.val_image_compactsBelow` carry no such binder and are reused. -/
theorem domain_strictHom (h₁ : IsBifinite α) (h₂ : IsBifinite β) : Domain (StrictHom α β) := by
  haveI : Domain (ScottHom α β) := domain_scottHom h₁ h₂
  have halg : IsAlgebraic (StrictHom α β) :=
    { directedOn_compactsBelow := by
        intro f k₁ hk₁ k₂ hk₂
        have hv₁ : (k₁.val : ScottHom α β) ∈ compactsBelow (f.val : ScottHom α β) := by
          rw [← PRepFun.val_image_compactsBelow]; exact ⟨k₁, hk₁, rfl⟩
        have hv₂ : (k₂.val : ScottHom α β) ∈ compactsBelow (f.val : ScottHom α β) := by
          rw [← PRepFun.val_image_compactsBelow]; exact ⟨k₂, hk₂, rfl⟩
        obtain ⟨K, hK, hK₁, hK₂⟩ :=
          IsAlgebraic.directedOn_compactsBelow (f.val : ScottHom α β) _ hv₁ _ hv₂
        exact ⟨⟨K, PRepFun.isStrict_of_le f.2 hK.2⟩,
          ⟨ClosureProperties.isCompactElement_of_isCompactElement_val hK.1, hK.2⟩, hK₁, hK₂⟩
      isLUB_compactsBelow := by
        intro f
        refine ⟨fun k hk => hk.2, fun v hv => ?_⟩
        show (f.val : ScottHom α β) ≤ v.val
        refine (IsAlgebraic.isLUB_compactsBelow (f.val : ScottHom α β)).2 ?_
        rw [← PRepFun.val_image_compactsBelow]
        rintro _ ⟨k, hk, rfl⟩
        exact hv hk }
  refine { halg with countable_compacts := ?_ }
  have hsub : compacts (StrictHom α β) ⊆ Subtype.val ⁻¹' compacts (ScottHom α β) :=
    fun _ hc => ClosureProperties.isCompactElement_val_of_isCompactElement hc
  exact Set.Countable.mono hsub
    ((Domain.countable_compacts (α := ScottHom α β)).preimage Subtype.val_injective)

end Algebraic

/-! ### The bar was not lowered -/

/-- `isAlgebraic_scottHom` implies `FunctionSpaceDomain.lean:121`'s statement. -/
theorem isAlgebraic_scottHom_imp_old [Domain α] [Domain β] [BoundedComplete β]
    (h₁ : IsBifinite α) (h₂ : IsBifinite β) : IsAlgebraic (ScottHom α β) :=
  isAlgebraic_scottHom h₁ h₂

/-- `domain_scottHom` implies `FunctionSpaceCountable.lean:122`'s statement. -/
theorem domain_scottHom_imp_old [Domain α] [Domain β] [BoundedComplete β]
    (h₁ : IsBifinite α) (h₂ : IsBifinite β) : Domain (ScottHom α β) :=
  domain_scottHom h₁ h₂

end ScottDomains.R47.Agent4
