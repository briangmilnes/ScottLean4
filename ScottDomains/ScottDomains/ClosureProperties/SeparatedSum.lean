import ScottDomains.Skeleton.Lemma10
import ScottDomains.Skeleton.Lemma17
import ScottDomains.Skeleton.Sum
import ScottDomains.Isomorphism.Copair
import ScottDomains.Isomorphism.Lift

/-!
# The separated sum `D + E`, and its two closure conjuncts

Gunter & Scott, *Semantic Domains*, §4.4, quoted from the source PDF:

> Given cpo's `D` and `E`, we define the **separated sum** `D + E` to be the cpo
> `D⊥ ⊕ E⊥`.

`+` is therefore a *defined* operator, not a primitive one: it is the coalesced
sum of the two lifts. This is what the Lemma 10 and Lemma 17 lists mean when they
name `D + E` and `D ⊕ E` as separate conjuncts —

> **Lemma 10** If `D` and `E` are bounded complete domains then so are the cpo's
> `D → E`, `D →⊥ E`, `D × E`, `D ⊗ E`, `D + E`, `D ⊕ E`, `D⊥`.

> **Lemma 17** If `D` and `E` are bifinite domains, then so are the cpo's
> `D → E`, `D →⊥ E`, `D × E`, `D ⊗ E`, `D + E`, `D ⊕ E`, `D⊥`, `D♮`, `D♯`, `D♭`.

Both `+` conjuncts are then compositions of conjuncts already proved: the lift
conjunct of the same lemma, followed by its `⊕` conjunct. The one piece of
machinery that was missing is `Domain (D⊥)` — the `⊕` conjuncts are stated for
*domains*, and `Lift.lean` supplied `D⊥` only as a cpo. That is what the first
section proves.

## What `Domain (D⊥)` costs

`K(D⊥) = {⊥} ∪ ↑K(D)` (`compactsBelow_coe`, on the strength of r0027's
`isCompactElement_coe_iff`), so countability of the basis is countability of
`K(D)` plus one point, and algebraicity of `D⊥` is algebraicity of `D` with the
adjoined bottom carried through each of the four cases of the directedness
argument. No hypothesis beyond `Domain D` is used; in particular `D⊥` is a domain
whether or not `D` is bounded complete.
-/

namespace ScottDomains.ClosureProperties

open ScottDomains

variable {α β : Type*} [CompletePartialOrder α] [CompletePartialOrder β]

/-! ### `K(D⊥)` and `D⊥` as a domain -/

/-- Below the adjoined bottom there is nothing but the adjoined bottom. -/
theorem compactsBelow_bot_withBot : compactsBelow (⊥ : WithBot α) = {⊥} := by
  ext z
  constructor
  · rintro ⟨-, hz⟩
    exact le_bot_iff.mp hz
  · rintro rfl
    exact ⟨isCompactElement_bot, le_rfl⟩

/-- **`K(D⊥) ∩ ↓↑a = {⊥} ∪ ↑(K(D) ∩ ↓a)`.** The adjoined bottom is compact for
free; a coercion is compact exactly when its base point is
(`isCompactElement_coe_iff`, r0027), and the coercion is an order embedding. -/
theorem compactsBelow_coe (a : α) :
    compactsBelow (↑a : WithBot α)
      = insert ⊥ ((fun k : α => (↑k : WithBot α)) '' compactsBelow a) := by
  ext z
  constructor
  · rintro ⟨hz, hza⟩
    induction z using WithBot.recBotCoe with
    | bot => exact Set.mem_insert _ _
    | coe k =>
      exact Set.mem_insert_of_mem _
        ⟨k, ⟨isCompactElement_coe_iff.mp hz, WithBot.coe_le_coe.mp hza⟩, rfl⟩
  · rintro (rfl | ⟨k, hk, rfl⟩)
    · exact ⟨isCompactElement_bot, bot_le⟩
    · exact ⟨isCompactElement_coe_iff.mpr hk.1, WithBot.coe_le_coe.mpr hk.2⟩

/-- **`D⊥` is algebraic when `D` is.** Directedness has four cases, three of
which are discharged by `bot_le`; the least-upper-bound conjunct turns on the
observation that an upper bound of `compactsBelow ↑a` cannot be the adjoined
bottom, because `↑⊥` is one of the elements it must dominate. -/
instance liftIsAlgebraic [IsAlgebraic α] : IsAlgebraic (WithBot α) where
  directedOn_compactsBelow z := by
    induction z using WithBot.recBotCoe with
    | bot =>
      rw [compactsBelow_bot_withBot]
      rintro p rfl q rfl
      exact ⟨⊥, rfl, le_rfl, le_rfl⟩
    | coe a =>
      rw [compactsBelow_coe]
      rintro p (rfl | ⟨k₁, hk₁, rfl⟩) q (rfl | ⟨k₂, hk₂, rfl⟩)
      · exact ⟨⊥, Set.mem_insert _ _, le_rfl, le_rfl⟩
      · exact ⟨↑k₂, Set.mem_insert_of_mem _ ⟨k₂, hk₂, rfl⟩, bot_le, le_rfl⟩
      · exact ⟨↑k₁, Set.mem_insert_of_mem _ ⟨k₁, hk₁, rfl⟩, le_rfl, bot_le⟩
      · obtain ⟨c, hc, h₁, h₂⟩ := IsAlgebraic.directedOn_compactsBelow a k₁ hk₁ k₂ hk₂
        exact ⟨↑c, Set.mem_insert_of_mem _ ⟨c, hc, rfl⟩,
          WithBot.coe_le_coe.mpr h₁, WithBot.coe_le_coe.mpr h₂⟩
  isLUB_compactsBelow z := by
    induction z using WithBot.recBotCoe with
    | bot =>
      rw [compactsBelow_bot_withBot]
      exact isLUB_singleton
    | coe a =>
      rw [compactsBelow_coe]
      constructor
      · rintro p (rfl | ⟨k, hk, rfl⟩)
        · exact bot_le
        · exact WithBot.coe_le_coe.mpr hk.2
      · intro v hv
        induction v using WithBot.recBotCoe with
        | bot =>
          exact absurd (hv (Set.mem_insert_of_mem _ ⟨⊥, bot_mem_compactsBelow a, rfl⟩))
            (WithBot.not_coe_le_bot _)
        | coe b =>
          refine WithBot.coe_le_coe.mpr ((IsAlgebraic.isLUB_compactsBelow a).2 ?_)
          intro k hk
          exact WithBot.coe_le_coe.mp (hv (Set.mem_insert_of_mem _ ⟨k, hk, rfl⟩))

/-- `K(D⊥) ⊆ {⊥} ∪ ↑K(D)`, the inclusion countability needs. -/
theorem compacts_withBot_subset :
    compacts (WithBot α) ⊆ insert ⊥ ((fun k : α => (↑k : WithBot α)) '' compacts α) := by
  intro z hz
  induction z using WithBot.recBotCoe with
  | bot => exact Set.mem_insert _ _
  | coe k => exact Set.mem_insert_of_mem _ ⟨k, isCompactElement_coe_iff.mp hz, rfl⟩

/-- **`D⊥` is a domain when `D` is.** Algebraicity is `liftIsAlgebraic`;
countability of `K(D⊥)` is countability of `K(D)` under a single injection, plus
the adjoined bottom. -/
instance liftDomain [Domain α] : Domain (WithBot α) where
  __ := liftIsAlgebraic
  countable_compacts :=
    Set.Countable.mono compacts_withBot_subset
      (((Domain.countable_compacts (α := α)).image _).insert ⊥)

/-! ### The separated sum -/

/-- The **separated sum** `D + E = D⊥ ⊕ E⊥` (Gunter & Scott §4.4). An `abbrev`,
because the paper's definition *is* an equation between cpo's: `D + E` carries
exactly the order, the suprema and the `Domain` structure that `D⊥ ⊕ E⊥` has.

Unlike the coalesced sum, `+` keeps the two bottoms apart: `↑⊥_D` and `↑⊥_E` are
distinct non-bottom points of `D⊥` and `E⊥`, so the coalescing identifies only
the two *adjoined* bottoms, and the result is the disjoint union of `D` and `E`
with one new bottom below both. -/
abbrev SeparatedSum (α β : Type*) [CompletePartialOrder α] [CompletePartialOrder β] :=
  CoalescedSum (WithBot α) (WithBot β)

/-- **Lemma 10, `D + E`.** The seventh and last conjunct: bounded completeness of
`D⊥` and of `E⊥` is the lift conjunct `lemma_10_lift`, and the coalesced sum of two
bounded complete domains is bounded complete by `lemma_10_sum`. `liftDomain` is what
lets `lemma_10_sum` be applied at `D⊥` and `E⊥` — it demands *domains*, not merely
cpo's. -/
theorem lemma_10_separated [Domain α] [BoundedComplete α] [Domain β] [BoundedComplete β] :
    BoundedComplete (SeparatedSum α β) := by
  haveI : BoundedComplete (WithBot α) := lemma_10_lift
  haveI : BoundedComplete (WithBot β) := lemma_10_lift
  exact lemma_10_sum

/-- **Lemma 17, `D + E`.** The same composition at the bifinite conjuncts:
`lemma_17_lift` then `lemma_17_sum`. No bounded completeness is needed anywhere — this
is the operator's whole point in §6, where `E` is not assumed bounded
complete. -/
theorem lemma_17_separated [Domain α] [Domain β] (h₁ : IsBifinite α) (h₂ : IsBifinite β) :
    IsBifinite (SeparatedSum α β) :=
  lemma_17_sum (lemma_17_lift h₁) (lemma_17_lift h₂)

/-! ### §4.4's universal property for `+` -/

section Universal

variable {γ : Type*} [CompletePartialOrder γ]

/-- Product congruence for order isomorphisms. Mathlib has `Equiv.prodCongr` but
**no `OrderIso.prodCongr`** — grepped across `Mathlib/Order/` — and without it
`e₁.prodCongr e₂` silently resolves through the coercion to `Equiv`, losing the
order. The product order is componentwise, so the content is `Prod.mk_le_mk`
plus the two `map_rel_iff`s. -/
def orderIsoProdCongr {α₁ α₂ β₁ β₂ : Type*} [Preorder α₁] [Preorder α₂]
    [Preorder β₁] [Preorder β₂] (e₁ : α₁ ≃o β₁) (e₂ : α₂ ≃o β₂) :
    α₁ × α₂ ≃o β₁ × β₂ where
  toEquiv := e₁.toEquiv.prodCongr e₂.toEquiv
  map_rel_iff' := by
    intro a b
    simp [Prod.le_def]

/-- **The universal property of the separated sum** (Gunter & Scott §4.4): a
*strict* continuous map out of `D + E` is exactly a pair of *continuous* maps out
of `D` and `E`, with `h = [f†, g†]` the unique one.

`+` differs from `⊕` precisely here. For the coalesced sum the correspondence is
with a pair of **strict** maps (`coalescedSumCopair`); adjoining a fresh bottom
to each summand first is what relaxes each factor to an arbitrary continuous map,
by `liftStrictHomIso : StrictHom D⊥ E ≃o ScottHom D E`. So this is the composite
of two isomorphisms the development already had, and nothing new is proved —
r0040 recorded it as a paper property with no Lean statement, and the gap was
that the composite was never declared.

Strictness of `h` is not an extra hypothesis but part of the correspondence: it
is what makes the map out of the sum determined by its two restrictions, since
the sum's bottom is not in the image of either injection. The paper also remarks
that `h` need not be the only *continuous* completion — that claim is separate
and is not stated here. -/
noncomputable def separatedSumCopair :
    StrictHom (SeparatedSum α β) γ ≃o ScottHom α γ × ScottHom β γ :=
  (Isomorphism.coalescedSumCopair).trans
    (orderIsoProdCongr Isomorphism.liftStrictHomIso Isomorphism.liftStrictHomIso)

end Universal

end ScottDomains.ClosureProperties
