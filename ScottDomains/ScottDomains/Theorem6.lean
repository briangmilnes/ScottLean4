import ScottDomains.NormalProjection

/-!
# Theorem 6

Gunter & Scott, *Semantic Domains*, §3.1:

> **Theorem 6** For any domain `D` there is an isomorphism between the cpo of
> normal substructures of `K(D)` and the poset `Fp(D)` of finitary projections
> on `D`.

The isomorphism is `N ↦ p_N` with inverse `p ↦ im(p) ∩ K(D)`. r0014 (Lemma 5)
showed the second map lands in the normal substructures; r0015 built `p_N`,
showed it is a projection, and proved `im(p_N) ∩ K(D) = N`. This file supplies
what remains: that `p_N` is **finitary**, that `p_{im(p) ∩ K(D)} = p`, and the
assembled statement.

## The shape of the remaining work

Both remaining halves are transfers across the subtype `↥(im p)`. The two
directions of that transfer are `IsProjection.isLUB_val_image` (r0014) and its
converse `isLUB_of_isLUB_val_image` here; with the identification
`val '' (compactsBelow y) = N ∩ ↓y` they turn statements about `im(p_N)` into
statements about `N` in `D`, where r0015's lemmas apply directly.
-/

namespace ScottDomains

open ScottHom

variable {α : Type*} [CompletePartialOrder α]

/-- Converse of `IsProjection.isLUB_val_image`: a least upper bound in `D` of a
set drawn from `im(p)` is a least upper bound in `im(p)`. -/
theorem isLUB_of_isLUB_val_image {p : ScottHom α α} {s : Set ↥(Set.range ⇑p)}
    {u : ↥(Set.range ⇑p)} (h : IsLUB (Subtype.val '' s) u.val) : IsLUB s u := by
  constructor
  · intro a ha
    exact h.1 ⟨a, ha, rfl⟩
  · intro v hv
    refine h.2 ?_
    rintro _ ⟨a, ha, rfl⟩
    exact hv ha

section Finitary

variable [IsAlgebraic α] {N : Set α} (hN : N ◁ compacts α)

/-- Under `val`, the compact approximants of `y` in `im(p_N)` are exactly
`N ∩ ↓y`. Lemma 5's first sentence identifies the compacts, and r0015's
`im(p_N) ∩ K(D) = N` identifies which elements those are. -/
theorem val_image_compactsBelow (y : ↥(Set.range ⇑(normalHom hN))) :
    Subtype.val '' (compactsBelow y) = N ∩ Set.Iic y.val := by
  have hproj := isProjection_normalHom hN
  ext z
  constructor
  · rintro ⟨c, ⟨hcK, hcy⟩, rfl⟩
    refine ⟨?_, hcy⟩
    have hmem : c.val ∈ Set.range ⇑(normalHom hN) ∩ compacts α :=
      ⟨c.2, hproj.isCompactElement_iff.mp hcK⟩
    rwa [range_normalHom_inter_compacts hN] at hmem
  · rintro ⟨hzN, hzy⟩
    have hz : z ∈ Set.range ⇑(normalHom hN) ∩ compacts α := by
      rw [range_normalHom_inter_compacts hN]; exact hzN
    exact ⟨⟨z, hz.1⟩, ⟨hproj.isCompactElement_iff.mpr hz.2, hzy⟩, rfl⟩

/-- `im(p_N)` is algebraic: every `y` in it satisfies `y = p_N y = ⨆(N ∩ ↓y)`,
and `N ∩ ↓y` is exactly the set of compact approximants of `y`. -/
theorem isAlgebraic_range_normalHom :
    @IsAlgebraic _ (IsProjection.rangeCompletePartialOrder (isProjection_normalHom hN)) := by
  letI : CompletePartialOrder ↥(Set.range ⇑(normalHom hN)) :=
    IsProjection.rangeCompletePartialOrder (isProjection_normalHom hN)
  constructor
  case directedOn_compactsBelow =>
    intro y a ha b hb
    have ha' : a.val ∈ N ∩ Set.Iic y.val := by
      rw [← val_image_compactsBelow hN y]; exact ⟨a, ha, rfl⟩
    have hb' : b.val ∈ N ∩ Set.Iic y.val := by
      rw [← val_image_compactsBelow hN y]; exact ⟨b, hb, rfl⟩
    obtain ⟨c, hc, hac, hbc⟩ := hN.directedOn_inter_Iic y.val a.val ha' b.val hb'
    have hcmem : c ∈ Subtype.val '' (compactsBelow y) := by
      rw [val_image_compactsBelow hN y]; exact hc
    obtain ⟨C, hC, rfl⟩ := hcmem
    exact ⟨C, hC, hac, hbc⟩
  case isLUB_compactsBelow =>
    intro y
    refine isLUB_of_isLUB_val_image ?_
    rw [val_image_compactsBelow hN y]
    have hfix : normalFun N y.val = y.val := by
      have := (isProjection_normalHom hN).apply_of_mem_range y.2
      simpa [coe_normalHom] using this
    have h := (hN.directedOn_inter_Iic y.val).isLUB_sSup
    rwa [show sSup (N ∩ Set.Iic y.val) = y.val from hfix] at h

end Finitary

section CountableBasis

variable [IsAlgebraic α] {N : Set α} (hN : N ◁ compacts α)

/-- Every compact element of `im(p_N)` lies in `N`. -/
theorem val_mem_of_isCompactElement {c : ↥(Set.range ⇑(normalHom hN))}
    (hc : IsCompactElement c) : c.val ∈ N := by
  have hmem : c.val ∈ Set.range ⇑(normalHom hN) ∩ compacts α :=
    ⟨c.2, (isProjection_normalHom hN).isCompactElement_iff.mp hc⟩
  rwa [range_normalHom_inter_compacts hN] at hmem

end CountableBasis

section Domain

variable [Domain α] {N : Set α} (hN : N ◁ compacts α)

/-- The basis of `im(p_N)` is `N`, which is countable because `K(D)` is. -/
theorem countable_compacts_range_normalHom :
    (compacts ↥(Set.range ⇑(normalHom hN))).Countable := by
  refine Set.countable_of_injective_of_countable_image Subtype.val_injective.injOn ?_
  refine Set.Countable.mono ?_ (Domain.countable_compacts (α := α))
  rintro _ ⟨c, hc, rfl⟩
  exact hN.subset (val_mem_of_isCompactElement hN hc)

/-- **`p_N` is a finitary projection.** -/
theorem isFinitaryProjection_normalHom : IsFinitaryProjection (normalHom hN) := by
  refine ⟨isProjection_normalHom hN, ?_⟩
  letI : CompletePartialOrder ↥(Set.range ⇑(normalHom hN)) :=
    IsProjection.rangeCompletePartialOrder (isProjection_normalHom hN)
  exact { __ := isAlgebraic_range_normalHom hN
          countable_compacts := countable_compacts_range_normalHom hN }

end Domain

section Inverse

variable [IsAlgebraic α] {p : ScottHom α α}

/-- **The reverse identity:** `p_{im(p) ∩ K(D)} = p` for a finitary projection.

`≤` is immediate: a member of `im(p)` below `x` is `p` of itself, hence below
`p x`. `≥` is where finitary is spent: `p x`, viewed in `im(p)`, is the least
upper bound of its compact approximants, and those are exactly the members of
`im(p) ∩ K(D)` below `p x ≤ x`. -/
theorem normalFun_range_inter_compacts (hp : IsFinitaryProjection p) (x : α) :
    normalFun (Set.range ⇑p ∩ compacts α) x = p x := by
  have hproj := hp.isProjection
  have hN := hp.isNormalIn_compacts
  letI : CompletePartialOrder ↥(Set.range ⇑p) :=
    IsProjection.rangeCompletePartialOrder hproj
  haveI : Domain ↥(Set.range ⇑p) := hp.domain
  refine le_antisymm ((hN.directedOn_inter_Iic x).sSup_le ?_) ?_
  · rintro y ⟨⟨hyR, _⟩, hyx⟩
    calc y = p y := (hproj.apply_of_mem_range hyR).symm
      _ ≤ p x := p.monotone hyx
  · -- `p x` is the least upper bound of its compact approximants in `im(p)`.
    have hlub := IsAlgebraic.isLUB_compactsBelow (⟨p x, Set.mem_range_self x⟩ :
      ↥(Set.range ⇑p))
    have hval := hproj.isLUB_val_image hlub
    refine hval.2 ?_
    rintro _ ⟨c, ⟨hcK, hcx⟩, rfl⟩
    refine (hN.directedOn_inter_Iic x).le_sSup ⟨⟨c.2, hproj.isCompactElement_iff.mp hcK⟩, ?_⟩
    exact le_trans hcx (hproj.le x)

end Inverse

section Theorem6Section

variable [Domain α]

/-- **Theorem 6.** For a domain `D`, the normal substructures of `K(D)` and the
finitary projections on `D` correspond, by `N ↦ p_N` and `p ↦ im(p) ∩ K(D)`.

Recorded as the five facts that constitute the isomorphism: each map lands in the
other's domain, the two round trips are identities, and both maps are monotone.
Stated this way rather than as a bundled `OrderIso` between subtypes, for the
same reason Lemma 4.4 was: it is the form the later results cite. -/
theorem theorem_6 :
    (∀ {N : Set α} (hN : N ◁ compacts α),
        IsFinitaryProjection (normalHom hN) ∧
        Set.range ⇑(normalHom hN) ∩ compacts α = N) ∧
    (∀ {p : ScottHom α α} (_hp : IsFinitaryProjection p),
        (Set.range ⇑p ∩ compacts α) ◁ compacts α ∧
        ∀ x, normalFun (Set.range ⇑p ∩ compacts α) x = p x) ∧
    (∀ {N N' : Set α} (hN : N ◁ compacts α) (hN' : N' ◁ compacts α),
        N ⊆ N' → normalHom hN ≤ normalHom hN') ∧
    (∀ {p q : ScottHom α α}, IsProjection p → IsProjection q → p ≤ q →
        Set.range ⇑p ⊆ Set.range ⇑q) := by
  refine ⟨fun hN => ⟨isFinitaryProjection_normalHom hN, range_normalHom_inter_compacts hN⟩,
    fun hp => ⟨hp.isNormalIn_compacts, normalFun_range_inter_compacts hp⟩,
    fun hN hN' h => normalHom_mono hN hN' h,
    fun hp hq hpq => IsProjection.range_mono hp hq hpq⟩

alias theorem6 := theorem_6

end Theorem6Section

end ScottDomains
