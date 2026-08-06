import ScottDomains.FinitaryProjection

/-!
# `p_N`: the projection determined by a normal subposet

Gunter & Scott, *Semantic Domains*, §3.1, continuing toward Theorem 6:

> Suppose, on the other hand, that `N ◁ K(D)`. Then it is easy to check that the
> function `p_N : D → D` given by `p_N(x) = ⨆{y ∈ N | y ⊑ x}` is a finitary
> projection. Indeed, the correspondence `N ↦ p_N` is inverse to the
> correspondence `p ↦ im(p) ∩ K(D)` …

This file builds `p_N`, shows it is Scott continuous, and shows it is a
projection. Lemma 5 already supplies the other direction of the correspondence
(`p ↦ im(p) ∩ K(D)` lands in the normal subposets of `K(D)`).

## The first thing to check is not in the paper

`N ◁ K(D)` says `N ∩ ↓x` is directed for `x` **in `K(D)`**. The definition of
`p_N` needs it for **every** `x ∈ D`, and that is not immediate: it is where
algebraicity of `D` is spent. Given `a, b ∈ N` below an arbitrary `x`, the
compacts below `x` are directed, so some compact `k ≤ x` dominates both; then
`N ∩ ↓k` is directed because `k ∈ K(D)`, and its witness is below `k ≤ x`.

The paper's "it is easy to check" covers this step; it is the only place the
argument needs `D` to be algebraic.
-/

namespace ScottDomains

open ScottHom

variable {α : Type*} [CompletePartialOrder α] {N : Set α}

/-- `N` contains `⊥`, so `N ∩ ↓x` is never empty. Needs no algebraicity. -/
theorem IsNormalIn.nonempty_inter_Iic (hN : N ◁ compacts α) (x : α) :
    (N ∩ Set.Iic x).Nonempty :=
  ⟨⊥, hN.bot_mem isCompactElement_bot, bot_le⟩

variable [IsAlgebraic α]

/-- `N ∩ ↓x` is directed for **every** `x`, not only compact `x`. This is where
algebraicity of `D` is used: a compact `k ≤ x` dominating `a` and `b` exists, and
`N ∩ ↓k` is directed because `k` is compact. -/
theorem IsNormalIn.directedOn_inter_Iic (hN : N ◁ compacts α) (x : α) :
    DirectedOn (· ≤ ·) (N ∩ Set.Iic x) := by
  rintro a ⟨haN, hax⟩ b ⟨hbN, hbx⟩
  obtain ⟨k, ⟨hkK, hkx⟩, hak, hbk⟩ :=
    IsAlgebraic.directedOn_compactsBelow x a ⟨hN.subset haN, hax⟩ b ⟨hN.subset hbN, hbx⟩
  obtain ⟨c, ⟨hcN, hck⟩, hac, hbc⟩ := hN.directedOn hkK a ⟨haN, hak⟩ b ⟨hbN, hbk⟩
  exact ⟨c, ⟨hcN, le_trans hck hkx⟩, hac, hbc⟩

/-- `p_N(x) = ⨆{y ∈ N | y ⊑ x}`. -/
noncomputable def normalFun (N : Set α) (x : α) : α := sSup (N ∩ Set.Iic x)

theorem normalFun_le (hN : N ◁ compacts α) (x : α) : normalFun N x ≤ x :=
  (hN.directedOn_inter_Iic x).sSup_le fun _ hy => hy.2

theorem le_normalFun (hN : N ◁ compacts α) {y x : α} (hyN : y ∈ N) (hyx : y ≤ x) :
    y ≤ normalFun N x :=
  (hN.directedOn_inter_Iic x).le_sSup ⟨hyN, hyx⟩

theorem monotone_normalFun (hN : N ◁ compacts α) : Monotone (normalFun N) := by
  intro x y hxy
  refine (hN.directedOn_inter_Iic x).sSup_le ?_
  rintro z ⟨hzN, hzx⟩
  exact le_normalFun hN hzN (hzx.trans hxy)

/-- `p_N` is Scott continuous. The least-upper-bound half is where `N ⊆ K(D)`
does its work: a member `y ∈ N` below `⨆s` is compact, so it is already below
some `x ∈ s`, and hence below `p_N x`. -/
theorem scottContinuous_normalFun (hN : N ◁ compacts α) :
    ScottContinuous (normalFun N) := by
  intro s hne hs a ha
  refine ⟨?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact monotone_normalFun hN (ha.1 hx)
  · intro v hv
    refine (hN.directedOn_inter_Iic a).sSup_le ?_
    rintro y ⟨hyN, hya⟩
    obtain ⟨x, hx, hyx⟩ := hN.subset hyN s a hne hs ha hya
    exact (le_normalFun hN hyN hyx).trans (hv ⟨x, hx, rfl⟩)

/-- `p_N` as an element of the function space. -/
noncomputable def normalHom (hN : N ◁ compacts α) : ScottHom α α :=
  ⟨normalFun N, scottContinuous_normalFun hN⟩

@[simp] theorem coe_normalHom (hN : N ◁ compacts α) : ⇑(normalHom hN) = normalFun N := rfl

/-- **`p_N` is a projection.** Idempotence in the `≥` direction is the only step
with content: every `y ∈ N ∩ ↓x` is below `p_N x`, hence lies in `N ∩ ↓(p_N x)`,
hence is below `p_N (p_N x)`. -/
theorem isProjection_normalHom (hN : N ◁ compacts α) : IsProjection (normalHom hN) := by
  refine ⟨fun x => le_antisymm ?_ ?_, fun x => normalFun_le hN x⟩
  · exact monotone_normalFun hN (normalFun_le hN x)
  · refine (hN.directedOn_inter_Iic x).sSup_le ?_
    rintro y ⟨hyN, hyx⟩
    exact le_normalFun hN hyN (le_normalFun hN hyN hyx)

/-- `p_N` fixes every member of `N`, since such a `y` is the greatest element of
`N ∩ ↓y`. -/
theorem normalFun_of_mem (hN : N ◁ compacts α) {y : α} (hy : y ∈ N) : normalFun N y = y :=
  le_antisymm (normalFun_le hN y) (le_normalFun hN hy le_rfl)

/-- **One half of Theorem 6's correspondence:** `im(p_N) ∩ K(D) = N`.

The inclusion `⊇` is `normalFun_of_mem`. For `⊆`, a compact `z` in the image
satisfies `z = ⨆(N ∩ ↓z)`, and compactness pulls the supremum back into the set:
some `y ∈ N` has `z ≤ y ≤ z`. -/
theorem range_normalHom_inter_compacts (hN : N ◁ compacts α) :
    Set.range ⇑(normalHom hN) ∩ compacts α = N := by
  ext z
  constructor
  · rintro ⟨hzR, hzK⟩
    have hfix : normalFun N z = z := by
      have := (isProjection_normalHom hN).apply_of_mem_range hzR
      simpa [coe_normalHom] using this
    have hlub : IsLUB (N ∩ Set.Iic z) z := by
      have h := (hN.directedOn_inter_Iic z).isLUB_sSup
      rwa [show sSup (N ∩ Set.Iic z) = z from hfix] at h
    obtain ⟨y, ⟨hyN, hyz⟩, hzy⟩ :=
      hzK (N ∩ Set.Iic z) z (hN.nonempty_inter_Iic z) (hN.directedOn_inter_Iic z) hlub le_rfl
    rwa [le_antisymm hzy hyz]
  · intro hz
    exact ⟨⟨z, normalFun_of_mem hN hz⟩, hN.subset hz⟩

/-- The correspondence is monotone: a larger normal subposet gives a larger
projection, pointwise. -/
theorem normalHom_mono {N' : Set α} (hN : N ◁ compacts α) (hN' : N' ◁ compacts α)
    (h : N ⊆ N') : normalHom hN ≤ normalHom hN' := by
  intro x
  refine (hN.directedOn_inter_Iic x).sSup_le ?_
  rintro y ⟨hyN, hyx⟩
  exact le_normalFun hN' (h hyN) hyx

omit [IsAlgebraic α] in
/-- The image of a smaller projection sits inside the image of a larger one: if
`p ≤ q` are projections and `p y = y`, then `y ≤ q y ≤ y`. -/
theorem IsProjection.range_mono {p q : ScottHom α α} (hp : IsProjection p)
    (hq : IsProjection q) (hpq : p ≤ q) : Set.range ⇑p ⊆ Set.range ⇑q := by
  rintro y ⟨x, rfl⟩
  exact ⟨p x, le_antisymm (hq.le _) (le_trans (le_of_eq (hp.idem x).symm) (hpq (p x)))⟩

end ScottDomains
