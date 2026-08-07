import ScottDomains.Bifinite
import ScottDomains.Lift
import ScottDomains.Product
import ScottDomains.FunctionSpaceCountable
-- `Set.Finite.prod`, for the rectangle `N₁ ×ˢ N₂` used in the product conjunct.
import Mathlib.Data.Finite.Prod

/-!
# Lemma 17: bifiniteness is closed under the operators

Gunter & Scott, *Semantic Domains*, §6.2:

> **Lemma 17** `D, E` bifinite ⟹ `→, ×, ⊗, +, ()⊥` bifinite (incl. function
> space).

The function-space conjunct is the substantive one: §6's whole point is that
bifiniteness, unlike bounded completeness, is preserved by `→` — Theorem 7 needed
bounded completeness of `E` to make `D → E` a domain, and §6 exists because that
hypothesis is not always available.

**Owned by agent3.** No other file's declarations are edited when these are
proved.
-/

namespace ScottDomains

variable {α β : Type*} [CompletePartialOrder α] [CompletePartialOrder β]

/-! ### The basis of a product

`K(D × E) = K(D) × K(E)`. Both directions are needed: the forward one to push a
finite `u ⊆ K(D × E)` down to each coordinate, the backward one to certify the
rectangle `N₁ × N₂` built from the two coordinate witnesses. -/

/-- A directed set of `α`, paired with a fixed `b`, is directed in `α × β`. -/
theorem directedOn_image_mk_right {s : Set α} (hs : DirectedOn (· ≤ ·) s) (b : β) :
    DirectedOn (· ≤ ·) ((fun a => (a, b)) '' s) := by
  rintro _ ⟨a₁, h₁, rfl⟩ _ ⟨a₂, h₂, rfl⟩
  obtain ⟨c, hc, hc₁, hc₂⟩ := hs a₁ h₁ a₂ h₂
  exact ⟨(c, b), ⟨c, hc, rfl⟩, ⟨hc₁, le_rfl⟩, ⟨hc₂, le_rfl⟩⟩

/-- The symmetric statement in the second coordinate. -/
theorem directedOn_image_mk_left {s : Set β} (hs : DirectedOn (· ≤ ·) s) (a : α) :
    DirectedOn (· ≤ ·) ((fun b => (a, b)) '' s) := by
  rintro _ ⟨b₁, h₁, rfl⟩ _ ⟨b₂, h₂, rfl⟩
  obtain ⟨c, hc, hc₁, hc₂⟩ := hs b₁ h₁ b₂ h₂
  exact ⟨(a, c), ⟨c, hc, rfl⟩, ⟨le_rfl, hc₁⟩, ⟨le_rfl, hc₂⟩⟩

theorem isLUB_image_mk_right {s : Set α} (hne : s.Nonempty) {u : α} (hu : IsLUB s u) (b : β) :
    IsLUB ((fun a => (a, b)) '' s) (u, b) := by
  rw [isLUB_prod]
  refine ⟨?_, ?_⟩
  · simpa [Set.image_image] using hu
  · simp [Set.image_image, hne.image_const]

theorem isLUB_image_mk_left {s : Set β} (hne : s.Nonempty) {u : β} (hu : IsLUB s u) (a : α) :
    IsLUB ((fun b => (a, b)) '' s) (a, u) := by
  rw [isLUB_prod]
  refine ⟨?_, ?_⟩
  · simp [Set.image_image, hne.image_const]
  · simpa [Set.image_image] using hu

/-- **`K(D × E) = K(D) × K(E)`.** Forward: test a coordinate's directed set by
pairing it with the other coordinate of `x`, which leaves the least upper bound in
that coordinate untouched. Backward: compactness in each coordinate produces two
members of `s`, and directedness of `s` merges them. -/
theorem isCompactElement_prod_iff {x : α × β} :
    IsCompactElement x ↔ IsCompactElement x.1 ∧ IsCompactElement x.2 := by
  constructor
  · intro hx
    refine ⟨?_, ?_⟩
    · intro s u hne hs hlub hxu
      obtain ⟨_, ⟨a, ha, rfl⟩, hle⟩ :=
        hx ((fun a => (a, x.2)) '' s) (u, x.2) (hne.image _)
          (directedOn_image_mk_right hs x.2) (isLUB_image_mk_right hne hlub x.2)
          ⟨hxu, le_rfl⟩
      exact ⟨a, ha, hle.1⟩
    · intro s u hne hs hlub hxu
      obtain ⟨_, ⟨b, hb, rfl⟩, hle⟩ :=
        hx ((fun b => (x.1, b)) '' s) (x.1, u) (hne.image _)
          (directedOn_image_mk_left hs x.1) (isLUB_image_mk_left hne hlub x.1)
          ⟨le_rfl, hxu⟩
      exact ⟨b, hb, hle.2⟩
  · rintro ⟨h₁, h₂⟩ s u hne hs hlub hxu
    rw [isLUB_prod] at hlub
    obtain ⟨_, ⟨p, hp, rfl⟩, hp₁⟩ :=
      h₁ _ u.1 (hne.image _) (directedOn_fst_image hs) hlub.1 hxu.1
    obtain ⟨_, ⟨q, hq, rfl⟩, hq₂⟩ :=
      h₂ _ u.2 (hne.image _) (directedOn_snd_image hs) hlub.2 hxu.2
    obtain ⟨c, hc, hpc, hqc⟩ := hs p hp q hq
    exact ⟨c, hc, hp₁.trans hpc.1, hq₂.trans hqc.2⟩

/-- **Lemma 17, product conjunct.** Take the two coordinate projections of the
finite `u`, expand each to a finite normal subposet, and use the rectangle. Since
`N ∩ ↓x` splits as `(N₁ ∩ ↓x.1) × (N₂ ∩ ↓x.2)`, directedness is coordinatewise. -/
theorem lem17_prod [Domain α] [Domain β] (_h₁ : IsBifinite α) (_h₂ : IsBifinite β) :
    IsBifinite (α × β) := by
  intro u hu husub
  have hfst : Prod.fst '' u ⊆ compacts α := by
    rintro _ ⟨p, hp, rfl⟩
    exact (isCompactElement_prod_iff.mp (husub hp)).1
  have hsnd : Prod.snd '' u ⊆ compacts β := by
    rintro _ ⟨p, hp, rfl⟩
    exact (isCompactElement_prod_iff.mp (husub hp)).2
  obtain ⟨N₁, hfin₁, hnorm₁, hsub₁⟩ := _h₁ _ (hu.image _) hfst
  obtain ⟨N₂, hfin₂, hnorm₂, hsub₂⟩ := _h₂ _ (hu.image _) hsnd
  refine ⟨N₁ ×ˢ N₂, Set.Finite.prod hfin₁ hfin₂, ⟨?_, ?_⟩, ?_⟩
  · rintro ⟨a, b⟩ ⟨ha, hb⟩
    exact isCompactElement_prod_iff.mpr ⟨hnorm₁.subset ha, hnorm₂.subset hb⟩
  · rintro x hx
    obtain ⟨hx₁, hx₂⟩ := isCompactElement_prod_iff.mp hx
    refine ⟨?_, ?_⟩
    · obtain ⟨a, ha, hax⟩ := hnorm₁.nonempty hx₁
      obtain ⟨b, hb, hbx⟩ := hnorm₂.nonempty hx₂
      exact ⟨(a, b), ⟨ha, hb⟩, hax, hbx⟩
    · rintro p ⟨⟨hp₁, hp₂⟩, hpx⟩ q ⟨⟨hq₁, hq₂⟩, hqx⟩
      obtain ⟨a, ⟨ha, hax⟩, hpa, hqa⟩ :=
        hnorm₁.directedOn hx₁ p.1 ⟨hp₁, hpx.1⟩ q.1 ⟨hq₁, hqx.1⟩
      obtain ⟨b, ⟨hb, hbx⟩, hpb, hqb⟩ :=
        hnorm₂.directedOn hx₂ p.2 ⟨hp₂, hpx.2⟩ q.2 ⟨hq₂, hqx.2⟩
      exact ⟨(a, b), ⟨⟨ha, hb⟩, hax, hbx⟩, ⟨hpa, hpb⟩, ⟨hqa, hqb⟩⟩
  · intro p hp
    exact ⟨hsub₁ ⟨p, hp, rfl⟩, hsub₂ ⟨p, hp, rfl⟩⟩

/-! ### The basis of a lift

`K(D⊥) = {⊥} ∪ ↑K(D)`. The adjoined bottom is compact for free; a coercion `↑a` is
compact exactly when `a` is, and the transfer in both directions is
`isLUB_liftBase` together with the fact that a coerced element is never below the
adjoined bottom. -/

/-- A least upper bound that is a coercion restricts to a least upper bound of the
base. An upper bound `c` of the base gives the upper bound `↑c` of `s`, because
every non-`⊥` member of `s` is a coercion of a base element. -/
theorem isLUB_liftBase {s : Set (WithBot α)} {b : α} (h : IsLUB s (↑b : WithBot α)) :
    IsLUB (liftBase s) b := by
  constructor
  · intro x hx
    exact WithBot.coe_le_coe.mp (h.1 (coe_mem_of_mem_liftBase hx))
  · intro c hc
    refine WithBot.coe_le_coe.mp (h.2 ?_)
    intro y hy
    induction y using WithBot.recBotCoe with
    | bot => exact bot_le
    | coe x => exact WithBot.coe_le_coe.mpr (hc (show x ∈ liftBase s from hy))

/-- If the least upper bound of `s` is a coercion, the base of `s` is nonempty:
otherwise `s ⊆ {⊥}` and `⊥` would be an upper bound above a coercion. -/
theorem liftBase_nonempty_of_isLUB {s : Set (WithBot α)} {b : α}
    (h : IsLUB s (↑b : WithBot α)) : (liftBase s).Nonempty := by
  rcases Set.eq_empty_or_nonempty (liftBase s) with hemp | hne
  · refine absurd (h.2 (fun y hy => ?_)) (WithBot.not_coe_le_bot b)
    induction y using WithBot.recBotCoe with
    | bot => exact le_rfl
    | coe x => exact absurd (show x ∈ liftBase s from hy) (by simp [hemp])
  · exact hne

theorem directedOn_image_coe {s : Set α} (hs : DirectedOn (· ≤ ·) s) :
    DirectedOn (· ≤ ·) ((fun a : α => (↑a : WithBot α)) '' s) := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  obtain ⟨c, hc, hxc, hyc⟩ := hs x hx y hy
  exact ⟨↑c, ⟨c, hc, rfl⟩, WithBot.coe_le_coe.mpr hxc, WithBot.coe_le_coe.mpr hyc⟩

theorem isLUB_image_coe {s : Set α} (hne : s.Nonempty) {u : α} (h : IsLUB s u) :
    IsLUB ((fun a : α => (↑a : WithBot α)) '' s) (↑u : WithBot α) := by
  constructor
  · rintro _ ⟨x, hx, rfl⟩
    exact WithBot.coe_le_coe.mpr (h.1 hx)
  · intro v hv
    obtain ⟨x₀, hx₀⟩ := hne
    induction v using WithBot.recBotCoe with
    | bot => exact absurd (hv ⟨x₀, hx₀, rfl⟩) (WithBot.not_coe_le_bot x₀)
    | coe c =>
      refine WithBot.coe_le_coe.mpr (h.2 fun x hx => ?_)
      exact WithBot.coe_le_coe.mp (hv ⟨x, hx, rfl⟩)

/-- **`↑a` is compact in `D⊥` exactly when `a` is compact in `D`.** -/
theorem isCompactElement_coe_iff {a : α} :
    IsCompactElement (↑a : WithBot α) ↔ IsCompactElement a := by
  constructor
  · intro h s u hne hs hlub hau
    obtain ⟨_, ⟨x, hx, rfl⟩, hax⟩ :=
      h ((fun a : α => (↑a : WithBot α)) '' s) (↑u : WithBot α) (hne.image _)
        (directedOn_image_coe hs) (isLUB_image_coe hne hlub) (WithBot.coe_le_coe.mpr hau)
    exact ⟨x, hx, WithBot.coe_le_coe.mp hax⟩
  · intro ha s u hne hs hlub hau
    induction u using WithBot.recBotCoe with
    | bot => exact absurd hau (WithBot.not_coe_le_bot a)
    | coe b =>
      obtain ⟨x, hx, hax⟩ :=
        ha (liftBase s) b (liftBase_nonempty_of_isLUB hlub) (directedOn_liftBase hs)
          (isLUB_liftBase hlub) (WithBot.coe_le_coe.mp hau)
      exact ⟨↑x, coe_mem_of_mem_liftBase hx, WithBot.coe_le_coe.mpr hax⟩

/-- **Lemma 17, lift conjunct.** Pull `u` back along the coercion, expand it to a
finite normal `N ◁ K(D)`, and push forward, adjoining `⊥`. Normality at the
adjoined bottom is trivial because `↓⊥ = {⊥}`; at a coercion `↑c` the compact `c`
is exactly what `N ◁ K(D)` is stated for. -/
theorem lem17_lift [Domain α] (_h : IsBifinite α) : IsBifinite (WithBot α) := by
  intro u hu husub
  have hu'fin : ((fun a : α => (↑a : WithBot α)) ⁻¹' u).Finite :=
    hu.preimage fun _ _ _ _ h => WithBot.coe_injective h
  have hu'sub : (fun a : α => (↑a : WithBot α)) ⁻¹' u ⊆ compacts α :=
    fun _ ha => isCompactElement_coe_iff.mp (husub ha)
  obtain ⟨N, hNfin, hNnorm, hNsub⟩ := _h _ hu'fin hu'sub
  refine ⟨insert ⊥ ((fun a : α => (↑a : WithBot α)) '' N),
    Set.Finite.insert _ (Set.Finite.image _ hNfin), ⟨?_, ?_⟩, ?_⟩
  · rintro y (rfl | ⟨a, ha, rfl⟩)
    · exact isCompactElement_bot
    · exact isCompactElement_coe_iff.mpr (hNnorm.subset ha)
  · rintro x hx
    induction x using WithBot.recBotCoe with
    | bot =>
      refine ⟨⟨⊥, Or.inl rfl, Set.mem_Iic.mpr le_rfl⟩, ?_⟩
      rintro y ⟨_, hy⟩ z ⟨_, hz⟩
      exact ⟨⊥, ⟨Or.inl rfl, Set.mem_Iic.mpr le_rfl⟩, hy, hz⟩
    | coe c =>
      have hc : IsCompactElement c := isCompactElement_coe_iff.mp hx
      refine ⟨⟨⊥, Or.inl rfl, Set.mem_Iic.mpr bot_le⟩, ?_⟩
      rintro y ⟨hy, hyx⟩ z ⟨hz, hzx⟩
      rcases hy with rfl | ⟨a, ha, rfl⟩
      · exact ⟨z, ⟨hz, hzx⟩, bot_le, le_rfl⟩
      rcases hz with rfl | ⟨b, hb, rfl⟩
      · exact ⟨(↑a : WithBot α), ⟨Or.inr ⟨a, ha, rfl⟩, hyx⟩, le_rfl, bot_le⟩
      obtain ⟨d, ⟨hdN, hdc⟩, had, hbd⟩ :=
        hNnorm.directedOn hc a ⟨ha, WithBot.coe_le_coe.mp hyx⟩ b
          ⟨hb, WithBot.coe_le_coe.mp hzx⟩
      exact ⟨(↑d : WithBot α), ⟨Or.inr ⟨d, hdN, rfl⟩, WithBot.coe_le_coe.mpr hdc⟩,
        WithBot.coe_le_coe.mpr had, WithBot.coe_le_coe.mpr hbd⟩
  · intro y hy
    induction y using WithBot.recBotCoe with
    | bot => exact Or.inl rfl
    | coe a => exact Or.inr ⟨a, hNsub hy, rfl⟩

theorem lem17_fun [Domain α] [Domain β] [BoundedComplete β]
    (_h₁ : IsBifinite α) (_h₂ : IsBifinite β) : IsBifinite (ScottHom α β) := by
  sorry

end ScottDomains
