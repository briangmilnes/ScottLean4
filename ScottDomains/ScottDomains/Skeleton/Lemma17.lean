import ScottDomains.Bifinite
import ScottDomains.Lift
import ScottDomains.Product
import ScottDomains.FunctionSpaceCountable
-- `IsProjection` and `p_N = normalHom`, the two ingredients of the function-space
-- conjunct; not reachable from the four imports above.
import ScottDomains.NormalProjection
-- `Set.Finite.prod`, for the rectangle `N₁ ×ˢ N₂` used in the product conjunct.
import Mathlib.Data.Finite.Prod
-- `Set.Finite.finite_subsets`, for finiteness of `im(p_N)` when `N` is finite.
import Mathlib.Data.Set.Finite.Powerset

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
theorem lemma_17_prod [Domain α] [Domain β] (_h₁ : IsBifinite α) (_h₂ : IsBifinite β) :
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
theorem lemma_17_lift [Domain α] (_h : IsBifinite α) : IsBifinite (WithBot α) := by
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

/-! ### Projections with a finite image

Gunter & Scott prove the function-space conjunct by exhibiting the finitary
projections `(q, p)(f) = q ∘ f ∘ p` and citing the correspondence of Theorem 6.
With `IsBifinite` *defined* as the Plotkin condition on the basis, the
correspondence is not needed: a projection whose image is **finite** already has
that image inside the basis and normal in it, and `P x` is the greatest member of
`im(P) ∩ ↓x`. Lemma 5's `IsFinitaryProjection.isNormalIn_compacts` is the general
statement; the finite case below needs no algebraicity of the image. -/

section FiniteRange

open ScottHom

variable {γ : Type*} [CompletePartialOrder γ] {P : ScottHom γ γ}

/-- A nonempty directed subset of a finite set has a greatest element: a maximal
element is greatest once every pair has an upper bound inside the set. -/
theorem exists_greatest_of_finite_directedOn {s : Set γ} (hfin : s.Finite)
    (hne : s.Nonempty) (hs : DirectedOn (· ≤ ·) s) : ∃ m ∈ s, ∀ a ∈ s, a ≤ m := by
  obtain ⟨m, hm, hmax⟩ := hfin.exists_maximal hne
  refine ⟨m, hm, fun a ha => ?_⟩
  obtain ⟨c, hc, hmc, hac⟩ := hs m hm a ha
  exact hac.trans (hmax hc hmc)

/-- **A projection with a finite image has that image inside the basis.** The
`P`-image of a directed `s` is a directed subset of the finite `im(P)`, so it has
a greatest element `P x`; continuity identifies `P u` with it, and
`y = P y ≤ P u = P x ≤ x` supplies the witness required of a compact element. -/
theorem isCompactElement_of_mem_range_of_finite (hP : IsProjection P)
    (hfin : (Set.range ⇑P).Finite) {y : γ} (hy : y ∈ Set.range ⇑P) :
    IsCompactElement y := by
  intro s u hne hs hlub hyu
  have hsub : ⇑P '' s ⊆ Set.range ⇑P := by
    rintro _ ⟨x, _, rfl⟩
    exact Set.mem_range_self x
  obtain ⟨m, hm, hmax⟩ :=
    exists_greatest_of_finite_directedOn (hfin.subset hsub) (hne.image _)
      (P.directedOn_image hs)
  have hmlub : IsLUB (⇑P '' s) m := ⟨fun a ha => hmax a ha, fun _ hv => hv hm⟩
  have hPu : P u = m := (P.scottContinuous hne hs hlub).unique hmlub
  obtain ⟨x, hx, rfl⟩ := hm
  refine ⟨x, hx, ?_⟩
  calc y = P y := (hP.apply_of_mem_range hy).symm
    _ ≤ P u := P.monotone hyu
    _ = P x := hPu
    _ ≤ x := hP.le x

/-- **A projection with a finite image has that image normal in the basis.**
`P x` lies in `im(P) ∩ ↓x` and dominates every member of it, which discharges
nonemptiness and directedness together. -/
theorem isNormalIn_range_of_finite (hP : IsProjection P)
    (hfin : (Set.range ⇑P).Finite) : Set.range ⇑P ◁ compacts γ := by
  refine ⟨fun _ hy => isCompactElement_of_mem_range_of_finite hP hfin hy,
    fun x _ => ⟨⟨P x, Set.mem_range_self x, Set.mem_Iic.mpr (hP.le x)⟩, ?_⟩⟩
  rintro a ⟨ha, hax⟩ b ⟨hb, hbx⟩
  exact ⟨P x, ⟨Set.mem_range_self x, Set.mem_Iic.mpr (hP.le x)⟩,
    (hP.apply_of_mem_range ha).symm.trans_le (P.monotone hax),
    (hP.apply_of_mem_range hb).symm.trans_le (P.monotone hbx)⟩

end FiniteRange

/-! ### `p_N` has a finite image, and the operator `(q, p)` -/

section CompHom

open ScottHom

/-- `p_N` has a finite image when `N` is finite: `p_N x = ⨆(N ∩ ↓x)` and there are
only finitely many subsets of `N` to take the least upper bound of. -/
theorem finite_range_normalHom [IsAlgebraic α] {N : Set α} (hN : N ◁ compacts α)
    (hfin : N.Finite) : (Set.range ⇑(normalHom hN)).Finite := by
  refine Set.Finite.subset (Set.Finite.image sSup hfin.finite_subsets) ?_
  rintro _ ⟨x, rfl⟩
  exact ⟨N ∩ Set.Iic x, Set.inter_subset_left, rfl⟩

/-- `(q, p)(f) = q ∘ f ∘ p`, Gunter & Scott's function-space operator. -/
def compFun (p : ScottHom α α) (q : ScottHom β β) (f : ScottHom α β) : ScottHom α β :=
  ⟨⇑q ∘ ⇑f ∘ ⇑p,
    ScottContinuous.comp (ScottContinuous.comp p.scottContinuous f.scottContinuous)
      q.scottContinuous⟩

@[simp] theorem compFun_apply (p : ScottHom α α) (q : ScottHom β β) (f : ScottHom α β)
    (x : α) : compFun p q f x = q (f (p x)) := rfl

/-- `(q, p)` is itself Scott continuous on `D → E`. Suprema in the function space
are pointwise, so the claim reduces at each `x` to continuity of `q` applied to
the evaluation image of `d` at `p x`. -/
theorem scottContinuous_compFun (p : ScottHom α α) (q : ScottHom β β) :
    ScottContinuous (compFun p q) := by
  intro d hne hd F hF
  constructor
  · rintro _ ⟨f, hf, rfl⟩
    intro x
    exact q.monotone (hF.1 hf (p x))
  · intro G hG x
    have hqlub : IsLUB (⇑q '' ((fun f : ScottHom α β => f (p x)) '' d)) (q (F (p x))) :=
      q.scottContinuous (hne.image _) (directedOn_eval_image hd (p x))
        (isLUB_eval_image_of_isLUB hd hF (p x))
    refine hqlub.2 ?_
    rintro _ ⟨_, ⟨f, hf, rfl⟩, rfl⟩
    exact hG ⟨f, hf, rfl⟩ x

/-- `(q, p)` as an element of `(D → E) → (D → E)`. -/
noncomputable def compHom (p : ScottHom α α) (q : ScottHom β β) :
    ScottHom (ScottHom α β) (ScottHom α β) :=
  ⟨compFun p q, scottContinuous_compFun p q⟩

@[simp] theorem compHom_apply (p : ScottHom α α) (q : ScottHom β β) (f : ScottHom α β)
    (x : α) : compHom p q f x = q (f (p x)) := rfl

/-- `(q, p)` is a projection whenever `p` and `q` are: idempotence is the two
idempotences composed, and `q (f (p x)) ≤ f (p x) ≤ f x`. -/
theorem isProjection_compHom {p : ScottHom α α} {q : ScottHom β β}
    (hp : IsProjection p) (hq : IsProjection q) : IsProjection (compHom p q) := by
  refine ⟨fun f => ?_, fun f x => ?_⟩
  · ext x
    show q (q (f (p (p x)))) = q (f (p x))
    rw [hp.idem, hq.idem]
  · exact (hq.le (f (p x))).trans (f.monotone (hp.le x))

/-- **`(q, p)` has a finite image when `p` and `q` do.** An element of the image
is fixed by `p` in its argument — `(q,p)(f)(x) = (q,p)(f)(p x)` — and its values
lie in `im(q)`, so it is determined by a function `im(p) → im(q)`, and there are
finitely many of those. -/
theorem finite_range_compHom {p : ScottHom α α} {q : ScottHom β β}
    (hp : IsProjection p) (hq : IsProjection q) (hpfin : (Set.range ⇑p).Finite)
    (hqfin : (Set.range ⇑q).Finite) : (Set.range ⇑(compHom p q)).Finite := by
  haveI : Finite ↥(Set.range ⇑p) := hpfin.to_subtype
  haveI : Finite ↥(Set.range ⇑q) := hqfin.to_subtype
  have hfix : ∀ (f : ScottHom α β) (x : α), compHom p q f (p x) = compHom p q f x := by
    intro f x
    show q (f (p (p x))) = q (f (p x))
    rw [hp.idem]
  have hval : ∀ (f : ScottHom α β) (y : α), q (compHom p q f y) = compHom p q f y :=
    fun f y => hq.apply_of_mem_range (Set.mem_range_self (f (p y)))
  rw [← Set.finite_coe_iff]
  refine Finite.of_injective
    (fun F : ↥(Set.range ⇑(compHom p q)) => fun k : ↥(Set.range ⇑p) =>
      (⟨q (F.val k.val), Set.mem_range_self _⟩ : ↥(Set.range ⇑q))) ?_
  rintro ⟨_, f₁, rfl⟩ ⟨_, f₂, rfl⟩ hEq
  refine Subtype.ext (ScottHom.ext fun x => ?_)
  have hy : q (compHom p q f₁ (p x)) = q (compHom p q f₂ (p x)) :=
    congrArg Subtype.val (congrFun hEq ⟨p x, Set.mem_range_self x⟩)
  calc compHom p q f₁ x = compHom p q f₁ (p x) := (hfix f₁ x).symm
    _ = q (compHom p q f₁ (p x)) := (hval f₁ (p x)).symm
    _ = q (compHom p q f₂ (p x)) := hy
    _ = compHom p q f₂ (p x) := hval f₂ (p x)
    _ = compHom p q f₂ x := hfix f₂ x

end CompHom

/-! ### Lemma 17, function-space conjunct -/

open ScottHom in
/-- **Lemma 17, function-space conjunct.** Every `f ∈ u` is a finite join of step
functions `step(k, e)` with `k ∈ K(D)` and `e ∈ K(E)` (`CompactFunction.lean`).
Collect all those `k` and `e`, expand each collection to a finite normal subposet
`N₁ ◁ K(D)`, `N₂ ◁ K(E)`, and form `P = (p_{N₂}, p_{N₁})`. Then `P` is a
projection with finite image, so `im(P)` is a finite normal subposet of
`K(D → E)`; and `P` fixes each `f ∈ u`, because `P f ≥ step(k, e)` for every step
function in the join — `k ∈ N₁` gives `k ≤ p_{N₁} x` whenever `k ≤ x`, and
`e ∈ N₂` gives `p_{N₂} e = e`. -/
theorem lemma_17_fun [Domain α] [Domain β] [BoundedComplete β]
    (_h₁ : IsBifinite α) (_h₂ : IsBifinite β) : IsBifinite (ScottHom α β) := by
  intro u hu husub
  have hstep : ∀ f : ScottHom α β, f ∈ u →
      ∃ S : Set (ScottHom α β), S.Finite ∧ S ⊆ stepsBelow f ∧ IsLUB S f :=
    fun f hf => exists_finite_isLUB_of_isCompactElement (husub hf)
  choose! S hSfin hSsub hSlub using hstep
  have hTfin : (⋃ f ∈ u, S f).Finite := hu.biUnion hSfin
  have hTstep : ∀ g ∈ ⋃ f ∈ u, S f, ∃ pr : α × β, IsStepPair g pr := by
    intro g hg
    obtain ⟨f, hf, hgS⟩ := Set.mem_iUnion₂.mp hg
    exact (hSsub f hf hgS).1
  choose! π hπ using hTstep
  have hK : (fun g => (π g).1) '' (⋃ f ∈ u, S f) ⊆ compacts α := by
    rintro _ ⟨g, hg, rfl⟩
    exact (hπ g hg).1
  have hE : (fun g => (π g).2) '' (⋃ f ∈ u, S f) ⊆ compacts β := by
    rintro _ ⟨g, hg, rfl⟩
    exact (hπ g hg).2.1
  obtain ⟨N₁, hN₁fin, hN₁, hN₁sub⟩ := _h₁ _ (hTfin.image _) hK
  obtain ⟨N₂, hN₂fin, hN₂, hN₂sub⟩ := _h₂ _ (hTfin.image _) hE
  have hp : IsProjection (normalHom hN₁) := isProjection_normalHom hN₁
  have hq : IsProjection (normalHom hN₂) := isProjection_normalHom hN₂
  have hP : IsProjection (compHom (normalHom hN₁) (normalHom hN₂)) := isProjection_compHom hp hq
  have hPfin : (Set.range ⇑(compHom (normalHom hN₁) (normalHom hN₂))).Finite :=
    finite_range_compHom hp hq (finite_range_normalHom hN₁ hN₁fin)
      (finite_range_normalHom hN₂ hN₂fin)
  refine ⟨Set.range ⇑(compHom (normalHom hN₁) (normalHom hN₂)), hPfin,
    isNormalIn_range_of_finite hP hPfin, ?_⟩
  intro f hf
  refine ⟨f, le_antisymm (hP.le f) ?_⟩
  refine (hSlub f hf).2 ?_
  intro g hg
  have hgT : g ∈ ⋃ f ∈ u, S f := Set.mem_biUnion hf hg
  obtain ⟨_, _, hgfun⟩ := hπ g hgT
  intro x
  show g x ≤ normalFun N₂ (f (normalFun N₁ x))
  by_cases hkx : (π g).1 ≤ x
  · have hkp : (π g).1 ≤ normalFun N₁ x :=
      le_normalFun hN₁ (hN₁sub ⟨g, hgT, rfl⟩) hkx
    have hle : (π g).2 ≤ f (normalFun N₁ x) := by
      have hgf := ScottHom.le_def.mp (hSsub f hf hg).2 (normalFun N₁ x)
      rwa [hgfun, stepFun_of_le hkp] at hgf
    calc g x = (π g).2 := by rw [hgfun]; exact stepFun_of_le hkx
      _ = normalFun N₂ ((π g).2) := (normalFun_of_mem hN₂ (hN₂sub ⟨g, hgT, rfl⟩)).symm
      _ ≤ normalFun N₂ (f (normalFun N₁ x)) := monotone_normalFun hN₂ hle
  · rw [hgfun, stepFun_of_not_le hkx]
    exact bot_le

end ScottDomains
