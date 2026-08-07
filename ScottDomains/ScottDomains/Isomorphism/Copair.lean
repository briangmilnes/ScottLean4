import ScottDomains.StrictHom
import ScottDomains.CoalescedSum

/-!
# Lemma 9, part 3: the coalesced sum is the coproduct for strict maps

Gunter & Scott, *Semantic Domains*, Lemma 9.3, in its corrected form:

> `(E ⊕ F) ◦→ D ≅ (E ◦→ D) × (F ◦→ D)`.

(The page prints `(E ◦→ D) × (E ◦→ F)`; that form is refuted under the kernel by
`Skeleton/Recovered.lean`'s `lem9_3_printed_false`, and the recovery evidence is
in `docs/StatementRecovery.md`.)

The corrected law is the universal property the paper itself states three pages
earlier, in §4.4:

> Moreover, if `f : D ◦→ F` and `g : E ◦→ F` are strict continuous functions,
> then there is a unique strict continuous function `[f, g]` which completes the
> following diagram.

Existence of `[f, g]` is `copairFun`; uniqueness in `f` and `g` is what makes the
correspondence a bijection, and naturality in the order is what makes it an
order isomorphism.

## The two injections carry a case split, and why

`sumInlFun : E → E ⊕ F` cannot be `Sum.inl` composed with a coercion, because
the coalesced sum has **deleted** `⊥_E` before adjoining its own bottom. The
injection is therefore `dite` on `y = ⊥`, sending `⊥_E` to `⊥_{E ⊕ F}` and every
other `y` to `↑⟨Sum.inl y, _⟩`. That is what makes it strict, and it is the only
case split in the file that is not forced by `WithBot`.

Its Scott continuity (`scottContinuous_sumInlFun`) turns on one observation: an
upper bound `u` of a set of injected non-bottom elements cannot be the adjoined
bottom, so `u = ↑r`, and `r` must lie on the **left**, because `Sum`'s order
relates only same-side elements. The left component of `r` is then an upper
bound of the original set in `E`.

## Copairing, and where directedness is spent

`copairFun g h` is `⊥` at the adjoined bottom and `Sum.elim g h` on the
injections. Its continuity (`scottContinuous_copairFun`) splits on the least
upper bound of the directed set. If that bound is `⊥` the set sits inside `{⊥}`.
Otherwise the bound is `↑q`, and every base element lies below `q` — so, by the
same same-side argument, on the side `q` is on. `isLUB_copairFun_left` and
`isLUB_copairFun_right` are the two halves; each reduces the claim to Scott
continuity of the corresponding summand map, applied to `leftParts` /
`rightParts` of the base, whose nonemptiness comes from
`WithBot.not_coe_le_bot`.
-/

namespace ScottDomains.Isomorphism

open ScottDomains

variable {α β γ : Type*}
variable [CompletePartialOrder α] [CompletePartialOrder β] [CompletePartialOrder γ]

/-! ### The two injections `E → E ⊕ F` and `F → E ⊕ F` -/

open Classical in
/-- The left injection of the coalesced sum: `⊥_E` goes to the adjoined bottom,
every other `y` to its own copy. -/
noncomputable def sumInlFun (y : β) : CoalescedSum β γ :=
  if h : y = ⊥ then ⊥ else ↑(⟨Sum.inl y, h⟩ : NonBotSum β γ)

open Classical in
/-- The right injection. -/
noncomputable def sumInrFun (z : γ) : CoalescedSum β γ :=
  if h : z = ⊥ then ⊥ else ↑(⟨Sum.inr z, h⟩ : NonBotSum β γ)

theorem sumInlFun_bot : sumInlFun (γ := γ) (⊥ : β) = (⊥ : CoalescedSum β γ) :=
  dif_pos rfl

theorem sumInrFun_bot : sumInrFun (β := β) (⊥ : γ) = (⊥ : CoalescedSum β γ) :=
  dif_pos rfl

theorem sumInlFun_of_ne {y : β} (h : y ≠ ⊥) :
    sumInlFun (γ := γ) y = ↑(⟨Sum.inl y, h⟩ : NonBotSum β γ) := by
  classical simp only [sumInlFun, dif_neg h]

theorem sumInrFun_of_ne {z : γ} (h : z ≠ ⊥) :
    sumInrFun (β := β) z = ↑(⟨Sum.inr z, h⟩ : NonBotSum β γ) := by
  classical simp only [sumInrFun, dif_neg h]

theorem sumInlFun_mono : Monotone (sumInlFun (β := β) (γ := γ)) := by
  intro y₁ y₂ hy
  by_cases h₁ : y₁ = ⊥
  · rw [h₁, sumInlFun_bot]
    exact bot_le
  · have h₂ : y₂ ≠ ⊥ := fun hb => h₁ (le_bot_iff.mp (hy.trans (le_of_eq hb)))
    rw [sumInlFun_of_ne h₁, sumInlFun_of_ne h₂]
    exact (WithBot.coe_le_coe (α := NonBotSum β γ)).mpr (Sum.inl_le_inl_iff.mpr hy)

theorem sumInrFun_mono : Monotone (sumInrFun (β := β) (γ := γ)) := by
  intro z₁ z₂ hz
  by_cases h₁ : z₁ = ⊥
  · rw [h₁, sumInrFun_bot]
    exact bot_le
  · have h₂ : z₂ ≠ ⊥ := fun hb => h₁ (le_bot_iff.mp (hz.trans (le_of_eq hb)))
    rw [sumInrFun_of_ne h₁, sumInrFun_of_ne h₂]
    exact (WithBot.coe_le_coe (α := NonBotSum β γ)).mpr (Sum.inr_le_inr_iff.mpr hz)

theorem scottContinuous_sumInlFun : ScottContinuous (sumInlFun (β := β) (γ := γ)) := by
  intro s hne hs a ha
  by_cases hab : a = ⊥
  · subst hab
    have hall : ∀ y ∈ s, y = (⊥ : β) := fun y hy => le_bot_iff.mp (ha.1 hy)
    constructor
    · rintro _ ⟨y, hy, rfl⟩
      exact le_of_eq (congrArg sumInlFun (hall y hy))
    · intro u hu
      obtain ⟨y₀, hy₀⟩ := hne
      have h := hu ⟨y₀, hy₀, rfl⟩
      rwa [hall y₀ hy₀] at h
  · constructor
    · rintro _ ⟨y, hy, rfl⟩
      exact sumInlFun_mono (ha.1 hy)
    · intro u hu
      obtain ⟨y₀, hy₀, hy₀b⟩ : ∃ y ∈ s, y ≠ (⊥ : β) := by
        by_contra hcon
        refine hab (le_bot_iff.mp (ha.2 fun y hy => ?_))
        by_cases hyb : y = ⊥
        · exact le_of_eq hyb
        · exact absurd ⟨y, hy, hyb⟩ hcon
      have hu₀ : sumInlFun (γ := γ) y₀ ≤ u := hu ⟨y₀, hy₀, rfl⟩
      rw [sumInlFun_of_ne hy₀b] at hu₀
      induction u using WithBot.recBotCoe with
      | bot => exact absurd hu₀ (WithBot.not_coe_le_bot _)
      | coe r =>
        have h₀ : (Sum.inl y₀ : β ⊕ γ) ≤ r.val :=
          (WithBot.coe_le_coe (α := NonBotSum β γ)).mp hu₀
        obtain ⟨c, hc⟩ : ∃ c : β, r.val = Sum.inl c := by
          cases hr : r.val with
          | inl c => exact ⟨c, rfl⟩
          | inr d =>
            rw [hr] at h₀
            exact absurd h₀ (by simp)
        have hub : ∀ y ∈ s, y ≤ c := by
          intro y hy
          by_cases hyb : y = ⊥
          · rw [hyb]
            exact bot_le
          · have hy' : sumInlFun (γ := γ) y ≤ (↑r : CoalescedSum β γ) := hu ⟨y, hy, rfl⟩
            rw [sumInlFun_of_ne hyb] at hy'
            have h2 : (Sum.inl y : β ⊕ γ) ≤ r.val :=
              (WithBot.coe_le_coe (α := NonBotSum β γ)).mp hy'
            rw [hc] at h2
            exact Sum.inl_le_inl_iff.mp h2
        rw [sumInlFun_of_ne hab]
        refine (WithBot.coe_le_coe (α := NonBotSum β γ)).mpr ?_
        show (Sum.inl a : β ⊕ γ) ≤ r.val
        rw [hc]
        exact Sum.inl_le_inl_iff.mpr (ha.2 hub)

theorem scottContinuous_sumInrFun : ScottContinuous (sumInrFun (β := β) (γ := γ)) := by
  intro s hne hs a ha
  by_cases hab : a = ⊥
  · subst hab
    have hall : ∀ z ∈ s, z = (⊥ : γ) := fun z hz => le_bot_iff.mp (ha.1 hz)
    constructor
    · rintro _ ⟨z, hz, rfl⟩
      exact le_of_eq (congrArg sumInrFun (hall z hz))
    · intro u hu
      obtain ⟨z₀, hz₀⟩ := hne
      have h := hu ⟨z₀, hz₀, rfl⟩
      rwa [hall z₀ hz₀] at h
  · constructor
    · rintro _ ⟨z, hz, rfl⟩
      exact sumInrFun_mono (ha.1 hz)
    · intro u hu
      obtain ⟨z₀, hz₀, hz₀b⟩ : ∃ z ∈ s, z ≠ (⊥ : γ) := by
        by_contra hcon
        refine hab (le_bot_iff.mp (ha.2 fun z hz => ?_))
        by_cases hzb : z = ⊥
        · exact le_of_eq hzb
        · exact absurd ⟨z, hz, hzb⟩ hcon
      have hu₀ : sumInrFun (β := β) z₀ ≤ u := hu ⟨z₀, hz₀, rfl⟩
      rw [sumInrFun_of_ne hz₀b] at hu₀
      induction u using WithBot.recBotCoe with
      | bot => exact absurd hu₀ (WithBot.not_coe_le_bot _)
      | coe r =>
        have h₀ : (Sum.inr z₀ : β ⊕ γ) ≤ r.val :=
          (WithBot.coe_le_coe (α := NonBotSum β γ)).mp hu₀
        obtain ⟨c, hc⟩ : ∃ c : γ, r.val = Sum.inr c := by
          cases hr : r.val with
          | inr c => exact ⟨c, rfl⟩
          | inl d =>
            rw [hr] at h₀
            exact absurd h₀ (by simp)
        have hub : ∀ z ∈ s, z ≤ c := by
          intro z hz
          by_cases hzb : z = ⊥
          · rw [hzb]
            exact bot_le
          · have hz' : sumInrFun (β := β) z ≤ (↑r : CoalescedSum β γ) := hu ⟨z, hz, rfl⟩
            rw [sumInrFun_of_ne hzb] at hz'
            have h2 : (Sum.inr z : β ⊕ γ) ≤ r.val :=
              (WithBot.coe_le_coe (α := NonBotSum β γ)).mp hz'
            rw [hc] at h2
            exact Sum.inr_le_inr_iff.mp h2
        rw [sumInrFun_of_ne hab]
        refine (WithBot.coe_le_coe (α := NonBotSum β γ)).mpr ?_
        show (Sum.inr a : β ⊕ γ) ≤ r.val
        rw [hc]
        exact Sum.inr_le_inr_iff.mpr (ha.2 hub)

/-- The left injection as a strict continuous map. -/
noncomputable def sumInl : StrictHom β (CoalescedSum β γ) :=
  ⟨⟨sumInlFun, scottContinuous_sumInlFun⟩, sumInlFun_bot⟩

/-- The right injection as a strict continuous map. -/
noncomputable def sumInr : StrictHom γ (CoalescedSum β γ) :=
  ⟨⟨sumInrFun, scottContinuous_sumInrFun⟩, sumInrFun_bot⟩

/-! ### Copairing -/

/-- `[g, h]`: the unique strict map out of the coalesced sum restricting to `g`
and `h`. -/
def copairFun (g : StrictHom β α) (h : StrictHom γ α) : CoalescedSum β γ → α :=
  fun w => WithBot.recBotCoe (C := fun _ => α) ⊥
    (fun q => Sum.elim (fun y => g.val y) (fun z => h.val z) q.val) w

@[simp] theorem copairFun_bot (g : StrictHom β α) (h : StrictHom γ α) :
    copairFun g h (⊥ : CoalescedSum β γ) = ⊥ := rfl

@[simp] theorem copairFun_coe (g : StrictHom β α) (h : StrictHom γ α)
    (q : NonBotSum β γ) :
    copairFun g h (↑q : CoalescedSum β γ) =
      Sum.elim (fun y => g.val y) (fun z => h.val z) q.val := rfl

/-- A set whose least upper bound is a coercion has a nonempty base. Otherwise
the adjoined bottom would be an upper bound, contradicting
`WithBot.not_coe_le_bot`. -/
theorem sumBase_nonempty_of_isLUB_coe {s : Set (CoalescedSum β γ)} {q : NonBotSum β γ}
    (hw : IsLUB s (↑q : CoalescedSum β γ)) : (sumBase s).Nonempty := by
  by_contra hempty
  have hub : (⊥ : CoalescedSum β γ) ∈ upperBounds s := by
    intro z hz
    induction z using WithBot.recBotCoe with
    | bot => exact le_rfl
    | coe p => exact absurd ⟨p, hz⟩ hempty
  exact WithBot.not_coe_le_bot q (hw.2 hub)

/-- **Copairing is continuous on a left-sided directed set.** The least upper
bound `↑q` lies on the left, so every base element does, and the claim reduces to
Scott continuity of `g` on `leftParts` of the base. -/
theorem isLUB_copairFun_left (g : StrictHom β α) (h : StrictHom γ α)
    {s : Set (CoalescedSum β γ)} (hs : DirectedOn (· ≤ ·) s)
    {q : NonBotSum β γ} (hw : IsLUB s (↑q : CoalescedSum β γ)) {c : β}
    (hc : q.val = Sum.inl c) :
    IsLUB (copairFun g h '' s) (copairFun g h (↑q : CoalescedSum β γ)) := by
  have hqval : copairFun g h (↑q : CoalescedSum β γ) = g.val c := by
    simp only [copairFun_coe, hc, Sum.elim_inl]
  have hbase : ∀ p ∈ sumBase s, p.val ≤ q.val := fun p hp =>
    (WithBot.coe_le_coe (α := NonBotSum β γ)).mp (hw.1 (coe_mem_of_mem_sumBase hp))
  have hleft : ∀ p ∈ sumBase s, ∃ y : β, p.val = Sum.inl y := by
    intro p hp
    have hle := hbase p hp
    rw [hc] at hle
    cases hpv : p.val with
    | inl y => exact ⟨y, rfl⟩
    | inr z =>
      rw [hpv] at hle
      exact absurd hle (by simp)
  obtain ⟨p₀, hp₀⟩ := sumBase_nonempty_of_isLUB_coe hw
  obtain ⟨y₀, hy₀⟩ := hleft p₀ hp₀
  have hy₀b : y₀ ≠ (⊥ : β) := by
    have hp := p₀.2
    rw [IsNonBotSum.eq_def, hy₀] at hp
    exact hp
  have hLne : (leftParts (sumBase s)).Nonempty := ⟨y₀, p₀, hp₀, hy₀⟩
  have hLdir : DirectedOn (· ≤ ·) (leftParts (sumBase s)) :=
    directedOn_leftParts (directedOn_sumBase hs)
  have hLlub : IsLUB (leftParts (sumBase s)) c := by
    constructor
    · rintro y ⟨p, hp, e⟩
      have hle := hbase p hp
      rw [e, hc] at hle
      exact Sum.inl_le_inl_iff.mp hle
    · intro d hd
      have hdb : d ≠ (⊥ : β) := fun hb =>
        hy₀b (le_bot_iff.mp ((hd ⟨p₀, hp₀, hy₀⟩).trans (le_of_eq hb)))
      have hdub : (↑(⟨Sum.inl d, hdb⟩ : NonBotSum β γ) : CoalescedSum β γ) ∈ upperBounds s := by
        intro z hz
        induction z using WithBot.recBotCoe with
        | bot => exact bot_le
        | coe p =>
          refine (WithBot.coe_le_coe (α := NonBotSum β γ)).mpr ?_
          obtain ⟨y, hy⟩ := hleft p hz
          show p.val ≤ (Sum.inl d : β ⊕ γ)
          rw [hy]
          exact Sum.inl_le_inl_iff.mpr (hd ⟨p, hz, hy⟩)
      have := (WithBot.coe_le_coe (α := NonBotSum β γ)).mp (hw.2 hdub)
      have h2 : q.val ≤ (Sum.inl d : β ⊕ γ) := this
      rw [hc] at h2
      exact Sum.inl_le_inl_iff.mp h2
  have hg := g.val.scottContinuous hLne hLdir hLlub
  rw [hqval]
  constructor
  · rintro _ ⟨z, hz, rfl⟩
    induction z using WithBot.recBotCoe with
    | bot => exact bot_le
    | coe p =>
      obtain ⟨y, hy⟩ := hleft p hz
      have : copairFun g h (↑p : CoalescedSum β γ) = g.val y := by
        simp only [copairFun_coe, hy, Sum.elim_inl]
      rw [this]
      exact hg.1 ⟨y, ⟨p, hz, hy⟩, rfl⟩
  · intro u hu
    refine hg.2 ?_
    rintro _ ⟨y, ⟨p, hp, hy⟩, rfl⟩
    have hpu := hu ⟨(↑p : CoalescedSum β γ), coe_mem_of_mem_sumBase hp, rfl⟩
    rw [copairFun_coe, hy] at hpu
    exact hpu

/-- The mirror image of `isLUB_copairFun_left`. `Sum` carries no symmetry that
Mathlib supplies at this level, so the argument is repeated rather than
transported — the same choice `CoalescedSum.lean` makes for
`isLUB_sumSup_left` / `isLUB_sumSup_right`. -/
theorem isLUB_copairFun_right (g : StrictHom β α) (h : StrictHom γ α)
    {s : Set (CoalescedSum β γ)} (hs : DirectedOn (· ≤ ·) s)
    {q : NonBotSum β γ} (hw : IsLUB s (↑q : CoalescedSum β γ)) {c : γ}
    (hc : q.val = Sum.inr c) :
    IsLUB (copairFun g h '' s) (copairFun g h (↑q : CoalescedSum β γ)) := by
  have hqval : copairFun g h (↑q : CoalescedSum β γ) = h.val c := by
    simp only [copairFun_coe, hc, Sum.elim_inr]
  have hbase : ∀ p ∈ sumBase s, p.val ≤ q.val := fun p hp =>
    (WithBot.coe_le_coe (α := NonBotSum β γ)).mp (hw.1 (coe_mem_of_mem_sumBase hp))
  have hright : ∀ p ∈ sumBase s, ∃ z : γ, p.val = Sum.inr z := by
    intro p hp
    have hle := hbase p hp
    rw [hc] at hle
    cases hpv : p.val with
    | inr z => exact ⟨z, rfl⟩
    | inl y =>
      rw [hpv] at hle
      exact absurd hle (by simp)
  obtain ⟨p₀, hp₀⟩ := sumBase_nonempty_of_isLUB_coe hw
  obtain ⟨z₀, hz₀⟩ := hright p₀ hp₀
  have hz₀b : z₀ ≠ (⊥ : γ) := by
    have hp := p₀.2
    rw [IsNonBotSum.eq_def, hz₀] at hp
    exact hp
  have hRne : (rightParts (sumBase s)).Nonempty := ⟨z₀, p₀, hp₀, hz₀⟩
  have hRdir : DirectedOn (· ≤ ·) (rightParts (sumBase s)) :=
    directedOn_rightParts (directedOn_sumBase hs)
  have hRlub : IsLUB (rightParts (sumBase s)) c := by
    constructor
    · rintro z ⟨p, hp, e⟩
      have hle := hbase p hp
      rw [e, hc] at hle
      exact Sum.inr_le_inr_iff.mp hle
    · intro d hd
      have hdb : d ≠ (⊥ : γ) := fun hb =>
        hz₀b (le_bot_iff.mp ((hd ⟨p₀, hp₀, hz₀⟩).trans (le_of_eq hb)))
      have hdub : (↑(⟨Sum.inr d, hdb⟩ : NonBotSum β γ) : CoalescedSum β γ) ∈ upperBounds s := by
        intro w hw'
        induction w using WithBot.recBotCoe with
        | bot => exact bot_le
        | coe p =>
          refine (WithBot.coe_le_coe (α := NonBotSum β γ)).mpr ?_
          obtain ⟨z, hz⟩ := hright p hw'
          show p.val ≤ (Sum.inr d : β ⊕ γ)
          rw [hz]
          exact Sum.inr_le_inr_iff.mpr (hd ⟨p, hw', hz⟩)
      have := (WithBot.coe_le_coe (α := NonBotSum β γ)).mp (hw.2 hdub)
      have h2 : q.val ≤ (Sum.inr d : β ⊕ γ) := this
      rw [hc] at h2
      exact Sum.inr_le_inr_iff.mp h2
  have hh := h.val.scottContinuous hRne hRdir hRlub
  rw [hqval]
  constructor
  · rintro _ ⟨w, hw', rfl⟩
    induction w using WithBot.recBotCoe with
    | bot => exact bot_le
    | coe p =>
      obtain ⟨z, hz⟩ := hright p hw'
      have : copairFun g h (↑p : CoalescedSum β γ) = h.val z := by
        simp only [copairFun_coe, hz, Sum.elim_inr]
      rw [this]
      exact hh.1 ⟨z, ⟨p, hw', hz⟩, rfl⟩
  · intro u hu
    refine hh.2 ?_
    rintro _ ⟨z, ⟨p, hp, hz⟩, rfl⟩
    have hpu := hu ⟨(↑p : CoalescedSum β γ), coe_mem_of_mem_sumBase hp, rfl⟩
    rw [copairFun_coe, hz] at hpu
    exact hpu

theorem scottContinuous_copairFun (g : StrictHom β α) (h : StrictHom γ α) :
    ScottContinuous (copairFun g h) := by
  intro s hne hs w hw
  induction w using WithBot.recBotCoe with
  | bot =>
    have hall : ∀ z ∈ s, z = (⊥ : CoalescedSum β γ) := fun z hz => le_bot_iff.mp (hw.1 hz)
    constructor
    · rintro _ ⟨z, hz, rfl⟩
      exact le_of_eq (congrArg (copairFun g h) (hall z hz))
    · intro u hu
      obtain ⟨z₀, hz₀⟩ := hne
      have h' := hu ⟨z₀, hz₀, rfl⟩
      rwa [hall z₀ hz₀] at h'
  | coe q =>
    cases hq : q.val with
    | inl c => exact isLUB_copairFun_left g h hs hw hq
    | inr c => exact isLUB_copairFun_right g h hs hw hq

/-- `[g, h]` as a strict continuous map out of the coalesced sum. -/
def copair (g : StrictHom β α) (h : StrictHom γ α) : StrictHom (CoalescedSum β γ) α :=
  ⟨⟨copairFun g h, scottContinuous_copairFun g h⟩, rfl⟩

/-- Restricting a strict map along the left injection. -/
noncomputable def restrictLeft (f : StrictHom (CoalescedSum β γ) α) : StrictHom β α :=
  ⟨⟨fun y => f.val (sumInlFun y), scottContinuous_sumInlFun.comp f.val.scottContinuous⟩, by
    show f.val (sumInlFun (⊥ : β)) = ⊥
    rw [sumInlFun_bot]
    exact f.2⟩

/-- Restricting a strict map along the right injection. -/
noncomputable def restrictRight (f : StrictHom (CoalescedSum β γ) α) : StrictHom γ α :=
  ⟨⟨fun z => f.val (sumInrFun z), scottContinuous_sumInrFun.comp f.val.scottContinuous⟩, by
    show f.val (sumInrFun (⊥ : γ)) = ⊥
    rw [sumInrFun_bot]
    exact f.2⟩

/-- **Lemma 9.3**, as a named map: `(E ⊕ F) ◦→ D ≅ (E ◦→ D) × (F ◦→ D)`. -/
noncomputable def coalescedSumCopair :
    StrictHom (CoalescedSum β γ) α ≃o StrictHom β α × StrictHom γ α where
  toFun f := (restrictLeft f, restrictRight f)
  invFun p := copair p.1 p.2
  left_inv f := by
    refine Subtype.ext (ScottHom.ext ?_)
    intro w
    induction w using WithBot.recBotCoe with
    | bot => exact f.2.symm
    | coe q =>
      obtain ⟨s, hs⟩ := q
      cases s with
      | inl y =>
        show f.val (sumInlFun (γ := γ) y) =
          f.val ((⟨Sum.inl y, hs⟩ : NonBotSum β γ) : CoalescedSum β γ)
        rw [sumInlFun_of_ne hs]
      | inr z =>
        show f.val (sumInrFun (β := β) z) =
          f.val ((⟨Sum.inr z, hs⟩ : NonBotSum β γ) : CoalescedSum β γ)
        rw [sumInrFun_of_ne hs]
  right_inv p := by
    refine Prod.ext ?_ ?_
    · refine Subtype.ext (ScottHom.ext ?_)
      intro y
      by_cases hy : y = ⊥
      · show copairFun p.1 p.2 (sumInlFun y) = p.1.val y
        rw [hy, sumInlFun_bot, copairFun_bot]
        exact p.1.2.symm
      · show copairFun p.1 p.2 (sumInlFun y) = p.1.val y
        rw [sumInlFun_of_ne hy, copairFun_coe]
        rfl
    · refine Subtype.ext (ScottHom.ext ?_)
      intro z
      by_cases hz : z = ⊥
      · show copairFun p.1 p.2 (sumInrFun z) = p.2.val z
        rw [hz, sumInrFun_bot, copairFun_bot]
        exact p.2.2.symm
      · show copairFun p.1 p.2 (sumInrFun z) = p.2.val z
        rw [sumInrFun_of_ne hz, copairFun_coe]
        rfl
  map_rel_iff' := by
    intro f g
    constructor
    · rintro ⟨h₁, h₂⟩ w
      induction w using WithBot.recBotCoe with
      | bot => exact le_of_eq (f.2.trans g.2.symm)
      | coe q =>
        obtain ⟨s, hs⟩ := q
        cases s with
        | inl y =>
          have := h₁ y
          show f.val _ ≤ g.val _
          rw [← sumInlFun_of_ne hs]
          exact this
        | inr z =>
          have := h₂ z
          show f.val _ ≤ g.val _
          rw [← sumInrFun_of_ne hs]
          exact this
    · intro h
      exact ⟨fun y => h (sumInlFun y), fun z => h (sumInrFun z)⟩

end ScottDomains.Isomorphism
