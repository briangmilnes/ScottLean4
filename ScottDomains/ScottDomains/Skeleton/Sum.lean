import ScottDomains.CoalescedSum
import ScottDomains.Smash
import ScottDomains.Bifinite
-- `Set.Finite.prod`, for the rectangle `N₁ ×ˢ N₂` used in the smash conjunct.
import Mathlib.Data.Finite.Prod

/-!
# The `+` conjuncts of Lemmas 10 and 17, and the `⊗` conjunct of Lemma 17

Gunter & Scott, *Semantic Domains*, §4.5 and §6.2:

> **Lemma 10** If `D` and `E` are bounded complete domains then so are the cpo's
> `D → E`, `D →⊥ E`, `D × E`, `D ⊗ E`, `D + E`, `D⊥`.

> **Lemma 17** `D, E` bifinite ⟹ `→, ×, ⊗, +, ()⊥` bifinite (incl. function
> space).

`Skeleton/Lemma10.lean` (r0027) proved the `×`, `⊗`, `⊥` and `→⊥` conjuncts of
Lemma 10 and `Skeleton/Lemma17.lean` (r0027) the `×`, `⊥` and `→` conjuncts of
Lemma 17. The three statements missing from both were exactly those naming an
operator that had no instance or no proof: `D + E` had **no `CompletePartialOrder`
instance at all** until r0028 supplied `sumSup` and `sumCpo`, so neither `+`
conjunct could even be stated; the `⊗` conjunct of Lemma 17 was omitted by
oversight. This file closes all three, taking Lemma 10 to 6 of 6 conjuncts and
Lemma 17 to 5 of 5.

## What the bifiniteness proofs need

`IsBifinite` is the Plotkin condition on the basis, so each conjunct is: given a
finite `u ⊆ K(D ⊕ E)`, produce a finite `N ◁ K(D ⊕ E)` containing it. The
construction is to push `u` down into the summands, expand there, and push the
result back up. Both moves need the basis of the operator computed in terms of
the bases of its arguments:

* `K(D ⊕ E) = {⊥} ∪ ↑K(D)∖{⊥} ∪ ↑K(E)∖{⊥}` — `isCompactElement_coe_inl_iff` and
  its `inr` mirror;
* `K(D ⊗ E) = {⊥} ∪ (K(D)∖{⊥} × K(E)∖{⊥})` — `isCompactElement_coe_smash_iff`.

Each is an `iff` and both directions are spent: the forward one to push `u` down,
the backward one to certify the set built back up.

**Owned by agent1.**
-/

namespace ScottDomains

variable {α β : Type*} [CompletePartialOrder α] [CompletePartialOrder β]

/-! ### The disjoint order on `α ⊕ β`

Four inversion lemmas. `Sum.instLESum` relates only same-side elements, so a
comparison with a left injection on either side forces the other side to be a
left injection too. Everything about one-sidedness in this file reduces to these.
-/

theorem exists_inl_of_le_inl {v : α ⊕ β} {x : α} (h : v ≤ Sum.inl x) :
    ∃ x' : α, v = Sum.inl x' ∧ x' ≤ x := by
  cases hv : v with
  | inl x' =>
    rw [hv] at h
    exact ⟨x', rfl, Sum.inl_le_inl_iff.mp h⟩
  | inr y =>
    rw [hv] at h
    exact absurd h (by simp)

theorem exists_inl_of_inl_le {v : α ⊕ β} {x : α} (h : Sum.inl x ≤ v) :
    ∃ x' : α, v = Sum.inl x' ∧ x ≤ x' := by
  cases hv : v with
  | inl x' =>
    rw [hv] at h
    exact ⟨x', rfl, Sum.inl_le_inl_iff.mp h⟩
  | inr y =>
    rw [hv] at h
    exact absurd h (by simp)

theorem exists_inr_of_le_inr {v : α ⊕ β} {y : β} (h : v ≤ Sum.inr y) :
    ∃ y' : β, v = Sum.inr y' ∧ y' ≤ y := by
  cases hv : v with
  | inr y' =>
    rw [hv] at h
    exact ⟨y', rfl, Sum.inr_le_inr_iff.mp h⟩
  | inl x =>
    rw [hv] at h
    exact absurd h (by simp)

theorem exists_inr_of_inr_le {v : α ⊕ β} {y : β} (h : Sum.inr y ≤ v) :
    ∃ y' : β, v = Sum.inr y' ∧ y ≤ y' := by
  cases hv : v with
  | inr y' =>
    rw [hv] at h
    exact ⟨y', rfl, Sum.inr_le_inr_iff.mp h⟩
  | inl x =>
    rw [hv] at h
    exact absurd h (by simp)

/-- The non-bottom witness carried by a member of `NonBotSum`, on the left. -/
theorem ne_bot_of_val_eq_inl {q : NonBotSum α β} {x : α} (h : q.val = Sum.inl x) : x ≠ ⊥ := by
  have hq := q.2
  rw [IsNonBotSum.eq_def, h] at hq
  exact hq

/-- The same on the right. -/
theorem ne_bot_of_val_eq_inr {q : NonBotSum α β} {y : β} (h : q.val = Sum.inr y) : y ≠ ⊥ := by
  have hq := q.2
  rw [IsNonBotSum.eq_def, h] at hq
  exact hq

/-! ### Lemma 10, the `D + E` conjunct -/

/-- An upper bound of a set whose base is nonempty is a coerced injection, never
the adjoined bottom — the coalesced-sum form of `exists_coe_of_mem_upperBounds`. -/
theorem exists_coe_of_mem_upperBounds_sum {s : Set (CoalescedSum α β)}
    (hne : (sumBase s).Nonempty) {u : CoalescedSum α β} (hu : u ∈ upperBounds s) :
    ∃ r : NonBotSum α β, u = ↑r := by
  obtain ⟨q₀, hq₀⟩ := hne
  induction u using WithBot.recBotCoe with
  | bot => exact absurd (hu (coe_mem_of_mem_sumBase hq₀)) (WithBot.not_coe_le_bot q₀)
  | coe r => exact ⟨r, rfl⟩

/-- **Lemma 10, `D + E`.** A bounded set with nonempty base is bounded by a
coerced injection `↑r`, and every member of the base is below `r`, so — `Sum`'s
order relating only same-side elements — the whole base lies on `r`'s side and
that side's parts are bounded by `r`'s value. Bounded completeness of the summand
makes the parts' supremum their least upper bound, which is what
`isLUB_sumSup_left` / `isLUB_sumSup_right` ask for. On an empty base the set is
contained in `{⊥}` and the value is `⊥`.

Unlike `lemma_10_smash`, this conjunct was not merely unproved before r0028: it was
unstatable, because `CoalescedSum α β` had no `CompletePartialOrder` instance. -/
theorem lemma_10_sum [Domain α] [BoundedComplete α] [Domain β] [BoundedComplete β] :
    BoundedComplete (CoalescedSum α β) where
  isLUB_sSup_of_bddAbove s hs := by
    show IsLUB s (sumSup s)
    by_cases hne : (sumBase s).Nonempty
    · obtain ⟨q₀, hq₀⟩ := hne
      obtain ⟨u, hu⟩ := hs
      obtain ⟨r, rfl⟩ := exists_coe_of_mem_upperBounds_sum ⟨q₀, hq₀⟩ hu
      have hle : ∀ q ∈ sumBase s, q.val ≤ r.val := fun q hq =>
        (WithBot.coe_le_coe (α := NonBotSum α β)).mp (hu (coe_mem_of_mem_sumBase hq))
      cases hr : r.val with
      | inl xr =>
        have hleft : ∀ q ∈ sumBase s, ∃ x : α, q.val = Sum.inl x := by
          intro q hq
          obtain ⟨x, hx, _⟩ := exists_inl_of_le_inl (hr ▸ hle q hq)
          exact ⟨x, hx⟩
        have hbdd : BddAbove (leftParts (sumBase s)) := by
          refine ⟨xr, ?_⟩
          rintro x ⟨q, hq, hqx⟩
          obtain ⟨x', hx', hle'⟩ := exists_inl_of_le_inl (hr ▸ hle q hq)
          rw [hqx] at hx'
          exact (Sum.inl_injective hx'.symm) ▸ hle'
        exact isLUB_sumSup_left hq₀ hleft (isLUB_sSup_of_bddAbove hbdd)
      | inr yr =>
        have hright : ∀ q ∈ sumBase s, ∃ y : β, q.val = Sum.inr y := by
          intro q hq
          obtain ⟨y, hy, _⟩ := exists_inr_of_le_inr (hr ▸ hle q hq)
          exact ⟨y, hy⟩
        have hbdd : BddAbove (rightParts (sumBase s)) := by
          refine ⟨yr, ?_⟩
          rintro y ⟨q, hq, hqy⟩
          obtain ⟨y', hy', hle'⟩ := exists_inr_of_le_inr (hr ▸ hle q hq)
          rw [hqy] at hy'
          exact (Sum.inr_injective hy'.symm) ▸ hle'
        exact isLUB_sumSup_right hq₀ hright (isLUB_sSup_of_bddAbove hbdd)
    · exact isLUB_sumSup_of_empty_base hne

/-! ### Directed sets with the bottom element removed

A directed set of `D` does not transport into `D ⊕ E` or `D ⊗ E` as it stands,
because `⊥_D` is not in the image of either injection — it was removed before the
new bottom was adjoined. Deleting it changes neither directedness nor the least
upper bound, provided that least upper bound is not itself `⊥`. -/

theorem isLUB_diff_bot {s : Set α} {u : α} (hdir : DirectedOn (· ≤ ·) s)
    (hlub : IsLUB s u) (hu : u ≠ ⊥) :
    (s \ {⊥}).Nonempty ∧ DirectedOn (· ≤ ·) (s \ {⊥}) ∧ IsLUB (s \ {⊥}) u := by
  refine ⟨?_, ?_, ?_⟩
  · rcases Set.eq_empty_or_nonempty (s \ {(⊥ : α)}) with hemp | h
    · refine absurd (le_bot_iff.mp (hlub.2 fun a ha => ?_)) hu
      by_cases hab : a = ⊥
      · exact le_of_eq hab
      · exact absurd (show a ∈ s \ {(⊥ : α)} from ⟨ha, hab⟩) (by simp [hemp])
    · exact h
  · rintro a ⟨ha, hab⟩ b ⟨hb, _⟩
    obtain ⟨c, hc, hac, hbc⟩ := hdir a ha b hb
    exact ⟨c, ⟨hc, fun hcb => hab (le_bot_iff.mp (hac.trans_eq hcb))⟩, hac, hbc⟩
  · refine ⟨fun a ha => hlub.1 ha.1, fun v hv => hlub.2 fun a ha => ?_⟩
    by_cases hab : a = ⊥
    · exact hab ▸ bot_le
    · exact hv ⟨ha, hab⟩

/-! ### The two injections of `D ⊕ E`, made total

`Sum.inl` does not land in `D ⊕ E`: `⊥_D` has been removed. `sumInl` sends it to
the adjoined bottom instead, which is the coalescing the paper describes, and
keeps the map injective — that is what makes the preimage of a finite set finite,
the step `lemma_17_sum` starts from. -/

open Classical in
/-- The left injection `D → D ⊕ E`, with `⊥_D` sent to `⊥_{D⊕E}`. -/
noncomputable def sumInl (β : Type*) [CompletePartialOrder β] (x : α) : CoalescedSum α β :=
  if h : x ≠ ⊥ then ↑(⟨Sum.inl x, h⟩ : NonBotSum α β) else ⊥

open Classical in
/-- The right injection `E → D ⊕ E`, with `⊥_E` sent to `⊥_{D⊕E}`. -/
noncomputable def sumInr (α : Type*) [CompletePartialOrder α] (y : β) : CoalescedSum α β :=
  if h : y ≠ ⊥ then ↑(⟨Sum.inr y, h⟩ : NonBotSum α β) else ⊥

theorem sumInl_of_ne_bot {x : α} (h : x ≠ ⊥) :
    sumInl β x = ↑(⟨Sum.inl x, h⟩ : NonBotSum α β) := by
  classical simp only [sumInl, dif_pos h]

theorem sumInr_of_ne_bot {y : β} (h : y ≠ ⊥) :
    sumInr α y = ↑(⟨Sum.inr y, h⟩ : NonBotSum α β) := by
  classical simp only [sumInr, dif_pos h]

@[simp] theorem sumInl_bot : sumInl β (⊥ : α) = (⊥ : CoalescedSum α β) := by
  classical simp only [sumInl, dif_neg (fun h : (⊥ : α) ≠ ⊥ => h rfl)]

@[simp] theorem sumInr_bot : sumInr α (⊥ : β) = (⊥ : CoalescedSum α β) := by
  classical simp only [sumInr, dif_neg (fun h : (⊥ : β) ≠ ⊥ => h rfl)]

theorem monotone_sumInl : Monotone (sumInl β : α → CoalescedSum α β) := by
  intro x y hxy
  by_cases hx : x = ⊥
  · rw [hx, sumInl_bot]
    exact bot_le
  · have hy : y ≠ ⊥ := fun hb => hx (le_bot_iff.mp (hxy.trans_eq hb))
    rw [sumInl_of_ne_bot hx, sumInl_of_ne_bot hy]
    refine (WithBot.coe_le_coe (α := NonBotSum α β)).mpr ?_
    show Sum.inl x ≤ (Sum.inl y : α ⊕ β)
    exact Sum.inl_le_inl_iff.mpr hxy

theorem monotone_sumInr : Monotone (sumInr α : β → CoalescedSum α β) := by
  intro x y hxy
  by_cases hx : x = ⊥
  · rw [hx, sumInr_bot]
    exact bot_le
  · have hy : y ≠ ⊥ := fun hb => hx (le_bot_iff.mp (hxy.trans_eq hb))
    rw [sumInr_of_ne_bot hx, sumInr_of_ne_bot hy]
    refine (WithBot.coe_le_coe (α := NonBotSum α β)).mpr ?_
    show Sum.inr x ≤ (Sum.inr y : α ⊕ β)
    exact Sum.inr_le_inr_iff.mpr hxy

theorem injective_sumInl : Function.Injective (sumInl β : α → CoalescedSum α β) := by
  intro x y hxy
  by_cases hx : x = ⊥ <;> by_cases hy : y = ⊥
  · rw [hx, hy]
  · rw [hx, sumInl_bot, sumInl_of_ne_bot hy] at hxy
    exact absurd hxy.symm WithBot.coe_ne_bot
  · rw [hy, sumInl_bot, sumInl_of_ne_bot hx] at hxy
    exact absurd hxy WithBot.coe_ne_bot
  · rw [sumInl_of_ne_bot hx, sumInl_of_ne_bot hy] at hxy
    have h2 : Sum.inl x = (Sum.inl y : α ⊕ β) :=
      congrArg Subtype.val (WithBot.coe_injective hxy)
    exact Sum.inl_injective h2

theorem injective_sumInr : Function.Injective (sumInr α : β → CoalescedSum α β) := by
  intro x y hxy
  by_cases hx : x = ⊥ <;> by_cases hy : y = ⊥
  · rw [hx, hy]
  · rw [hx, sumInr_bot, sumInr_of_ne_bot hy] at hxy
    exact absurd hxy.symm WithBot.coe_ne_bot
  · rw [hy, sumInr_bot, sumInr_of_ne_bot hx] at hxy
    exact absurd hxy WithBot.coe_ne_bot
  · rw [sumInr_of_ne_bot hx, sumInr_of_ne_bot hy] at hxy
    have h2 : Sum.inr x = (Sum.inr y : α ⊕ β) :=
      congrArg Subtype.val (WithBot.coe_injective hxy)
    exact Sum.inr_injective h2

theorem directedOn_image_sumInl {s : Set α} (hdir : DirectedOn (· ≤ ·) s) :
    DirectedOn (· ≤ ·) ((sumInl β : α → CoalescedSum α β) '' s) := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  obtain ⟨c, hc, hac, hbc⟩ := hdir a ha b hb
  exact ⟨sumInl β c, ⟨c, hc, rfl⟩, monotone_sumInl hac, monotone_sumInl hbc⟩

theorem directedOn_image_sumInr {s : Set β} (hdir : DirectedOn (· ≤ ·) s) :
    DirectedOn (· ≤ ·) ((sumInr α : β → CoalescedSum α β) '' s) := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  obtain ⟨c, hc, hac, hbc⟩ := hdir a ha b hb
  exact ⟨sumInr α c, ⟨c, hc, rfl⟩, monotone_sumInr hac, monotone_sumInr hbc⟩

/-- A least upper bound of a set of non-`⊥` elements is carried by `sumInl` to a
least upper bound of the image. An upper bound of the image is not the adjoined
bottom — the image is nonempty and consists of coercions — so it is `↑t`, and `t`
is a left injection because everything below it is. -/
theorem isLUB_image_sumInl {s : Set α} (hne : s.Nonempty) (hbot : ∀ a ∈ s, a ≠ ⊥)
    {u : α} (hu : u ≠ ⊥) (hlub : IsLUB s u) :
    IsLUB ((sumInl β : α → CoalescedSum α β) '' s) (sumInl β u) := by
  obtain ⟨a₀, ha₀⟩ := hne
  constructor
  · rintro _ ⟨a, ha, rfl⟩
    exact monotone_sumInl (hlub.1 ha)
  · intro v hv
    have hv₀ : sumInl β a₀ ≤ v := hv ⟨a₀, ha₀, rfl⟩
    rw [sumInl_of_ne_bot (hbot a₀ ha₀)] at hv₀
    obtain ⟨t, rfl⟩ : ∃ t : NonBotSum α β, v = ↑t := by
      induction v using WithBot.recBotCoe with
      | bot => exact absurd hv₀ (WithBot.not_coe_le_bot _)
      | coe t => exact ⟨t, rfl⟩
    have h₀ : Sum.inl a₀ ≤ t.val := (WithBot.coe_le_coe (α := NonBotSum α β)).mp hv₀
    obtain ⟨xt, hxt, _⟩ := exists_inl_of_inl_le h₀
    rw [sumInl_of_ne_bot hu]
    refine (WithBot.coe_le_coe (α := NonBotSum α β)).mpr ?_
    show Sum.inl u ≤ t.val
    rw [hxt]
    refine Sum.inl_le_inl_iff.mpr (hlub.2 fun a ha => ?_)
    have hva : sumInl β a ≤ (↑t : CoalescedSum α β) := hv ⟨a, ha, rfl⟩
    rw [sumInl_of_ne_bot (hbot a ha)] at hva
    have hva' : Sum.inl a ≤ t.val := (WithBot.coe_le_coe (α := NonBotSum α β)).mp hva
    rw [hxt] at hva'
    exact Sum.inl_le_inl_iff.mp hva'

/-- The mirror image of `isLUB_image_sumInl`. -/
theorem isLUB_image_sumInr {s : Set β} (hne : s.Nonempty) (hbot : ∀ a ∈ s, a ≠ ⊥)
    {u : β} (hu : u ≠ ⊥) (hlub : IsLUB s u) :
    IsLUB ((sumInr α : β → CoalescedSum α β) '' s) (sumInr α u) := by
  obtain ⟨a₀, ha₀⟩ := hne
  constructor
  · rintro _ ⟨a, ha, rfl⟩
    exact monotone_sumInr (hlub.1 ha)
  · intro v hv
    have hv₀ : sumInr α a₀ ≤ v := hv ⟨a₀, ha₀, rfl⟩
    rw [sumInr_of_ne_bot (hbot a₀ ha₀)] at hv₀
    obtain ⟨t, rfl⟩ : ∃ t : NonBotSum α β, v = ↑t := by
      induction v using WithBot.recBotCoe with
      | bot => exact absurd hv₀ (WithBot.not_coe_le_bot _)
      | coe t => exact ⟨t, rfl⟩
    have h₀ : Sum.inr a₀ ≤ t.val := (WithBot.coe_le_coe (α := NonBotSum α β)).mp hv₀
    obtain ⟨yt, hyt, _⟩ := exists_inr_of_inr_le h₀
    rw [sumInr_of_ne_bot hu]
    refine (WithBot.coe_le_coe (α := NonBotSum α β)).mpr ?_
    show Sum.inr u ≤ t.val
    rw [hyt]
    refine Sum.inr_le_inr_iff.mpr (hlub.2 fun a ha => ?_)
    have hva : sumInr α a ≤ (↑t : CoalescedSum α β) := hv ⟨a, ha, rfl⟩
    rw [sumInr_of_ne_bot (hbot a ha)] at hva
    have hva' : Sum.inr a ≤ t.val := (WithBot.coe_le_coe (α := NonBotSum α β)).mp hva
    rw [hyt] at hva'
    exact Sum.inr_le_inr_iff.mp hva'

/-! ### The basis of `D ⊕ E`

`K(D ⊕ E) = {⊥} ∪ ↑(K(D)∖{⊥}) ∪ ↑(K(E)∖{⊥})`. The transfer both ways rests on the
observation that a least upper bound of `s ⊆ D ⊕ E` that is a coercion pins the
base of `s` to one summand and restricts to a least upper bound of that summand's
parts. -/

theorem exists_coe_of_coe_le {q : NonBotSum α β} {z : CoalescedSum α β}
    (h : (↑q : CoalescedSum α β) ≤ z) : ∃ r : NonBotSum α β, z = ↑r := by
  induction z using WithBot.recBotCoe with
  | bot => exact absurd h (WithBot.not_coe_le_bot q)
  | coe r => exact ⟨r, rfl⟩

/-- If the least upper bound of `s` is a coercion, the base of `s` is nonempty:
otherwise `s ⊆ {⊥}` and `⊥` would be an upper bound above a coercion. -/
theorem sumBase_nonempty_of_isLUB_coe {s : Set (CoalescedSum α β)} {r : NonBotSum α β}
    (h : IsLUB s (↑r : CoalescedSum α β)) : (sumBase s).Nonempty := by
  rcases Set.eq_empty_or_nonempty (sumBase s) with hemp | hne
  · refine absurd (h.2 fun z hz => ?_) (WithBot.not_coe_le_bot r)
    induction z using WithBot.recBotCoe with
    | bot => exact le_rfl
    | coe q => exact absurd (show q ∈ sumBase s from hz) (by simp [hemp])
  · exact hne

/-- **A least upper bound that is a left injection restricts to one on the left
parts.** For the "least" half, an upper bound `c` of the left parts is not `⊥`
(some left part is not), so `↑(inl c)` is an element of `D ⊕ E` and an upper bound
of `s` — which is where the base being pinned to the left summand is spent. -/
theorem isLUB_leftParts_of_isLUB {s : Set (CoalescedSum α β)} {r : NonBotSum α β} {xr : α}
    (hr : r.val = Sum.inl xr) (h : IsLUB s (↑r : CoalescedSum α β)) :
    IsLUB (leftParts (sumBase s)) xr := by
  obtain ⟨q₀, hq₀⟩ := sumBase_nonempty_of_isLUB_coe h
  have hle : ∀ q ∈ sumBase s, ∃ x : α, q.val = Sum.inl x ∧ x ≤ xr := by
    intro q hq
    have h1 : q.val ≤ r.val :=
      (WithBot.coe_le_coe (α := NonBotSum α β)).mp (h.1 (coe_mem_of_mem_sumBase hq))
    rw [hr] at h1
    exact exists_inl_of_le_inl h1
  constructor
  · rintro x ⟨q, hq, hqx⟩
    obtain ⟨x', hx', hle'⟩ := hle q hq
    rw [hqx] at hx'
    exact (Sum.inl_injective hx'.symm) ▸ hle'
  · intro c hc
    obtain ⟨x₀, hx₀, _⟩ := hle q₀ hq₀
    have hcbot : c ≠ ⊥ := fun hb =>
      ne_bot_of_val_eq_inl hx₀ (le_bot_iff.mp ((hc ⟨q₀, hq₀, hx₀⟩).trans_eq hb))
    have hub : (↑(⟨Sum.inl c, hcbot⟩ : NonBotSum α β) : CoalescedSum α β) ∈ upperBounds s := by
      intro z hz
      induction z using WithBot.recBotCoe with
      | bot => exact bot_le
      | coe q =>
        refine (WithBot.coe_le_coe (α := NonBotSum α β)).mpr ?_
        show q.val ≤ Sum.inl c
        obtain ⟨x, hx, _⟩ := hle q hz
        rw [hx]
        exact Sum.inl_le_inl_iff.mpr (hc ⟨q, hz, hx⟩)
    have h2 : r.val ≤ Sum.inl c := (WithBot.coe_le_coe (α := NonBotSum α β)).mp (h.2 hub)
    rw [hr] at h2
    exact Sum.inl_le_inl_iff.mp h2

/-- The mirror image of `isLUB_leftParts_of_isLUB`. -/
theorem isLUB_rightParts_of_isLUB {s : Set (CoalescedSum α β)} {r : NonBotSum α β} {yr : β}
    (hr : r.val = Sum.inr yr) (h : IsLUB s (↑r : CoalescedSum α β)) :
    IsLUB (rightParts (sumBase s)) yr := by
  obtain ⟨q₀, hq₀⟩ := sumBase_nonempty_of_isLUB_coe h
  have hle : ∀ q ∈ sumBase s, ∃ y : β, q.val = Sum.inr y ∧ y ≤ yr := by
    intro q hq
    have h1 : q.val ≤ r.val :=
      (WithBot.coe_le_coe (α := NonBotSum α β)).mp (h.1 (coe_mem_of_mem_sumBase hq))
    rw [hr] at h1
    exact exists_inr_of_le_inr h1
  constructor
  · rintro y ⟨q, hq, hqy⟩
    obtain ⟨y', hy', hle'⟩ := hle q hq
    rw [hqy] at hy'
    exact (Sum.inr_injective hy'.symm) ▸ hle'
  · intro c hc
    obtain ⟨y₀, hy₀, _⟩ := hle q₀ hq₀
    have hcbot : c ≠ ⊥ := fun hb =>
      ne_bot_of_val_eq_inr hy₀ (le_bot_iff.mp ((hc ⟨q₀, hq₀, hy₀⟩).trans_eq hb))
    have hub : (↑(⟨Sum.inr c, hcbot⟩ : NonBotSum α β) : CoalescedSum α β) ∈ upperBounds s := by
      intro z hz
      induction z using WithBot.recBotCoe with
      | bot => exact bot_le
      | coe q =>
        refine (WithBot.coe_le_coe (α := NonBotSum α β)).mpr ?_
        show q.val ≤ Sum.inr c
        obtain ⟨y, hy, _⟩ := hle q hz
        rw [hy]
        exact Sum.inr_le_inr_iff.mpr (hc ⟨q, hz, hy⟩)
    have h2 : r.val ≤ Sum.inr c := (WithBot.coe_le_coe (α := NonBotSum α β)).mp (h.2 hub)
    rw [hr] at h2
    exact Sum.inr_le_inr_iff.mp h2

/-- **`↑(inl x)` is compact in `D ⊕ E` exactly when `x` is compact in `D`.**
Forward: transport a directed set of `D` into `D ⊕ E` by `sumInl`, having first
deleted `⊥_D`, which `sumInl` does not carry into the sum. Backward: the base of a
directed set with least upper bound `↑r` has left parts directed with least upper
bound `r`'s value, and compactness of `x` there produces the member of the base. -/
theorem isCompactElement_coe_inl_iff {r : NonBotSum α β} {x : α} (hr : r.val = Sum.inl x) :
    IsCompactElement (↑r : CoalescedSum α β) ↔ IsCompactElement x := by
  constructor
  · intro h s u _hne hdir hlub hxu
    have hx : x ≠ ⊥ := ne_bot_of_val_eq_inl hr
    have hu : u ≠ ⊥ := fun hb => hx (le_bot_iff.mp (hxu.trans_eq hb))
    obtain ⟨hne', hdir', hlub'⟩ := isLUB_diff_bot hdir hlub hu
    have hle : (↑r : CoalescedSum α β) ≤ sumInl β u := by
      rw [sumInl_of_ne_bot hu]
      refine (WithBot.coe_le_coe (α := NonBotSum α β)).mpr ?_
      show r.val ≤ Sum.inl u
      rw [hr]
      exact Sum.inl_le_inl_iff.mpr hxu
    obtain ⟨_, ⟨a, ha, rfl⟩, hrz⟩ :=
      h _ _ (hne'.image _) (directedOn_image_sumInl hdir')
        (isLUB_image_sumInl hne' (fun _ hb => hb.2) hu hlub') hle
    refine ⟨a, ha.1, ?_⟩
    rw [sumInl_of_ne_bot ha.2] at hrz
    have h2 : r.val ≤ Sum.inl a := (WithBot.coe_le_coe (α := NonBotSum α β)).mp hrz
    rw [hr] at h2
    exact Sum.inl_le_inl_iff.mp h2
  · intro hx S w hSne hSdir hSlub hrw
    obtain ⟨t, rfl⟩ := exists_coe_of_coe_le hrw
    have h1 : r.val ≤ t.val := (WithBot.coe_le_coe (α := NonBotSum α β)).mp hrw
    rw [hr] at h1
    obtain ⟨xt, hxt, hxxt⟩ := exists_inl_of_inl_le h1
    have hne' : (leftParts (sumBase S)).Nonempty := by
      obtain ⟨q₀, hq₀⟩ := sumBase_nonempty_of_isLUB_coe hSlub
      have h2 : q₀.val ≤ t.val :=
        (WithBot.coe_le_coe (α := NonBotSum α β)).mp (hSlub.1 (coe_mem_of_mem_sumBase hq₀))
      rw [hxt] at h2
      obtain ⟨x₀, hx₀, _⟩ := exists_inl_of_le_inl h2
      exact ⟨x₀, q₀, hq₀, hx₀⟩
    obtain ⟨x', ⟨q, hq, hqx⟩, hxx'⟩ :=
      hx _ xt hne' (directedOn_leftParts (directedOn_sumBase hSdir))
        (isLUB_leftParts_of_isLUB hxt hSlub) hxxt
    refine ⟨↑q, coe_mem_of_mem_sumBase hq, ?_⟩
    refine (WithBot.coe_le_coe (α := NonBotSum α β)).mpr ?_
    show r.val ≤ q.val
    rw [hr, hqx]
    exact Sum.inl_le_inl_iff.mpr hxx'

/-- The mirror image of `isCompactElement_coe_inl_iff`. -/
theorem isCompactElement_coe_inr_iff {r : NonBotSum α β} {y : β} (hr : r.val = Sum.inr y) :
    IsCompactElement (↑r : CoalescedSum α β) ↔ IsCompactElement y := by
  constructor
  · intro h s u _hne hdir hlub hyu
    have hy : y ≠ ⊥ := ne_bot_of_val_eq_inr hr
    have hu : u ≠ ⊥ := fun hb => hy (le_bot_iff.mp (hyu.trans_eq hb))
    obtain ⟨hne', hdir', hlub'⟩ := isLUB_diff_bot hdir hlub hu
    have hle : (↑r : CoalescedSum α β) ≤ sumInr α u := by
      rw [sumInr_of_ne_bot hu]
      refine (WithBot.coe_le_coe (α := NonBotSum α β)).mpr ?_
      show r.val ≤ Sum.inr u
      rw [hr]
      exact Sum.inr_le_inr_iff.mpr hyu
    obtain ⟨_, ⟨a, ha, rfl⟩, hrz⟩ :=
      h _ _ (hne'.image _) (directedOn_image_sumInr hdir')
        (isLUB_image_sumInr hne' (fun _ hb => hb.2) hu hlub') hle
    refine ⟨a, ha.1, ?_⟩
    rw [sumInr_of_ne_bot ha.2] at hrz
    have h2 : r.val ≤ Sum.inr a := (WithBot.coe_le_coe (α := NonBotSum α β)).mp hrz
    rw [hr] at h2
    exact Sum.inr_le_inr_iff.mp h2
  · intro hy S w hSne hSdir hSlub hrw
    obtain ⟨t, rfl⟩ := exists_coe_of_coe_le hrw
    have h1 : r.val ≤ t.val := (WithBot.coe_le_coe (α := NonBotSum α β)).mp hrw
    rw [hr] at h1
    obtain ⟨yt, hyt, hyyt⟩ := exists_inr_of_inr_le h1
    have hne' : (rightParts (sumBase S)).Nonempty := by
      obtain ⟨q₀, hq₀⟩ := sumBase_nonempty_of_isLUB_coe hSlub
      have h2 : q₀.val ≤ t.val :=
        (WithBot.coe_le_coe (α := NonBotSum α β)).mp (hSlub.1 (coe_mem_of_mem_sumBase hq₀))
      rw [hyt] at h2
      obtain ⟨y₀, hy₀, _⟩ := exists_inr_of_le_inr h2
      exact ⟨y₀, q₀, hq₀, hy₀⟩
    obtain ⟨y', ⟨q, hq, hqy⟩, hyy'⟩ :=
      hy _ yt hne' (directedOn_rightParts (directedOn_sumBase hSdir))
        (isLUB_rightParts_of_isLUB hyt hSlub) hyyt
    refine ⟨↑q, coe_mem_of_mem_sumBase hq, ?_⟩
    refine (WithBot.coe_le_coe (α := NonBotSum α β)).mpr ?_
    show r.val ≤ q.val
    rw [hr, hqy]
    exact Sum.inr_le_inr_iff.mpr hyy'

/-! ### Lemma 17, the `D + E` conjunct -/

/-- The subset of `D ⊕ E` built from `N₁ ⊆ D` and `N₂ ⊆ E`: the adjoined bottom
together with the injections of `N₁` and of `N₂`. Stated as a comprehension rather
than as `insert ⊥ (sumInl '' N₁ ∪ sumInr '' N₂)` because membership is then
directly the case distinction the normality proof runs on; finiteness is recovered
by `finite_sumNormal`, which compares it with that image. -/
def sumNormal (N₁ : Set α) (N₂ : Set β) : Set (CoalescedSum α β) :=
  {z | z = ⊥ ∨ ∃ q : NonBotSum α β, z = ↑q ∧
    ((∃ x, q.val = Sum.inl x ∧ x ∈ N₁) ∨ ∃ y, q.val = Sum.inr y ∧ y ∈ N₂)}

theorem finite_sumNormal {N₁ : Set α} {N₂ : Set β} (h₁ : N₁.Finite) (h₂ : N₂.Finite) :
    (sumNormal N₁ N₂ : Set (CoalescedSum α β)).Finite := by
  refine Set.Finite.subset
    (((h₁.image (sumInl β)).union (h₂.image (sumInr α))).insert ⊥) ?_
  rintro z (rfl | ⟨q, rfl, ⟨x, hx, hxN⟩ | ⟨y, hy, hyN⟩⟩)
  · exact Set.mem_insert _ _
  · refine Set.mem_insert_of_mem _ (Or.inl ⟨x, hxN, ?_⟩)
    rw [sumInl_of_ne_bot (ne_bot_of_val_eq_inl hx)]
    congr 1
    exact Subtype.ext hx.symm
  · refine Set.mem_insert_of_mem _ (Or.inr ⟨y, hyN, ?_⟩)
    rw [sumInr_of_ne_bot (ne_bot_of_val_eq_inr hy)]
    congr 1
    exact Subtype.ext hy.symm

/-- **Lemma 17, `D + E`.** Pull `u` back along each injection — both are injective,
so both preimages are finite — expand each to a finite normal subposet of its
summand's basis, and take the injections of the two together with `⊥`.

Normality is where the coalesced sum is *easier* than the product: two elements of
`N ∩ ↓z` other than `⊥` force `z` to be a coercion, and then everything in sight
lies in one summand, so directedness is inherited from that summand's `N ◁ K(D)`
with no rectangle to build. -/
theorem lemma_17_sum [Domain α] [Domain β] (_h₁ : IsBifinite α) (_h₂ : IsBifinite β) :
    IsBifinite (CoalescedSum α β) := by
  intro u hu husub
  have hfinL : ((sumInl β : α → CoalescedSum α β) ⁻¹' u).Finite :=
    hu.preimage fun _ _ _ _ h => injective_sumInl h
  have hfinR : ((sumInr α : β → CoalescedSum α β) ⁻¹' u).Finite :=
    hu.preimage fun _ _ _ _ h => injective_sumInr h
  have hsubL : (sumInl β : α → CoalescedSum α β) ⁻¹' u ⊆ compacts α := by
    intro x hx
    by_cases hxb : x = ⊥
    · rw [hxb]
      exact isCompactElement_bot
    · have hc : IsCompactElement (sumInl β x) := husub hx
      rw [sumInl_of_ne_bot hxb] at hc
      exact (isCompactElement_coe_inl_iff (r := ⟨Sum.inl x, hxb⟩) rfl).mp hc
  have hsubR : (sumInr α : β → CoalescedSum α β) ⁻¹' u ⊆ compacts β := by
    intro y hy
    by_cases hyb : y = ⊥
    · rw [hyb]
      exact isCompactElement_bot
    · have hc : IsCompactElement (sumInr α y) := husub hy
      rw [sumInr_of_ne_bot hyb] at hc
      exact (isCompactElement_coe_inr_iff (r := ⟨Sum.inr y, hyb⟩) rfl).mp hc
  obtain ⟨N₁, hN₁fin, hN₁, hN₁sub⟩ := _h₁ _ hfinL hsubL
  obtain ⟨N₂, hN₂fin, hN₂, hN₂sub⟩ := _h₂ _ hfinR hsubR
  refine ⟨sumNormal N₁ N₂, finite_sumNormal hN₁fin hN₂fin, ⟨?_, ?_⟩, ?_⟩
  · rintro z (rfl | ⟨q, rfl, ⟨x, hx, hxN⟩ | ⟨y, hy, hyN⟩⟩)
    · exact isCompactElement_bot
    · exact (isCompactElement_coe_inl_iff hx).mpr (hN₁.subset hxN)
    · exact (isCompactElement_coe_inr_iff hy).mpr (hN₂.subset hyN)
  · intro z hz
    refine ⟨⟨⊥, Or.inl rfl, Set.mem_Iic.mpr bot_le⟩, ?_⟩
    rintro a ⟨haN, haz⟩ b ⟨hbN, hbz⟩
    rcases haN with rfl | ⟨qa, rfl, ha⟩
    · exact ⟨b, ⟨hbN, hbz⟩, bot_le, le_rfl⟩
    rcases hbN with rfl | ⟨qb, rfl, hb⟩
    · exact ⟨↑qa, ⟨Or.inr ⟨qa, rfl, ha⟩, haz⟩, le_rfl, bot_le⟩
    obtain ⟨r, rfl⟩ := exists_coe_of_coe_le haz
    have hqar : qa.val ≤ r.val := (WithBot.coe_le_coe (α := NonBotSum α β)).mp haz
    have hqbr : qb.val ≤ r.val := (WithBot.coe_le_coe (α := NonBotSum α β)).mp hbz
    rcases ha with ⟨xa, hxa, hxaN⟩ | ⟨ya, hya, hyaN⟩
    · rw [hxa] at hqar
      obtain ⟨xr, hxr, hxaxr⟩ := exists_inl_of_inl_le hqar
      obtain ⟨xb, hxb, hxbN⟩ : ∃ xb, qb.val = Sum.inl xb ∧ xb ∈ N₁ := by
        rcases hb with ⟨xb, hxb, hxbN⟩ | ⟨yb, hyb, _⟩
        · exact ⟨xb, hxb, hxbN⟩
        · rw [hyb, hxr] at hqbr
          exact absurd hqbr (by simp)
      rw [hxb, hxr] at hqbr
      have hxrc : IsCompactElement xr := (isCompactElement_coe_inl_iff hxr).mp hz
      obtain ⟨c, ⟨hcN, hcxr⟩, hac, hbc⟩ :=
        hN₁.directedOn hxrc xa ⟨hxaN, Set.mem_Iic.mpr hxaxr⟩ xb
          ⟨hxbN, Set.mem_Iic.mpr (Sum.inl_le_inl_iff.mp hqbr)⟩
      have hcbot : c ≠ ⊥ := fun hb' =>
        ne_bot_of_val_eq_inl hxa (le_bot_iff.mp (hac.trans_eq hb'))
      refine ⟨↑(⟨Sum.inl c, hcbot⟩ : NonBotSum α β),
        ⟨Or.inr ⟨_, rfl, Or.inl ⟨c, rfl, hcN⟩⟩, Set.mem_Iic.mpr ?_⟩, ?_, ?_⟩
      · refine (WithBot.coe_le_coe (α := NonBotSum α β)).mpr ?_
        show Sum.inl c ≤ r.val
        rw [hxr]
        exact Sum.inl_le_inl_iff.mpr (Set.mem_Iic.mp hcxr)
      · refine (WithBot.coe_le_coe (α := NonBotSum α β)).mpr ?_
        show qa.val ≤ Sum.inl c
        rw [hxa]
        exact Sum.inl_le_inl_iff.mpr hac
      · refine (WithBot.coe_le_coe (α := NonBotSum α β)).mpr ?_
        show qb.val ≤ Sum.inl c
        rw [hxb]
        exact Sum.inl_le_inl_iff.mpr hbc
    · rw [hya] at hqar
      obtain ⟨yr, hyr, hyayr⟩ := exists_inr_of_inr_le hqar
      obtain ⟨yb, hyb, hybN⟩ : ∃ yb, qb.val = Sum.inr yb ∧ yb ∈ N₂ := by
        rcases hb with ⟨xb, hxb, _⟩ | ⟨yb, hyb, hybN⟩
        · rw [hxb, hyr] at hqbr
          exact absurd hqbr (by simp)
        · exact ⟨yb, hyb, hybN⟩
      rw [hyb, hyr] at hqbr
      have hyrc : IsCompactElement yr := (isCompactElement_coe_inr_iff hyr).mp hz
      obtain ⟨c, ⟨hcN, hcyr⟩, hac, hbc⟩ :=
        hN₂.directedOn hyrc ya ⟨hyaN, Set.mem_Iic.mpr hyayr⟩ yb
          ⟨hybN, Set.mem_Iic.mpr (Sum.inr_le_inr_iff.mp hqbr)⟩
      have hcbot : c ≠ ⊥ := fun hb' =>
        ne_bot_of_val_eq_inr hya (le_bot_iff.mp (hac.trans_eq hb'))
      refine ⟨↑(⟨Sum.inr c, hcbot⟩ : NonBotSum α β),
        ⟨Or.inr ⟨_, rfl, Or.inr ⟨c, rfl, hcN⟩⟩, Set.mem_Iic.mpr ?_⟩, ?_, ?_⟩
      · refine (WithBot.coe_le_coe (α := NonBotSum α β)).mpr ?_
        show Sum.inr c ≤ r.val
        rw [hyr]
        exact Sum.inr_le_inr_iff.mpr (Set.mem_Iic.mp hcyr)
      · refine (WithBot.coe_le_coe (α := NonBotSum α β)).mpr ?_
        show qa.val ≤ Sum.inr c
        rw [hya]
        exact Sum.inr_le_inr_iff.mpr hac
      · refine (WithBot.coe_le_coe (α := NonBotSum α β)).mpr ?_
        show qb.val ≤ Sum.inr c
        rw [hyb]
        exact Sum.inr_le_inr_iff.mpr hbc
  · intro z hz
    induction z using WithBot.recBotCoe with
    | bot => exact Or.inl rfl
    | coe q =>
      refine Or.inr ⟨q, rfl, ?_⟩
      cases hq : q.val with
      | inl x =>
        refine Or.inl ⟨x, rfl, hN₁sub ?_⟩
        show sumInl β x ∈ u
        rw [sumInl_of_ne_bot (ne_bot_of_val_eq_inl hq)]
        have hqe : (⟨Sum.inl x, ne_bot_of_val_eq_inl hq⟩ : NonBotSum α β) = q :=
          Subtype.ext hq.symm
        rw [hqe]
        exact hz
      | inr y =>
        refine Or.inr ⟨y, rfl, hN₂sub ?_⟩
        show sumInr α y ∈ u
        rw [sumInr_of_ne_bot (ne_bot_of_val_eq_inr hq)]
        have hqe : (⟨Sum.inr y, ne_bot_of_val_eq_inr hq⟩ : NonBotSum α β) = q :=
          Subtype.ext hq.symm
        rw [hqe]
        exact hz

/-! ### The pairing of `D ⊗ E`, made total

`Prod.mk` does not land in `D ⊗ E` either: a pair with a `⊥` coordinate was
identified with the new bottom. `smashPair` sends every such pair there. -/

open Classical in
/-- The pairing `D × E → D ⊗ E`, with every pair having a `⊥` coordinate sent to
`⊥_{D⊗E}`. -/
noncomputable def smashPair (p : α × β) : Smash α β :=
  if h : p.1 ≠ ⊥ ∧ p.2 ≠ ⊥ then ↑(⟨p, h⟩ : NonBotPair α β) else ⊥

theorem smashPair_of_ne_bot {p : α × β} (h : p.1 ≠ ⊥ ∧ p.2 ≠ ⊥) :
    smashPair p = ↑(⟨p, h⟩ : NonBotPair α β) := by
  classical simp only [smashPair, dif_pos h]

theorem smashPair_of_bot {p : α × β} (h : ¬ (p.1 ≠ ⊥ ∧ p.2 ≠ ⊥)) :
    smashPair p = (⊥ : Smash α β) := by
  classical simp only [smashPair, dif_neg h]

theorem monotone_smashPair_left (b : β) :
    Monotone (fun a : α => smashPair ((a, b) : α × β)) := by
  intro a a' haa'
  show smashPair ((a, b) : α × β) ≤ smashPair ((a', b) : α × β)
  by_cases h : a ≠ ⊥ ∧ b ≠ ⊥
  · have ha' : a' ≠ ⊥ := fun hb => h.1 (le_bot_iff.mp (haa'.trans_eq hb))
    rw [smashPair_of_ne_bot (p := (a, b)) h, smashPair_of_ne_bot (p := (a', b)) ⟨ha', h.2⟩]
    refine (WithBot.coe_le_coe (α := NonBotPair α β)).mpr ?_
    show ((a, b) : α × β) ≤ (a', b)
    exact ⟨haa', le_rfl⟩
  · rw [smashPair_of_bot (p := (a, b)) h]
    exact bot_le

theorem monotone_smashPair_right (a : α) :
    Monotone (fun b : β => smashPair ((a, b) : α × β)) := by
  intro b b' hbb'
  show smashPair ((a, b) : α × β) ≤ smashPair ((a, b') : α × β)
  by_cases h : a ≠ ⊥ ∧ b ≠ ⊥
  · have hb' : b' ≠ ⊥ := fun hb => h.2 (le_bot_iff.mp (hbb'.trans_eq hb))
    rw [smashPair_of_ne_bot (p := (a, b)) h, smashPair_of_ne_bot (p := (a, b')) ⟨h.1, hb'⟩]
    refine (WithBot.coe_le_coe (α := NonBotPair α β)).mpr ?_
    show ((a, b) : α × β) ≤ (a, b')
    exact ⟨le_rfl, hbb'⟩
  · rw [smashPair_of_bot (p := (a, b)) h]
    exact bot_le

theorem directedOn_image_smashPair_left {s : Set α} (b : β) (hdir : DirectedOn (· ≤ ·) s) :
    DirectedOn (· ≤ ·) ((fun a : α => smashPair ((a, b) : α × β)) '' s) := by
  rintro _ ⟨a₁, h₁, rfl⟩ _ ⟨a₂, h₂, rfl⟩
  obtain ⟨c, hc, hc₁, hc₂⟩ := hdir a₁ h₁ a₂ h₂
  exact ⟨smashPair (c, b), ⟨c, hc, rfl⟩, monotone_smashPair_left b hc₁,
    monotone_smashPair_left b hc₂⟩

theorem directedOn_image_smashPair_right {s : Set β} (a : α) (hdir : DirectedOn (· ≤ ·) s) :
    DirectedOn (· ≤ ·) ((fun b : β => smashPair ((a, b) : α × β)) '' s) := by
  rintro _ ⟨b₁, h₁, rfl⟩ _ ⟨b₂, h₂, rfl⟩
  obtain ⟨c, hc, hc₁, hc₂⟩ := hdir b₁ h₁ b₂ h₂
  exact ⟨smashPair (a, c), ⟨c, hc, rfl⟩, monotone_smashPair_right a hc₁,
    monotone_smashPair_right a hc₂⟩

/-- Pairing a set of non-`⊥` elements of `D` with a fixed non-`⊥` `b` carries its
least upper bound to the least upper bound of the image. -/
theorem isLUB_image_smashPair_left {s : Set α} {u : α} {b : β} (hne : s.Nonempty)
    (hbot : ∀ a ∈ s, a ≠ ⊥) (hu : u ≠ ⊥) (hb : b ≠ ⊥) (hlub : IsLUB s u) :
    IsLUB ((fun a : α => smashPair ((a, b) : α × β)) '' s) (smashPair (u, b)) := by
  obtain ⟨a₀, ha₀⟩ := hne
  constructor
  · rintro _ ⟨a, ha, rfl⟩
    exact monotone_smashPair_left b (hlub.1 ha)
  · intro v hv
    have hv₀ : smashPair ((a₀, b) : α × β) ≤ v := hv ⟨a₀, ha₀, rfl⟩
    rw [smashPair_of_ne_bot (p := (a₀, b)) ⟨hbot a₀ ha₀, hb⟩] at hv₀
    obtain ⟨t, rfl⟩ : ∃ t : NonBotPair α β, v = ↑t := by
      induction v using WithBot.recBotCoe with
      | bot => exact absurd hv₀ (WithBot.not_coe_le_bot _)
      | coe t => exact ⟨t, rfl⟩
    have h₀ : ((a₀, b) : α × β) ≤ t.val := (WithBot.coe_le_coe (α := NonBotPair α β)).mp hv₀
    rw [smashPair_of_ne_bot (p := (u, b)) ⟨hu, hb⟩]
    refine (WithBot.coe_le_coe (α := NonBotPair α β)).mpr ?_
    show ((u, b) : α × β) ≤ t.val
    refine ⟨hlub.2 fun a ha => ?_, h₀.2⟩
    have hva : smashPair ((a, b) : α × β) ≤ (↑t : Smash α β) := hv ⟨a, ha, rfl⟩
    rw [smashPair_of_ne_bot (p := (a, b)) ⟨hbot a ha, hb⟩] at hva
    exact ((WithBot.coe_le_coe (α := NonBotPair α β)).mp hva).1

/-- The mirror image of `isLUB_image_smashPair_left`, in the second coordinate. -/
theorem isLUB_image_smashPair_right {s : Set β} {u : β} {a : α} (hne : s.Nonempty)
    (hbot : ∀ b ∈ s, b ≠ ⊥) (hu : u ≠ ⊥) (ha : a ≠ ⊥) (hlub : IsLUB s u) :
    IsLUB ((fun b : β => smashPair ((a, b) : α × β)) '' s) (smashPair (a, u)) := by
  obtain ⟨b₀, hb₀⟩ := hne
  constructor
  · rintro _ ⟨b, hb, rfl⟩
    exact monotone_smashPair_right a (hlub.1 hb)
  · intro v hv
    have hv₀ : smashPair ((a, b₀) : α × β) ≤ v := hv ⟨b₀, hb₀, rfl⟩
    rw [smashPair_of_ne_bot (p := (a, b₀)) ⟨ha, hbot b₀ hb₀⟩] at hv₀
    obtain ⟨t, rfl⟩ : ∃ t : NonBotPair α β, v = ↑t := by
      induction v using WithBot.recBotCoe with
      | bot => exact absurd hv₀ (WithBot.not_coe_le_bot _)
      | coe t => exact ⟨t, rfl⟩
    have h₀ : ((a, b₀) : α × β) ≤ t.val := (WithBot.coe_le_coe (α := NonBotPair α β)).mp hv₀
    rw [smashPair_of_ne_bot (p := (a, u)) ⟨ha, hu⟩]
    refine (WithBot.coe_le_coe (α := NonBotPair α β)).mpr ?_
    show ((a, u) : α × β) ≤ t.val
    refine ⟨h₀.1, hlub.2 fun b hb => ?_⟩
    have hvb : smashPair ((a, b) : α × β) ≤ (↑t : Smash α β) := hv ⟨b, hb, rfl⟩
    rw [smashPair_of_ne_bot (p := (a, b)) ⟨ha, hbot b hb⟩] at hvb
    exact ((WithBot.coe_le_coe (α := NonBotPair α β)).mp hvb).2

/-! ### The basis of `D ⊗ E`

`K(D ⊗ E) = {⊥} ∪ (K(D)∖{⊥}) × (K(E)∖{⊥})`. -/

theorem exists_coe_of_coe_le_smash {q : NonBotPair α β} {z : Smash α β}
    (h : (↑q : Smash α β) ≤ z) : ∃ r : NonBotPair α β, z = ↑r := by
  induction z using WithBot.recBotCoe with
  | bot => exact absurd h (WithBot.not_coe_le_bot q)
  | coe r => exact ⟨r, rfl⟩

theorem smashBase_nonempty_of_isLUB_coe {s : Set (Smash α β)} {r : NonBotPair α β}
    (h : IsLUB s (↑r : Smash α β)) : (smashBase s).Nonempty := by
  rcases Set.eq_empty_or_nonempty (smashBase s) with hemp | hne
  · refine absurd (h.2 fun z hz => ?_) (WithBot.not_coe_le_bot r)
    induction z using WithBot.recBotCoe with
    | bot => exact le_rfl
    | coe q => exact absurd (show q ∈ smashBase s from hz) (by simp [hemp])
  · exact hne

/-- **A least upper bound that is a coerced pair restricts to one on the base's
image.** An upper bound `v` of that image in `D × E` has neither coordinate `⊥`,
since it dominates a member of the base, so `↑v` is an element of `D ⊗ E` and an
upper bound of `s`. -/
theorem isLUB_val_smashBase_of_isLUB {s : Set (Smash α β)} {r : NonBotPair α β}
    (h : IsLUB s (↑r : Smash α β)) : IsLUB (Subtype.val '' smashBase s) r.val := by
  obtain ⟨q₀, hq₀⟩ := smashBase_nonempty_of_isLUB_coe h
  have hle : ∀ q ∈ smashBase s, q.val ≤ r.val := fun q hq =>
    (WithBot.coe_le_coe (α := NonBotPair α β)).mp (h.1 (coe_mem_of_mem_smashBase hq))
  constructor
  · rintro _ ⟨q, hq, rfl⟩
    exact hle q hq
  · intro v hv
    have hv₀ : q₀.val ≤ v := hv ⟨q₀, hq₀, rfl⟩
    have hvbot : v.1 ≠ ⊥ ∧ v.2 ≠ ⊥ :=
      ⟨fun hb => q₀.2.1 (le_bot_iff.mp (hv₀.1.trans_eq hb)),
        fun hb => q₀.2.2 (le_bot_iff.mp (hv₀.2.trans_eq hb))⟩
    have hub : (↑(⟨v, hvbot⟩ : NonBotPair α β) : Smash α β) ∈ upperBounds s := by
      intro z hz
      induction z using WithBot.recBotCoe with
      | bot => exact bot_le
      | coe q =>
        refine (WithBot.coe_le_coe (α := NonBotPair α β)).mpr ?_
        show q.val ≤ v
        exact hv ⟨q, hz, rfl⟩
    exact (WithBot.coe_le_coe (α := NonBotPair α β)).mp (h.2 hub)

/-- **`↑(x, y)` is compact in `D ⊗ E` exactly when `x` and `y` are compact.**
Forward, in the first coordinate: pair a directed set of `D` with the fixed `y`,
having first deleted `⊥_D`, and read off the witness. Backward: the base's image
has least upper bound `r`'s value, so each coordinate image has that coordinate as
its least upper bound (`isLUB_prod`); compactness in each coordinate produces a
member of the base, and directedness of the base merges the two. -/
theorem isCompactElement_coe_smash_iff {p : NonBotPair α β} :
    IsCompactElement (↑p : Smash α β) ↔ IsCompactElement p.val.1 ∧ IsCompactElement p.val.2 := by
  constructor
  · intro h
    constructor
    · intro s u _hne hdir hlub hxu
      have hu : u ≠ ⊥ := fun hb => p.2.1 (le_bot_iff.mp (hxu.trans_eq hb))
      obtain ⟨hne', hdir', hlub'⟩ := isLUB_diff_bot hdir hlub hu
      have hle : (↑p : Smash α β) ≤ smashPair (u, p.val.2) := by
        rw [smashPair_of_ne_bot (p := (u, p.val.2)) ⟨hu, p.2.2⟩]
        refine (WithBot.coe_le_coe (α := NonBotPair α β)).mpr ?_
        show p.val ≤ ((u, p.val.2) : α × β)
        exact ⟨hxu, le_rfl⟩
      obtain ⟨_, ⟨a, ha, rfl⟩, hpz⟩ :=
        h _ _ (hne'.image _) (directedOn_image_smashPair_left _ hdir')
          (isLUB_image_smashPair_left hne' (fun _ hb => hb.2) hu p.2.2 hlub') hle
      refine ⟨a, ha.1, ?_⟩
      have hpz' : (↑p : Smash α β) ≤ smashPair ((a, p.val.2) : α × β) := hpz
      rw [smashPair_of_ne_bot (p := (a, p.val.2)) ⟨ha.2, p.2.2⟩] at hpz'
      exact ((WithBot.coe_le_coe (α := NonBotPair α β)).mp hpz').1
    · intro s u _hne hdir hlub hyu
      have hu : u ≠ ⊥ := fun hb => p.2.2 (le_bot_iff.mp (hyu.trans_eq hb))
      obtain ⟨hne', hdir', hlub'⟩ := isLUB_diff_bot hdir hlub hu
      have hle : (↑p : Smash α β) ≤ smashPair (p.val.1, u) := by
        rw [smashPair_of_ne_bot (p := (p.val.1, u)) ⟨p.2.1, hu⟩]
        refine (WithBot.coe_le_coe (α := NonBotPair α β)).mpr ?_
        show p.val ≤ ((p.val.1, u) : α × β)
        exact ⟨le_rfl, hyu⟩
      obtain ⟨_, ⟨b, hb, rfl⟩, hpz⟩ :=
        h _ _ (hne'.image _) (directedOn_image_smashPair_right _ hdir')
          (isLUB_image_smashPair_right hne' (fun _ hb' => hb'.2) hu p.2.1 hlub') hle
      refine ⟨b, hb.1, ?_⟩
      have hpz' : (↑p : Smash α β) ≤ smashPair ((p.val.1, b) : α × β) := hpz
      rw [smashPair_of_ne_bot (p := (p.val.1, b)) ⟨p.2.1, hb.2⟩] at hpz'
      exact ((WithBot.coe_le_coe (α := NonBotPair α β)).mp hpz').2
  · rintro ⟨h₁, h₂⟩ S w hSne hSdir hSlub hpw
    obtain ⟨t, rfl⟩ := exists_coe_of_coe_le_smash hpw
    have hpt : p.val ≤ t.val := (WithBot.coe_le_coe (α := NonBotPair α β)).mp hpw
    obtain ⟨q₀, hq₀⟩ := smashBase_nonempty_of_isLUB_coe hSlub
    have hbdir : DirectedOn (· ≤ ·) (smashBase S) := directedOn_smashBase hSdir
    have hvdir : DirectedOn (· ≤ ·) (Subtype.val '' smashBase S) :=
      directedOn_val_smashBase hbdir
    have hvne : (Subtype.val '' smashBase S).Nonempty := ⟨q₀.val, q₀, hq₀, rfl⟩
    have hvlub : IsLUB (Subtype.val '' smashBase S) t.val := isLUB_val_smashBase_of_isLUB hSlub
    rw [isLUB_prod] at hvlub
    obtain ⟨_, ⟨_, ⟨q₁, hq₁, rfl⟩, rfl⟩, hle₁⟩ :=
      h₁ _ t.val.1 (hvne.image _) (directedOn_fst_image hvdir) hvlub.1 hpt.1
    obtain ⟨_, ⟨_, ⟨q₂, hq₂, rfl⟩, rfl⟩, hle₂⟩ :=
      h₂ _ t.val.2 (hvne.image _) (directedOn_snd_image hvdir) hvlub.2 hpt.2
    obtain ⟨c, hc, hc₁, hc₂⟩ := hbdir q₁ hq₁ q₂ hq₂
    refine ⟨↑c, coe_mem_of_mem_smashBase hc, ?_⟩
    refine (WithBot.coe_le_coe (α := NonBotPair α β)).mpr ?_
    show p.val ≤ c.val
    exact ⟨hle₁.trans hc₁.1, hle₂.trans hc₂.2⟩

/-! ### Lemma 17, the `D ⊗ E` conjunct -/

/-- The subset of `D ⊗ E` built from `N₁ ⊆ D` and `N₂ ⊆ E`: the adjoined bottom
together with the pairs drawn from `N₁ × N₂` that have neither coordinate `⊥`. -/
def smashNormal (N₁ : Set α) (N₂ : Set β) : Set (Smash α β) :=
  {z | z = ⊥ ∨ ∃ p : NonBotPair α β, z = ↑p ∧ p.val.1 ∈ N₁ ∧ p.val.2 ∈ N₂}

theorem finite_smashNormal {N₁ : Set α} {N₂ : Set β} (h₁ : N₁.Finite) (h₂ : N₂.Finite) :
    (smashNormal N₁ N₂ : Set (Smash α β)).Finite := by
  refine Set.Finite.subset ((Set.Finite.image smashPair (h₁.prod h₂)).insert ⊥) ?_
  rintro z (rfl | ⟨p, rfl, hp₁, hp₂⟩)
  · exact Set.mem_insert _ _
  · refine Set.mem_insert_of_mem _ ⟨p.val, ⟨hp₁, hp₂⟩, ?_⟩
    rw [smashPair_of_ne_bot p.2]

/-- **Lemma 17, `D ⊗ E`.** The base of `u` is finite — the coercion is injective —
so both coordinate images are finite sets of compacts. Expand each to a finite
normal subposet of its factor's basis and take the rectangle of non-`⊥` pairs,
with `⊥` adjoined. Directedness of `N ∩ ↓z` at a coercion `↑r` is coordinatewise,
exactly as in `lemma_17_prod`, once `r`'s coordinates are known compact — which is the
forward direction of `isCompactElement_coe_smash_iff`.

This conjunct was omitted from the r0026 skeleton by oversight; nothing about it
was open. -/
theorem lemma_17_smash [Domain α] [Domain β] (_h₁ : IsBifinite α) (_h₂ : IsBifinite β) :
    IsBifinite (Smash α β) := by
  intro u hu husub
  have hbfin : (smashBase u).Finite := by
    have h : ((fun q : NonBotPair α β => (↑q : Smash α β)) ⁻¹' u).Finite :=
      hu.preimage fun _ _ _ _ h => WithBot.coe_injective h
    exact h
  have hcomp : ∀ q ∈ smashBase u, IsCompactElement q.val.1 ∧ IsCompactElement q.val.2 :=
    fun q hq => isCompactElement_coe_smash_iff.mp (husub (coe_mem_of_mem_smashBase hq))
  have hfin₁ : ((fun q : NonBotPair α β => q.val.1) '' smashBase u).Finite := hbfin.image _
  have hfin₂ : ((fun q : NonBotPair α β => q.val.2) '' smashBase u).Finite := hbfin.image _
  have hsub₁ : (fun q : NonBotPair α β => q.val.1) '' smashBase u ⊆ compacts α := by
    rintro _ ⟨q, hq, rfl⟩
    exact (hcomp q hq).1
  have hsub₂ : (fun q : NonBotPair α β => q.val.2) '' smashBase u ⊆ compacts β := by
    rintro _ ⟨q, hq, rfl⟩
    exact (hcomp q hq).2
  obtain ⟨N₁, hN₁fin, hN₁, hN₁sub⟩ := _h₁ _ hfin₁ hsub₁
  obtain ⟨N₂, hN₂fin, hN₂, hN₂sub⟩ := _h₂ _ hfin₂ hsub₂
  refine ⟨smashNormal N₁ N₂, finite_smashNormal hN₁fin hN₂fin, ⟨?_, ?_⟩, ?_⟩
  · rintro z (rfl | ⟨p, rfl, hp₁, hp₂⟩)
    · exact isCompactElement_bot
    · exact isCompactElement_coe_smash_iff.mpr ⟨hN₁.subset hp₁, hN₂.subset hp₂⟩
  · intro z hz
    refine ⟨⟨⊥, Or.inl rfl, Set.mem_Iic.mpr bot_le⟩, ?_⟩
    rintro a ⟨haN, haz⟩ b ⟨hbN, hbz⟩
    rcases haN with rfl | ⟨pa, rfl, hpa₁, hpa₂⟩
    · exact ⟨b, ⟨hbN, hbz⟩, bot_le, le_rfl⟩
    rcases hbN with rfl | ⟨pb, rfl, hpb₁, hpb₂⟩
    · exact ⟨↑pa, ⟨Or.inr ⟨pa, rfl, hpa₁, hpa₂⟩, haz⟩, le_rfl, bot_le⟩
    obtain ⟨r, rfl⟩ := exists_coe_of_coe_le_smash haz
    have hpar : pa.val ≤ r.val := (WithBot.coe_le_coe (α := NonBotPair α β)).mp haz
    have hpbr : pb.val ≤ r.val := (WithBot.coe_le_coe (α := NonBotPair α β)).mp hbz
    obtain ⟨hr₁, hr₂⟩ := isCompactElement_coe_smash_iff.mp hz
    obtain ⟨c₁, ⟨hc₁N, hc₁r⟩, hac₁, hbc₁⟩ :=
      hN₁.directedOn hr₁ pa.val.1 ⟨hpa₁, Set.mem_Iic.mpr hpar.1⟩ pb.val.1
        ⟨hpb₁, Set.mem_Iic.mpr hpbr.1⟩
    obtain ⟨c₂, ⟨hc₂N, hc₂r⟩, hac₂, hbc₂⟩ :=
      hN₂.directedOn hr₂ pa.val.2 ⟨hpa₂, Set.mem_Iic.mpr hpar.2⟩ pb.val.2
        ⟨hpb₂, Set.mem_Iic.mpr hpbr.2⟩
    have hcbot : (⟨c₁, c₂⟩ : α × β).1 ≠ ⊥ ∧ (⟨c₁, c₂⟩ : α × β).2 ≠ ⊥ :=
      ⟨fun hb' => pa.2.1 (le_bot_iff.mp (hac₁.trans_eq hb')),
        fun hb' => pa.2.2 (le_bot_iff.mp (hac₂.trans_eq hb'))⟩
    refine ⟨↑(⟨(c₁, c₂), hcbot⟩ : NonBotPair α β),
      ⟨Or.inr ⟨_, rfl, hc₁N, hc₂N⟩, Set.mem_Iic.mpr ?_⟩, ?_, ?_⟩
    · refine (WithBot.coe_le_coe (α := NonBotPair α β)).mpr ?_
      show ((c₁, c₂) : α × β) ≤ r.val
      exact ⟨Set.mem_Iic.mp hc₁r, Set.mem_Iic.mp hc₂r⟩
    · refine (WithBot.coe_le_coe (α := NonBotPair α β)).mpr ?_
      show pa.val ≤ ((c₁, c₂) : α × β)
      exact ⟨hac₁, hac₂⟩
    · refine (WithBot.coe_le_coe (α := NonBotPair α β)).mpr ?_
      show pb.val ≤ ((c₁, c₂) : α × β)
      exact ⟨hbc₁, hbc₂⟩
  · intro z hz
    induction z using WithBot.recBotCoe with
    | bot => exact Or.inl rfl
    | coe q =>
      exact Or.inr ⟨q, rfl, hN₁sub ⟨q, hz, rfl⟩, hN₂sub ⟨q, hz, rfl⟩⟩

/- Axiom audit, by `#print axioms` (run, then removed so the build emits no `info`
lines): `lemma_10_sum`, `lemma_17_sum`, `lemma_17_smash`, the three basis characterizations
`isCompactElement_coe_inl_iff` / `isCompactElement_coe_inr_iff` /
`isCompactElement_coe_smash_iff`, and `CoalescedSum`'s `sumSup`, `sumCpo`,
`isLUB_sumSup_left` and `isLUB_sumSup_right` each depend on
`[propext, Classical.choice, Quot.sound]` — `Classical.choice` entering through
the `dite` in `sumSup`, `sumInl`, `sumInr` and `smashPair`. None depends on
`sorryAx`. -/

end ScottDomains
