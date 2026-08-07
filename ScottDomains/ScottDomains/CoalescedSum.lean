import ScottDomains.Domain
import Mathlib.Order.WithBot
-- The *disjoint* order on `α ⊕ β` (`Sum.instLESum`, `Data/Sum/Order.lean:112`),
-- in which `inl` and `inr` elements are incomparable — not the lexicographic
-- `α ⊕ₗ β`. That incomparability is exactly what makes a directed set in a sum
-- lie on one side.
import Mathlib.Data.Sum.Order

/-!
# §4.4: the coalesced sum `D ⊕ E`

Gunter & Scott, *Semantic Domains*, §4.4:

> Given cpo's `D` and `E`, we define the **coalesced sum** `D ⊕ E` to be the set
> `(D∖{⊥_D}) × {0} ∪ (E∖{⊥_E}) × {1} ∪ {⊥_{D⊕E}}`
> where `D∖{⊥_D}` and `E∖{⊥_E}` are the sets `D` and `E` with their respective
> bottom elements removed and `⊥_{D⊕E}` is a new element which is not a pair. It
> is ordered by taking `⊥_{D⊕E} ⊑ z` for all `z` and `(x, m) ⊑ (y, n)` if and only
> if `m = n` and `x ⊑ y`.

*Coalesced*, not separated: the two bottoms are removed and replaced by a single
new one, so `D ⊕ E` has exactly one bottom rather than two incomparable ones.

## The encoding

`WithBot (NonBotSum α β)` where `NonBotSum` is the sum type restricted to
non-bottom injections. Removing the bottoms first is what makes the order
condition "`m = n` and `x ⊑ y`" automatic: `Sum`'s own order in Mathlib already
relates only same-side elements, and with the bottoms gone there is nothing else
to identify.

This is the same shape as the smash product — `WithBot` over a subtype of
non-bottom things — and the two proof obligations are the same:

* the base inherits directedness, because an upper bound of two coerced elements
  cannot be the adjoined bottom;
* the base is closed under nonempty directed suprema.

The second is *easier* here than for the smash product. A directed set in a sum
lies entirely on one side (two elements on opposite sides have no upper bound in
`Sum`), so its supremum is computed in that side alone and is non-bottom because
some member of it already is.

## What `sumSup` branches on

`SupSet` is total, so `sumSup` must answer on every set and some case split is
forced. It branches on **`IsNonBotSum` of the candidate value** — the proposition
the `NonBotSum` constructor needs, i.e. membership of that value in the subtype —
and not on any merely *sufficient* condition for it. `Smash.lean`'s module
docstring records what branching on a sufficient condition (nonempty and directed)
cost there: `BoundedComplete (Smash α β)` was **false** as stated, refuted by the
kernel in r0027; `ScottHom.lean`'s docstring records the identical defect for the
function space.

The candidate itself needs a definition, and this is where the sum differs from
the smash. `α × β` carries a `SupSet` — the smash's candidate is just the
coordinatewise supremum — but `α ⊕ β` carries none, because a set with members on
both sides has no upper bound at all. So `sumCandidate` first selects a summand,
by `(rightParts t).Nonempty`, and takes the supremum there. That inner branch is
*not* a second guard on directedness: on any set that has an upper bound in
`D ⊕ E` with nonempty base, the members all lie on one side (an upper bound is a
coercion `↑r`, and `Sum`'s order relates only same-side elements), so the summand
selected is the only one that could carry the supremum. Sets with members on both
sides — the sets on which the selection is arbitrary — have no upper bound, hence
no least upper bound, so nothing is required of `sumSup` there.

The strongest correctness statement available is exactly Lemma 10's sum conjunct,
`lem10_sum` in `Skeleton/Sum.lean`: when `D` and `E` are bounded complete domains,
`sumSup` returns the least upper bound of **every** set that has an upper bound —
not only of the directed ones. `sumCpo`'s `lubOfDirected` is the directed-set
statement, which needs no such hypothesis on `D` and `E`. Both are discharged by
`isLUB_sumSup_left` / `isLUB_sumSup_right` below, which take the least upper bound
in the summand as a hypothesis and so do not care whether it came from
directedness or from boundedness.
-/

namespace ScottDomains

variable {α β : Type*} [CompletePartialOrder α] [CompletePartialOrder β]

/-- The non-bottom injections of `D` and `E`. -/
def IsNonBotSum (s : α ⊕ β) : Prop :=
  match s with
  | Sum.inl x => x ≠ ⊥
  | Sum.inr y => y ≠ ⊥

/-- `(D∖{⊥}) × {0} ∪ (E∖{⊥}) × {1}` — the paper's two punctured copies. -/
abbrev NonBotSum (α β : Type*) [CompletePartialOrder α] [CompletePartialOrder β] :=
  {s : α ⊕ β // IsNonBotSum s}

/-- The **coalesced sum** `D ⊕ E`: the two punctured copies with a single new
bottom adjoined. -/
abbrev CoalescedSum (α β : Type*) [CompletePartialOrder α] [CompletePartialOrder β] :=
  WithBot (NonBotSum α β)

/-- The base of a set in `D ⊕ E`. -/
def sumBase (s : Set (CoalescedSum α β)) : Set (NonBotSum α β) :=
  {q : NonBotSum α β | (↑q : CoalescedSum α β) ∈ s}

theorem coe_mem_of_mem_sumBase {s : Set (CoalescedSum α β)} {q : NonBotSum α β}
    (h : q ∈ sumBase s) : (↑q : CoalescedSum α β) ∈ s := h

/-- Directedness transfers to the base: an upper bound of two coerced elements is
not the adjoined bottom. -/
theorem directedOn_sumBase {s : Set (CoalescedSum α β)} (hs : DirectedOn (· ≤ ·) s) :
    DirectedOn (· ≤ ·) (sumBase s) := by
  intro q₁ h₁ q₂ h₂
  obtain ⟨c, hc, hle₁, hle₂⟩ :=
    hs _ (coe_mem_of_mem_sumBase h₁) _ (coe_mem_of_mem_sumBase h₂)
  induction c using WithBot.recBotCoe with
  | bot => exact absurd hle₁ (WithBot.not_coe_le_bot q₁)
  | coe q₃ =>
    exact ⟨q₃, hc, (WithBot.coe_le_coe (α := NonBotSum α β)).mp hle₁,
      (WithBot.coe_le_coe (α := NonBotSum α β)).mp hle₂⟩

/-- **A directed set in a sum lies on one side.** Two elements on opposite sides
have no upper bound in `Sum`, so directedness forces agreement. This is what
makes the coalesced sum's suprema easy: they are computed in a single summand. -/
theorem sameSide_of_directedOn {t : Set (NonBotSum α β)} (ht : DirectedOn (· ≤ ·) t)
    {q₁ q₂ : NonBotSum α β} (h₁ : q₁ ∈ t) (h₂ : q₂ ∈ t) :
    (∃ x₁ x₂ : α, q₁.val = Sum.inl x₁ ∧ q₂.val = Sum.inl x₂) ∨
    (∃ y₁ y₂ : β, q₁.val = Sum.inr y₁ ∧ q₂.val = Sum.inr y₂) := by
  obtain ⟨q₃, _, hle₁, hle₂⟩ := ht q₁ h₁ q₂ h₂
  have h1 : q₁.val ≤ q₃.val := hle₁
  have h2 : q₂.val ≤ q₃.val := hle₂
  cases hq₁ : q₁.val with
  | inl x₁ =>
    cases hq₂ : q₂.val with
    | inl x₂ => exact Or.inl ⟨x₁, x₂, rfl, rfl⟩
    | inr y₂ =>
      cases hq₃ : q₃.val with
      | inl x₃ =>
        rw [hq₂, hq₃] at h2
        exact absurd h2 (by simp)
      | inr y₃ =>
        rw [hq₁, hq₃] at h1
        exact absurd h1 (by simp)
  | inr y₁ =>
    cases hq₂ : q₂.val with
    | inl x₂ =>
      cases hq₃ : q₃.val with
      | inl x₃ =>
        rw [hq₁, hq₃] at h1
        exact absurd h1 (by simp)
      | inr y₃ =>
        rw [hq₂, hq₃] at h2
        exact absurd h2 (by simp)
    | inr y₂ => exact Or.inr ⟨y₁, y₂, rfl, rfl⟩

/-- The `α`-parts of a set in the base. -/
def leftParts (t : Set (NonBotSum α β)) : Set α := {x : α | ∃ q ∈ t, q.val = Sum.inl x}

/-- The `β`-parts. -/
def rightParts (t : Set (NonBotSum α β)) : Set β := {y : β | ∃ q ∈ t, q.val = Sum.inr y}

theorem directedOn_leftParts {t : Set (NonBotSum α β)} (ht : DirectedOn (· ≤ ·) t) :
    DirectedOn (· ≤ ·) (leftParts t) := by
  rintro x₁ ⟨q₁, hq₁, e₁⟩ x₂ ⟨q₂, hq₂, e₂⟩
  obtain ⟨q₃, hq₃, hle₁, hle₂⟩ := ht q₁ hq₁ q₂ hq₂
  cases hq : q₃.val with
  | inl x₃ =>
    refine ⟨x₃, ⟨q₃, hq₃, hq⟩, ?_, ?_⟩
    · have h : q₁.val ≤ q₃.val := hle₁
      rw [e₁, hq] at h
      exact Sum.inl_le_inl_iff.mp h
    · have h : q₂.val ≤ q₃.val := hle₂
      rw [e₂, hq] at h
      exact Sum.inl_le_inl_iff.mp h
  | inr y₃ =>
    have h : q₁.val ≤ q₃.val := hle₁
    rw [e₁, hq] at h
    exact absurd h (by simp)

theorem directedOn_rightParts {t : Set (NonBotSum α β)} (ht : DirectedOn (· ≤ ·) t) :
    DirectedOn (· ≤ ·) (rightParts t) := by
  rintro y₁ ⟨q₁, hq₁, e₁⟩ y₂ ⟨q₂, hq₂, e₂⟩
  obtain ⟨q₃, hq₃, hle₁, hle₂⟩ := ht q₁ hq₁ q₂ hq₂
  cases hq : q₃.val with
  | inr y₃ =>
    refine ⟨y₃, ⟨q₃, hq₃, hq⟩, ?_, ?_⟩
    · have h : q₁.val ≤ q₃.val := hle₁
      rw [e₁, hq] at h
      exact Sum.inr_le_inr_iff.mp h
    · have h : q₂.val ≤ q₃.val := hle₂
      rw [e₂, hq] at h
      exact Sum.inr_le_inr_iff.mp h
  | inl x₃ =>
    have h : q₁.val ≤ q₃.val := hle₁
    rw [e₁, hq] at h
    exact absurd h (by simp)

/-- A supremum of left parts is non-bottom, provided there is one to start from. -/
theorem sSup_leftParts_ne_bot {t : Set (NonBotSum α β)} (ht : DirectedOn (· ≤ ·) t)
    {x₀ : α} (hx₀ : x₀ ∈ leftParts t) : sSup (leftParts t) ≠ ⊥ := by
  obtain ⟨q₀, hq₀, e₀⟩ := hx₀
  intro hbot
  have hle : x₀ ≤ sSup (leftParts t) := (directedOn_leftParts ht).le_sSup ⟨q₀, hq₀, e₀⟩
  have hx : x₀ = ⊥ := le_bot_iff.mp (le_of_le_of_eq hle hbot)
  have := q₀.2
  rw [IsNonBotSum.eq_def, e₀] at this
  exact this hx

theorem sSup_rightParts_ne_bot {t : Set (NonBotSum α β)} (ht : DirectedOn (· ≤ ·) t)
    {y₀ : β} (hy₀ : y₀ ∈ rightParts t) : sSup (rightParts t) ≠ ⊥ := by
  obtain ⟨q₀, hq₀, e₀⟩ := hy₀
  intro hbot
  have hle : y₀ ≤ sSup (rightParts t) := (directedOn_rightParts ht).le_sSup ⟨q₀, hq₀, e₀⟩
  have hy : y₀ = ⊥ := le_bot_iff.mp (le_of_le_of_eq hle hbot)
  have := q₀.2
  rw [IsNonBotSum.eq_def, e₀] at this
  exact this hy

/-! ## Suprema in `D ⊕ E` -/

/-- The supremum of the empty set in a cpo is `⊥`: `∅` is directed, so `sSup ∅` is
its least upper bound, and `⊥` is an upper bound of it. -/
theorem sSup_empty_eq_bot : sSup (∅ : Set α) = (⊥ : α) := by
  have hdir : DirectedOn (· ≤ ·) (∅ : Set α) := fun _ hx => hx.elim
  exact le_bot_iff.mp (hdir.isLUB_sSup.2 fun _ hx => hx.elim)

@[simp] theorem leftParts_empty : leftParts (∅ : Set (NonBotSum α β)) = (∅ : Set α) := by
  ext x
  simp [leftParts]

@[simp] theorem rightParts_empty : rightParts (∅ : Set (NonBotSum α β)) = (∅ : Set β) := by
  ext y
  simp [rightParts]

open Classical in
/-- The candidate supremum of a base, computed in `α ⊕ β`. The summand is selected
by `(rightParts t).Nonempty`; on any `t` with an upper bound that selection is
forced, since `Sum`'s order relates only same-side elements. -/
noncomputable def sumCandidate (t : Set (NonBotSum α β)) : α ⊕ β :=
  if (rightParts t).Nonempty then Sum.inr (sSup (rightParts t)) else Sum.inl (sSup (leftParts t))

theorem sumCandidate_of_right {t : Set (NonBotSum α β)} (h : (rightParts t).Nonempty) :
    sumCandidate t = Sum.inr (sSup (rightParts t)) := by
  classical simp only [sumCandidate, if_pos h]

theorem sumCandidate_of_left {t : Set (NonBotSum α β)} (h : ¬ (rightParts t).Nonempty) :
    sumCandidate t = Sum.inl (sSup (leftParts t)) := by
  classical simp only [sumCandidate, if_neg h]

open Classical in
/-- Suprema in `D ⊕ E`: the candidate value when it lands in `NonBotSum`, and the
adjoined bottom otherwise. The guard is membership of the candidate in the
subtype — the proposition the constructor needs — not a sufficient condition for
it; see the module docstring. -/
noncomputable def sumSup (s : Set (CoalescedSum α β)) : CoalescedSum α β :=
  if h : IsNonBotSum (sumCandidate (sumBase s)) then
    ↑(⟨sumCandidate (sumBase s), h⟩ : NonBotSum α β)
  else ⊥

/-- The defining equation of `sumSup` on the branch it is meant for, with the
`dite` discharged. -/
theorem sumSup_of_isNonBotSum {s : Set (CoalescedSum α β)}
    (h : IsNonBotSum (sumCandidate (sumBase s))) :
    sumSup s = ↑(⟨sumCandidate (sumBase s), h⟩ : NonBotSum α β) := by
  classical simp only [sumSup, dif_pos h]

/-- The defining equation of `sumSup` on the adjoined-bottom branch. -/
theorem sumSup_of_not_isNonBotSum {s : Set (CoalescedSum α β)}
    (h : ¬ IsNonBotSum (sumCandidate (sumBase s))) : sumSup s = ⊥ := by
  classical simp only [sumSup, dif_neg h]

/-- The candidate of an empty base is `Sum.inl ⊥`, which fails the guard. This is
what sends a set contained in `{⊥}` to the adjoined bottom. -/
theorem sumCandidate_of_empty_base {s : Set (CoalescedSum α β)} (h : ¬ (sumBase s).Nonempty) :
    sumCandidate (sumBase s) = Sum.inl (⊥ : α) := by
  have hb : sumBase s = ∅ := Set.not_nonempty_iff_eq_empty.mp h
  have hR : ¬ (rightParts (sumBase s)).Nonempty := by
    rw [hb, rightParts_empty]
    exact Set.not_nonempty_empty
  rw [sumCandidate_of_left hR, hb, leftParts_empty, sSup_empty_eq_bot]

theorem sumSup_of_empty {s : Set (CoalescedSum α β)} (h : ¬ (sumBase s).Nonempty) :
    sumSup s = ⊥ := by
  refine sumSup_of_not_isNonBotSum ?_
  rw [sumCandidate_of_empty_base h]
  exact fun hne => hne rfl

/-- A set contained in `{⊥}` has `⊥` as its least upper bound, which is what
`sumSup` returns for it. -/
theorem isLUB_sumSup_of_empty_base {s : Set (CoalescedSum α β)}
    (h : ¬ (sumBase s).Nonempty) : IsLUB s (sumSup s) := by
  rw [sumSup_of_empty h]
  constructor
  · intro z hz
    induction z using WithBot.recBotCoe with
    | bot => exact le_rfl
    | coe q => exact absurd ⟨q, hz⟩ h
  · intro _ _
    exact bot_le

/-- **`sumSup` is the least upper bound of a left-sided set**, given the least
upper bound of its left parts. The hypothesis is `IsLUB` of the `sSup` of
`leftParts`, so a caller may supply it either from directedness
(`DirectedOn.isLUB_sSup`, as `sumCpo` does) or from bounded completeness
(`isLUB_sSup_of_bddAbove`, as `lem10_sum` does). -/
theorem isLUB_sumSup_left {s : Set (CoalescedSum α β)} {q₀ : NonBotSum α β}
    (hq₀ : q₀ ∈ sumBase s) (hleft : ∀ q ∈ sumBase s, ∃ x : α, q.val = Sum.inl x)
    (hlub : IsLUB (leftParts (sumBase s)) (sSup (leftParts (sumBase s)))) :
    IsLUB s (sumSup s) := by
  obtain ⟨x₀, e₀⟩ := hleft q₀ hq₀
  have hx₀ : x₀ ∈ leftParts (sumBase s) := ⟨q₀, hq₀, e₀⟩
  have hx₀bot : x₀ ≠ ⊥ := by
    have h := q₀.2
    rw [IsNonBotSum.eq_def, e₀] at h
    exact h
  have hR : ¬ (rightParts (sumBase s)).Nonempty := by
    rintro ⟨y, q, hq, hqy⟩
    obtain ⟨x, hx⟩ := hleft q hq
    rw [hx] at hqy
    exact absurd hqy (by simp)
  have hc : sumCandidate (sumBase s) = Sum.inl (sSup (leftParts (sumBase s))) :=
    sumCandidate_of_left hR
  have hguard : IsNonBotSum (sumCandidate (sumBase s)) := by
    rw [hc]
    exact fun hbot => hx₀bot (le_bot_iff.mp (le_of_le_of_eq (hlub.1 hx₀) hbot))
  rw [sumSup_of_isNonBotSum hguard]
  constructor
  · intro z hz
    induction z using WithBot.recBotCoe with
    | bot => exact bot_le
    | coe q =>
      refine (WithBot.coe_le_coe (α := NonBotSum α β)).mpr ?_
      show q.val ≤ sumCandidate (sumBase s)
      obtain ⟨x, hx⟩ := hleft q hz
      rw [hc, hx]
      exact Sum.inl_le_inl_iff.mpr (hlub.1 ⟨q, hz, hx⟩)
  · intro u hu
    induction u using WithBot.recBotCoe with
    | bot => exact absurd (hu (coe_mem_of_mem_sumBase hq₀)) (WithBot.not_coe_le_bot q₀)
    | coe r =>
      refine (WithBot.coe_le_coe (α := NonBotSum α β)).mpr ?_
      show sumCandidate (sumBase s) ≤ r.val
      have hq₀r : q₀.val ≤ r.val :=
        (WithBot.coe_le_coe (α := NonBotSum α β)).mp (hu (coe_mem_of_mem_sumBase hq₀))
      rw [e₀] at hq₀r
      obtain ⟨xr, hxr⟩ : ∃ xr : α, r.val = Sum.inl xr := by
        cases hr : r.val with
        | inl xr => exact ⟨xr, rfl⟩
        | inr yr =>
          rw [hr] at hq₀r
          exact absurd hq₀r (by simp)
      rw [hc, hxr]
      refine Sum.inl_le_inl_iff.mpr (hlub.2 ?_)
      rintro x ⟨q, hq, hqx⟩
      have hqr : q.val ≤ r.val :=
        (WithBot.coe_le_coe (α := NonBotSum α β)).mp (hu (coe_mem_of_mem_sumBase hq))
      rw [hqx, hxr] at hqr
      exact Sum.inl_le_inl_iff.mp hqr

/-- **`sumSup` is the least upper bound of a right-sided set**, given the least
upper bound of its right parts. The mirror image of `isLUB_sumSup_left`; the two
summands are not interchangeable by a `Sum`-level symmetry that Mathlib supplies,
so the argument is repeated rather than transported. -/
theorem isLUB_sumSup_right {s : Set (CoalescedSum α β)} {q₀ : NonBotSum α β}
    (hq₀ : q₀ ∈ sumBase s) (hright : ∀ q ∈ sumBase s, ∃ y : β, q.val = Sum.inr y)
    (hlub : IsLUB (rightParts (sumBase s)) (sSup (rightParts (sumBase s)))) :
    IsLUB s (sumSup s) := by
  obtain ⟨y₀, e₀⟩ := hright q₀ hq₀
  have hy₀ : y₀ ∈ rightParts (sumBase s) := ⟨q₀, hq₀, e₀⟩
  have hy₀bot : y₀ ≠ ⊥ := by
    have h := q₀.2
    rw [IsNonBotSum.eq_def, e₀] at h
    exact h
  have hc : sumCandidate (sumBase s) = Sum.inr (sSup (rightParts (sumBase s))) :=
    sumCandidate_of_right ⟨y₀, hy₀⟩
  have hguard : IsNonBotSum (sumCandidate (sumBase s)) := by
    rw [hc]
    exact fun hbot => hy₀bot (le_bot_iff.mp (le_of_le_of_eq (hlub.1 hy₀) hbot))
  rw [sumSup_of_isNonBotSum hguard]
  constructor
  · intro z hz
    induction z using WithBot.recBotCoe with
    | bot => exact bot_le
    | coe q =>
      refine (WithBot.coe_le_coe (α := NonBotSum α β)).mpr ?_
      show q.val ≤ sumCandidate (sumBase s)
      obtain ⟨y, hy⟩ := hright q hz
      rw [hc, hy]
      exact Sum.inr_le_inr_iff.mpr (hlub.1 ⟨q, hz, hy⟩)
  · intro u hu
    induction u using WithBot.recBotCoe with
    | bot => exact absurd (hu (coe_mem_of_mem_sumBase hq₀)) (WithBot.not_coe_le_bot q₀)
    | coe r =>
      refine (WithBot.coe_le_coe (α := NonBotSum α β)).mpr ?_
      show sumCandidate (sumBase s) ≤ r.val
      have hq₀r : q₀.val ≤ r.val :=
        (WithBot.coe_le_coe (α := NonBotSum α β)).mp (hu (coe_mem_of_mem_sumBase hq₀))
      rw [e₀] at hq₀r
      obtain ⟨yr, hyr⟩ : ∃ yr : β, r.val = Sum.inr yr := by
        cases hr : r.val with
        | inr yr => exact ⟨yr, rfl⟩
        | inl xr =>
          rw [hr] at hq₀r
          exact absurd hq₀r (by simp)
      rw [hc, hyr]
      refine Sum.inr_le_inr_iff.mpr (hlub.2 ?_)
      rintro y ⟨q, hq, hqy⟩
      have hqr : q.val ≤ r.val :=
        (WithBot.coe_le_coe (α := NonBotSum α β)).mp (hu (coe_mem_of_mem_sumBase hq))
      rw [hqy, hyr] at hqr
      exact Sum.inr_le_inr_iff.mp hqr

/-- **`D ⊕ E` is a cpo.** The base of a directed set is directed and lies on one
side (`sameSide_of_directedOn`), so one of `isLUB_sumSup_left` /
`isLUB_sumSup_right` applies with the least upper bound supplied by
`DirectedOn.isLUB_sSup` in that summand. -/
noncomputable instance sumCpo : CompletePartialOrder (CoalescedSum α β) :=
  { (inferInstance : PartialOrder (CoalescedSum α β)),
    (inferInstance : OrderBot (CoalescedSum α β)) with
    sSup := sumSup
    lubOfDirected := fun s hs => by
      by_cases hne : (sumBase s).Nonempty
      · obtain ⟨q₀, hq₀⟩ := hne
        have hdir := directedOn_sumBase hs
        cases e₀ : q₀.val with
        | inl x₀ =>
          have hleft : ∀ q ∈ sumBase s, ∃ x : α, q.val = Sum.inl x := by
            intro q hq
            rcases sameSide_of_directedOn hdir hq₀ hq with ⟨_, x, _, hx⟩ | ⟨_, _, hq₀r, _⟩
            · exact ⟨x, hx⟩
            · rw [e₀] at hq₀r
              exact absurd hq₀r (by simp)
          exact isLUB_sumSup_left hq₀ hleft (directedOn_leftParts hdir).isLUB_sSup
        | inr y₀ =>
          have hright : ∀ q ∈ sumBase s, ∃ y : β, q.val = Sum.inr y := by
            intro q hq
            rcases sameSide_of_directedOn hdir hq₀ hq with ⟨_, _, hq₀l, _⟩ | ⟨_, y, _, hy⟩
            · rw [e₀] at hq₀l
              exact absurd hq₀l (by simp)
            · exact ⟨y, hy⟩
          exact isLUB_sumSup_right hq₀ hright (directedOn_rightParts hdir).isLUB_sSup
      · exact isLUB_sumSup_of_empty_base hne }

end ScottDomains
