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

end ScottDomains
