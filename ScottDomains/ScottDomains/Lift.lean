import ScottDomains.Domain
import Mathlib.Order.WithBot

/-!
# The lift `D⊥`

Gunter & Scott, *Semantic Domains*, §4.4: the **lift** of a cpo adjoins a new
bottom element below everything.

Mathlib's `WithBot α` is exactly that construction on the order side, with the
coercion `↑ : α → WithBot α` an order embedding and `⊥` the new element. What it
does not carry is a cpo structure, which this file supplies.

## Suprema in the lift

For `s ⊆ D⊥`, write `t = {a : D | ↑a ∈ s}` for the part of `s` below the new
bottom's level. If `t` is empty then `s ⊆ {⊥}` and its supremum is `⊥`;
otherwise the supremum is `↑(⨆t)`.

The step that needs an argument is that `t` inherits directedness: given
`↑a₁, ↑a₂ ∈ s`, directedness of `s` produces some `c ∈ s` above both, and `c`
**cannot be `⊥`** — `↑a₁ ≤ ⊥` is false in `WithBot`. So `c` is again a coercion
and its preimage lies in `t`. That single observation is what makes the lift a
cpo rather than merely a pointed order.

As with `ScottHom` and `↓a`, `SupSet` totality forces a case split; here it is on
whether `t` is empty, and on a directed set the branch taken is always the
correct one.
-/

namespace ScottDomains

variable {α : Type*} [CompletePartialOrder α]

/-- The elements of `s` that are not the adjoined bottom, pulled back to `D`. -/
def liftBase (s : Set (WithBot α)) : Set α := {a : α | (↑a : WithBot α) ∈ s}

omit [CompletePartialOrder α] in
theorem coe_mem_of_mem_liftBase {s : Set (WithBot α)} {a : α} (h : a ∈ liftBase s) :
    (↑a : WithBot α) ∈ s := h

/-- Directedness transfers to the base: an upper bound of two coercions cannot be
the adjoined bottom. -/
theorem directedOn_liftBase {s : Set (WithBot α)} (hs : DirectedOn (· ≤ ·) s) :
    DirectedOn (· ≤ ·) (liftBase s) := by
  intro a₁ h₁ a₂ h₂
  obtain ⟨c, hc, hle₁, hle₂⟩ := hs _ (coe_mem_of_mem_liftBase h₁) _ (coe_mem_of_mem_liftBase h₂)
  induction c using WithBot.recBotCoe with
  | bot => exact absurd hle₁ (WithBot.not_coe_le_bot a₁)
  | coe a₃ =>
    exact ⟨a₃, hc, WithBot.coe_le_coe.mp hle₁, WithBot.coe_le_coe.mp hle₂⟩

open Classical in
/-- Suprema in `D⊥`: the coerced supremum of the base when the base is nonempty,
and the adjoined bottom otherwise. -/
noncomputable def liftSup (s : Set (WithBot α)) : WithBot α :=
  if (liftBase s).Nonempty then ↑(sSup (liftBase s)) else ⊥

theorem liftSup_of_nonempty {s : Set (WithBot α)} (h : (liftBase s).Nonempty) :
    liftSup s = ↑(sSup (liftBase s)) := by
  classical simp only [liftSup, if_pos h]

theorem liftSup_of_empty {s : Set (WithBot α)} (h : ¬ (liftBase s).Nonempty) :
    liftSup s = ⊥ := by
  classical simp only [liftSup, if_neg h]

/-- **`D⊥` is a cpo.** -/
@[reducible] noncomputable def liftCpo : CompletePartialOrder (WithBot α) :=
  { (inferInstance : PartialOrder (WithBot α)),
    (inferInstance : OrderBot (WithBot α)) with
    sSup := liftSup
    lubOfDirected := fun s hs => by
      by_cases hne : (liftBase s).Nonempty
      · rw [liftSup_of_nonempty hne]
        have hdir := directedOn_liftBase hs
        constructor
        · intro x hx
          induction x using WithBot.recBotCoe with
          | bot => exact bot_le
          | coe a => exact WithBot.coe_le_coe.mpr (hdir.le_sSup hx)
        · intro u hu
          obtain ⟨a₀, ha₀⟩ := hne
          induction u using WithBot.recBotCoe with
          | bot => exact absurd (hu (coe_mem_of_mem_liftBase ha₀)) (WithBot.not_coe_le_bot a₀)
          | coe b =>
            refine WithBot.coe_le_coe.mpr (hdir.sSup_le ?_)
            intro a ha
            exact WithBot.coe_le_coe.mp (hu (coe_mem_of_mem_liftBase ha))
      · rw [liftSup_of_empty hne]
        constructor
        · intro x hx
          induction x using WithBot.recBotCoe with
          | bot => exact le_rfl
          | coe a => exact absurd ⟨a, hx⟩ hne
        · intro _ _
          exact bot_le }

end ScottDomains
