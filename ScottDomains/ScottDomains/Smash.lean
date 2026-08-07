import ScottDomains.Product
import Mathlib.Order.WithBot

/-!
# §4.3: the smash product `D ⊗ E`

Gunter & Scott, *Semantic Domains*, §4.3:

> For cpo's `D` and `E`, the smash product `D ⊗ E` is the set
> `{(x, y) ∈ D × E | x ≠ ⊥ and y ≠ ⊥} ∪ {⊥_{D⊗E}}`
> where `⊥_{D⊗E}` is some new element which is not a pair. The ordering on pairs
> is coordinatewise and we stipulate that `⊥_{D⊗E} ⊑ z` for every `z ∈ D ⊗ E`.

The paper's "some new element which is not a pair" is exactly `WithBot` applied
to the subtype of pairs with neither coordinate `⊥` — the collapsed product in
which `(x, ⊥)` and `(⊥, y)` are identified with each other and with the new
bottom.

## The two things that need proof

**The base inherits directedness.** As with the lift, an upper bound of two
coerced pairs cannot be the adjoined bottom, so directedness of a set in `D ⊗ E`
transfers to its base. This is `WithBot.not_coe_le_bot` again.

**The base is closed under directed suprema.** This is the part that is *not*
shared with the lift: the coordinatewise supremum of a nonempty directed set of
non-bottom pairs is again non-bottom, because some member `q` of the set has
`q.1 ≠ ⊥` and `q.1 ⊑ (⨆t).1`, so `(⨆t).1 = ⊥` would force `q.1 = ⊥`. The
nonemptiness is essential — the empty set's coordinatewise supremum *is*
`(⊥, ⊥)`, which is why the empty case is sent to the adjoined bottom instead.
-/

namespace ScottDomains

variable {α β : Type*} [CompletePartialOrder α] [CompletePartialOrder β]

/-- The pairs with neither coordinate `⊥`. -/
abbrev NonBotPair (α β : Type*) [CompletePartialOrder α] [CompletePartialOrder β] :=
  {p : α × β // p.1 ≠ ⊥ ∧ p.2 ≠ ⊥}

/-- The **smash product** `D ⊗ E`: the non-bottom pairs with a new bottom
adjoined. -/
abbrev Smash (α β : Type*) [CompletePartialOrder α] [CompletePartialOrder β] :=
  WithBot (NonBotPair α β)

/-- The base of a set in `D ⊗ E`: its non-bottom members, as pairs. -/
def smashBase (s : Set (Smash α β)) : Set (NonBotPair α β) :=
  {q : NonBotPair α β | (↑q : Smash α β) ∈ s}

theorem coe_mem_of_mem_smashBase {s : Set (Smash α β)} {q : NonBotPair α β}
    (h : q ∈ smashBase s) : (↑q : Smash α β) ∈ s := h

/-- Directedness transfers to the base: an upper bound of two coerced pairs is
not the adjoined bottom. -/
theorem directedOn_smashBase {s : Set (Smash α β)} (hs : DirectedOn (· ≤ ·) s) :
    DirectedOn (· ≤ ·) (smashBase s) := by
  intro q₁ h₁ q₂ h₂
  obtain ⟨c, hc, hle₁, hle₂⟩ :=
    hs _ (coe_mem_of_mem_smashBase h₁) _ (coe_mem_of_mem_smashBase h₂)
  induction c using WithBot.recBotCoe with
  | bot => exact absurd hle₁ (WithBot.not_coe_le_bot q₁)
  | coe q₃ => exact ⟨q₃, hc, WithBot.coe_le_coe.mp hle₁, WithBot.coe_le_coe.mp hle₂⟩

/-- The base's image in `D × E` is directed. -/
theorem directedOn_val_smashBase {t : Set (NonBotPair α β)} (ht : DirectedOn (· ≤ ·) t) :
    DirectedOn (· ≤ ·) (Subtype.val '' t) := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  obtain ⟨c, hc, hac, hbc⟩ := ht a ha b hb
  exact ⟨c.val, ⟨c, hc, rfl⟩, hac, hbc⟩

/-- **Non-bottom pairs are closed under nonempty directed suprema.** Neither
coordinate of the supremum can be `⊥`, because some member of the set already has
that coordinate non-`⊥` and sits below the supremum.

Nonemptiness is essential: the coordinatewise supremum of `∅` is `(⊥, ⊥)`. -/
theorem sSup_ne_bot_of_nonempty {t : Set (NonBotPair α β)} (hne : t.Nonempty)
    (ht : DirectedOn (· ≤ ·) t) :
    (sSup (Subtype.val '' t)).1 ≠ ⊥ ∧ (sSup (Subtype.val '' t)).2 ≠ ⊥ := by
  obtain ⟨q, hq⟩ := hne
  have hle : q.val ≤ sSup (Subtype.val '' t) :=
    (directedOn_val_smashBase ht).le_sSup ⟨q, hq, rfl⟩
  constructor
  · intro hbot
    exact q.2.1 (le_bot_iff.mp (le_of_le_of_eq hle.1 hbot))
  · intro hbot
    exact q.2.2 (le_bot_iff.mp (le_of_le_of_eq hle.2 hbot))

open Classical in
/-- Suprema in `D ⊗ E`: the coordinatewise supremum of the base when the base is
nonempty and directed, and the adjoined bottom otherwise. -/
noncomputable def smashSup (s : Set (Smash α β)) : Smash α β :=
  if h : (smashBase s).Nonempty ∧ DirectedOn (· ≤ ·) (smashBase s) then
    ↑(⟨sSup (Subtype.val '' smashBase s), sSup_ne_bot_of_nonempty h.1 h.2⟩ : NonBotPair α β)
  else ⊥

theorem smashSup_of_directed {s : Set (Smash α β)} (hne : (smashBase s).Nonempty)
    (hdir : DirectedOn (· ≤ ·) (smashBase s)) :
    smashSup s =
      ↑(⟨sSup (Subtype.val '' smashBase s), sSup_ne_bot_of_nonempty hne hdir⟩ :
        NonBotPair α β) := by
  classical simp only [smashSup, dif_pos (And.intro hne hdir)]

theorem smashSup_of_empty {s : Set (Smash α β)} (h : ¬ (smashBase s).Nonempty) :
    smashSup s = ⊥ := by
  classical
  have hneg : ¬ ((smashBase s).Nonempty ∧ DirectedOn (· ≤ ·) (smashBase s)) :=
    fun hc => h hc.1
  simp only [smashSup, dif_neg hneg]

/-- **`D ⊗ E` is a cpo.** -/
noncomputable instance smashCpo : CompletePartialOrder (Smash α β) :=
  { (inferInstance : PartialOrder (Smash α β)),
    (inferInstance : OrderBot (Smash α β)) with
    sSup := smashSup
    lubOfDirected := fun s hs => by
      have hdir := directedOn_smashBase hs
      by_cases hne : (smashBase s).Nonempty
      · rw [smashSup_of_directed hne hdir]
        have hvdir := directedOn_val_smashBase hdir
        constructor
        · intro x hx
          induction x using WithBot.recBotCoe with
          | bot => exact bot_le
          | coe q => exact WithBot.coe_le_coe.mpr (hvdir.le_sSup ⟨q, hx, rfl⟩)
        · intro u hu
          obtain ⟨q₀, hq₀⟩ := hne
          induction u using WithBot.recBotCoe with
          | bot =>
            exact absurd (hu (coe_mem_of_mem_smashBase hq₀)) (WithBot.not_coe_le_bot q₀)
          | coe r =>
            refine WithBot.coe_le_coe.mpr ?_
            show sSup (Subtype.val '' smashBase s) ≤ r.val
            refine hvdir.sSup_le ?_
            rintro _ ⟨q, hq, rfl⟩
            have hqr : (↑q : Smash α β) ≤ ↑r := hu (coe_mem_of_mem_smashBase hq)
            -- `NonBotPair` is itself a subtype, so `↑` is ambiguous here; pin the
            -- lemma to the `WithBot` layer rather than the `Subtype` one.
            exact (WithBot.coe_le_coe (α := NonBotPair α β)).mp hqr
      · rw [smashSup_of_empty hne]
        constructor
        · intro x hx
          induction x using WithBot.recBotCoe with
          | bot => exact le_rfl
          | coe q => exact absurd ⟨q, hx⟩ hne
        · intro _ _
          exact bot_le }

end ScottDomains
