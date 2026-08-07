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

## What `smashSup` branches on (r0027)

`SupSet` is total, so `smashSup` must answer on every set and some case split is
forced. It branches on **the coordinatewise supremum having neither coordinate
`⊥`** — the condition under which that supremum is an element of `D ⊗ E` at all —
and not on any merely *sufficient* condition for it.

An earlier version branched on the base being nonempty and directed. That made
`BoundedComplete (Smash α β)` false as stated, which agent1 refuted by the kernel
in r0027: for the bounded complete domains `D = Prop × Prop` and `E = Prop`, the
set `{↑((True, False), True), ↑((False, True), True)}` is bounded above by
`↑((True, True), True)` but is not directed, so the old `smashSup` returned the
adjoined bottom — not even an upper bound of the set — while the least upper bound
is `↑((True, True), True)`. `ScottHom`'s module docstring records the identical
defect and the identical repair for the function space, where the condition to
branch on is continuity of the pointwise supremum rather than directedness.

The repair is conservative: `smashSup_of_directed` and `smashSup_of_empty` below
are unchanged in statement, so the new guard agrees with the old one wherever the
old one applied — `sSup_ne_bot_of_nonempty` discharges the new guard on a nonempty
directed base, and `sSup_val_smashBase_eq_bot` refutes it on an empty base.
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
/-- Suprema in `D ⊗ E`: the coordinatewise supremum of the base when that supremum
has neither coordinate `⊥`, and the adjoined bottom otherwise. The guard is the
condition under which the coordinatewise supremum is an element of `D ⊗ E`, not a
sufficient condition for it — see the module docstring for what branching on
directedness instead cost. -/
noncomputable def smashSup (s : Set (Smash α β)) : Smash α β :=
  if h : (sSup (Subtype.val '' smashBase s)).1 ≠ ⊥ ∧
      (sSup (Subtype.val '' smashBase s)).2 ≠ ⊥ then
    ↑(⟨sSup (Subtype.val '' smashBase s), h⟩ : NonBotPair α β)
  else ⊥

/-- The defining equation of `smashSup` on the branch it is meant for, with the
`dite` discharged. -/
theorem smashSup_of_ne_bot {s : Set (Smash α β)}
    (h : (sSup (Subtype.val '' smashBase s)).1 ≠ ⊥ ∧
      (sSup (Subtype.val '' smashBase s)).2 ≠ ⊥) :
    smashSup s = ↑(⟨sSup (Subtype.val '' smashBase s), h⟩ : NonBotPair α β) := by
  classical simp only [smashSup, dif_pos h]

/-- **The new guard agrees with the old one on a nonempty directed base**, which
is what keeps `smashCpo` below unchanged: `sSup_ne_bot_of_nonempty` discharges the
guard, and the resulting `NonBotPair` differs from the one named here only in its
proof component, where Lean's definitional proof irrelevance applies. -/
theorem smashSup_of_directed {s : Set (Smash α β)} (hne : (smashBase s).Nonempty)
    (hdir : DirectedOn (· ≤ ·) (smashBase s)) :
    smashSup s =
      ↑(⟨sSup (Subtype.val '' smashBase s), sSup_ne_bot_of_nonempty hne hdir⟩ :
        NonBotPair α β) :=
  smashSup_of_ne_bot (sSup_ne_bot_of_nonempty hne hdir)

/-- The coordinatewise supremum of an empty base is `(⊥, ⊥)`. The empty set is
directed, so `sSup ∅` is its least upper bound; `⊥` is an upper bound of it; hence
`sSup ∅ ≤ ⊥`. This is what makes the guard fail on an empty base. -/
theorem sSup_val_smashBase_eq_bot {s : Set (Smash α β)} (h : ¬ (smashBase s).Nonempty) :
    sSup (Subtype.val '' smashBase s) = (⊥ : α × β) := by
  rw [Set.not_nonempty_iff_eq_empty.mp h, Set.image_empty]
  have hdir : DirectedOn (· ≤ ·) (∅ : Set (α × β)) := fun _ hx => hx.elim
  exact le_bot_iff.mp (hdir.isLUB_sSup.2 fun _ hx => hx.elim)

/-- **The new guard agrees with the old one on an empty base**: both send it to
the adjoined bottom, the first because `sSup ∅ = (⊥, ⊥)` fails the guard. -/
theorem smashSup_of_empty {s : Set (Smash α β)} (h : ¬ (smashBase s).Nonempty) :
    smashSup s = ⊥ := by
  classical
  have hneg : ¬ ((sSup (Subtype.val '' smashBase s)).1 ≠ ⊥ ∧
      (sSup (Subtype.val '' smashBase s)).2 ≠ ⊥) := by
    rw [sSup_val_smashBase_eq_bot h]
    exact fun hc => hc.1 rfl
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
