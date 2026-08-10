import ScottDomains.Smash
import ScottDomains.Lift
import ScottDomains.StrictHom
import ScottDomains.Product
import ScottDomains.FunctionSpaceCountable

/-!
# Lemma 10: bounded completeness is closed under the operators

Gunter & Scott, *Semantic Domains*, §4.5:

> **Lemma 10** If `D` and `E` are bounded complete domains then so are the cpo's
> `D → E`, `D →⊥ E`, `D × E`, `D ⊗ E`, `D + E`, `D⊥`.

The `D → E` conjunct is **already proved** — it is Theorem 7's bounded-complete
half (`ScottHom`'s `BoundedComplete` instance, r0007) — so it is not restated
here. The remaining conjuncts are one statement each so they can be discharged
independently.

## Status

All four are proved: `lemma_10_prod`, `lemma_10_smash`, `lemma_10_lift`, `lemma_10_strict`.
Zero `sorry`.

## The defect `lemma_10_smash` exposed, and the repair (r0027)

`lemma_10_smash` was first refutable, not merely open. `smashSup` in `Smash.lean`
branched its `dite` on the base being nonempty **and directed**, so on a bounded
but non-directed set `sSup` returned the adjoined bottom, which is not even an
upper bound of the set. The kernel-checked refutation used the bounded complete
domains `D = Prop × Prop` (all four elements compact, hence a domain; bounded
complete by `lemma_10_prod`) and `E = Prop`, with

    s = {↑((True, False), True), ↑((False, True), True)} ⊆ D ⊗ E,

bounded above by `↑((True, True), True)` and not directed, since `(True, False)`
and `(False, True)` are incomparable in `Prop × Prop`.

The paper's mathematics was never in doubt — `D ⊗ E` is bounded complete — the
defect was in the Lean rendering of a total `sSup`. `Smash.lean` now branches on
the condition that makes the coordinatewise supremum an element of `D ⊗ E`, that
it lands in `NonBotPair`, rather than on a sufficient condition for it;
`smashSup_of_directed` and `smashSup_of_empty` keep their statements, so the new
guard provably agrees with the old wherever the old one applied, and `smashCpo`
needed no change. `ScottHom.lean`'s module docstring records the identical defect
and repair for the function space, where the condition is continuity of the
pointwise supremum. The refutation itself is not kept: it is false against the
repaired definition. It is in the git history at commit `1f1f10c`.

**Owned by agent1**, except for the authorized repair to `Smash.lean`.
-/

namespace ScottDomains

variable {α β : Type*} [CompletePartialOrder α] [CompletePartialOrder β]

section Prod

/-- The first-coordinate image of a set bounded above is bounded above. -/
theorem bddAbove_fst_image {s : Set (α × β)} (hs : BddAbove s) : BddAbove (Prod.fst '' s) := by
  obtain ⟨u, hu⟩ := hs
  exact ⟨u.1, by rintro _ ⟨p, hp, rfl⟩; exact (hu hp).1⟩

/-- The second-coordinate image of a set bounded above is bounded above. -/
theorem bddAbove_snd_image {s : Set (α × β)} (hs : BddAbove s) : BddAbove (Prod.snd '' s) := by
  obtain ⟨u, hu⟩ := hs
  exact ⟨u.2, by rintro _ ⟨p, hp, rfl⟩; exact (hu hp).2⟩

/-- **Lemma 10, `D × E`.** Suprema in the product cpo are coordinatewise
(`Prod.supSet`), and `isLUB_prod` says a least upper bound in a product is a pair
of least upper bounds. Boundedness passes to each coordinate image, so each
coordinate supremum is a least upper bound by bounded completeness of the factor.
No case split — unlike `ScottHom`, `WithBot` and `Smash`, the product's `sSup` is
correct on every set on which the factors' `sSup` is. -/
theorem lemma_10_prod [Domain α] [BoundedComplete α] [Domain β] [BoundedComplete β] :
    BoundedComplete (α × β) where
  isLUB_sSup_of_bddAbove s hs := by
    have hsup : (sSup s : α × β) = (sSup (Prod.fst '' s), sSup (Prod.snd '' s)) := rfl
    rw [isLUB_prod, hsup]
    exact ⟨isLUB_sSup_of_bddAbove (bddAbove_fst_image hs),
      isLUB_sSup_of_bddAbove (bddAbove_snd_image hs)⟩

end Prod

section Smash

/-- An upper bound of a set whose base is nonempty is a coerced pair, never the
adjoined bottom — the smash-product form of `exists_coe_of_mem_upperBounds`. -/
theorem exists_coe_of_mem_upperBounds_smash {s : Set (Smash α β)}
    (hne : (smashBase s).Nonempty) {u : Smash α β} (hu : u ∈ upperBounds s) :
    ∃ r : NonBotPair α β, u = ↑r := by
  obtain ⟨q₀, hq₀⟩ := hne
  induction u using WithBot.recBotCoe with
  | bot => exact absurd (hu (coe_mem_of_mem_smashBase hq₀)) (WithBot.not_coe_le_bot q₀)
  | coe r => exact ⟨r, rfl⟩

/-- **Lemma 10, `D ⊗ E`.** The base of a bounded set is bounded in `D × E` —
an upper bound of a set with nonempty base is a coerced pair, and coercion
reflects `≤`. `lemma_10_prod` makes the coordinatewise supremum of the base's image
its least upper bound, and a member of a nonempty base sits below it with both
coordinates non-`⊥`, so `smashSup`'s guard holds and the value is that supremum
coerced. On an empty base the set is contained in `{⊥}` and the value is `⊥`.

This is the conjunct that `smashSup`'s original `dite` guard made false: it
branched on the base being nonempty and *directed*, so a bounded non-directed set
received the adjoined bottom. The r0027 refutation used `D = Prop × Prop`,
`E = Prop` and `s = {↑((True, False), True), ↑((False, True), True)}`, which is
bounded above by `↑((True, True), True)` and not directed. `Smash.lean` now
branches on the coordinatewise supremum landing in `NonBotPair` — the condition
that makes it an element of `D ⊗ E` — and its module docstring carries the full
account. -/
theorem lemma_10_smash [Domain α] [BoundedComplete α] [Domain β] [BoundedComplete β] :
    BoundedComplete (Smash α β) where
  isLUB_sSup_of_bddAbove s hs := by
    haveI : BoundedComplete (α × β) := lemma_10_prod
    show IsLUB s (smashSup s)
    by_cases hne : (smashBase s).Nonempty
    · obtain ⟨q₀, hq₀⟩ := hne
      have hne : (smashBase s).Nonempty := ⟨q₀, hq₀⟩
      obtain ⟨u, hu⟩ := hs
      obtain ⟨r, rfl⟩ := exists_coe_of_mem_upperBounds_smash hne hu
      have hbdd : BddAbove (Subtype.val '' smashBase s) := by
        refine ⟨r.val, ?_⟩
        rintro _ ⟨q, hq, rfl⟩
        exact (WithBot.coe_le_coe (α := NonBotPair α β)).mp (hu (coe_mem_of_mem_smashBase hq))
      have hlub := isLUB_sSup_of_bddAbove hbdd
      have hq₀le : q₀.val ≤ sSup (Subtype.val '' smashBase s) := hlub.1 ⟨q₀, hq₀, rfl⟩
      have hguard : (sSup (Subtype.val '' smashBase s)).1 ≠ ⊥ ∧
          (sSup (Subtype.val '' smashBase s)).2 ≠ ⊥ :=
        ⟨fun hbot => q₀.2.1 (le_bot_iff.mp (le_of_le_of_eq hq₀le.1 hbot)),
          fun hbot => q₀.2.2 (le_bot_iff.mp (le_of_le_of_eq hq₀le.2 hbot))⟩
      rw [smashSup_of_ne_bot hguard]
      constructor
      · intro x hx
        induction x using WithBot.recBotCoe with
        | bot => exact bot_le
        | coe q => exact WithBot.coe_le_coe.mpr (hlub.1 ⟨q, hx, rfl⟩)
      · intro v hv
        obtain ⟨w, rfl⟩ := exists_coe_of_mem_upperBounds_smash hne hv
        refine WithBot.coe_le_coe.mpr ?_
        show sSup (Subtype.val '' smashBase s) ≤ w.val
        refine hlub.2 ?_
        rintro _ ⟨q, hq, rfl⟩
        exact (WithBot.coe_le_coe (α := NonBotPair α β)).mp (hv (coe_mem_of_mem_smashBase hq))
    · rw [smashSup_of_empty hne]
      constructor
      · intro x hx
        induction x using WithBot.recBotCoe with
        | bot => exact le_rfl
        | coe q => exact absurd ⟨q, hx⟩ hne
      · intro _ _
        exact bot_le

end Smash

section Lift

/-- The base of a set bounded above by a *coercion* is bounded above. The
hypothesis has to name the bound in `D`, not merely in `D⊥`: an upper bound of `s`
that is the adjoined bottom bounds nothing in the base. -/
theorem bddAbove_liftBase {s : Set (WithBot α)} {b : α} (hb : (↑b : WithBot α) ∈ upperBounds s) :
    BddAbove (liftBase s) :=
  ⟨b, fun _a ha => WithBot.coe_le_coe.mp (hb (coe_mem_of_mem_liftBase ha))⟩

/-- An upper bound of a set whose base is nonempty is a coercion, never the
adjoined bottom — `WithBot.not_coe_le_bot`. -/
theorem exists_coe_of_mem_upperBounds {s : Set (WithBot α)} (hne : (liftBase s).Nonempty)
    {u : WithBot α} (hu : u ∈ upperBounds s) : ∃ b : α, u = ↑b := by
  obtain ⟨a₀, ha₀⟩ := hne
  induction u using WithBot.recBotCoe with
  | bot => exact absurd (hu (coe_mem_of_mem_liftBase ha₀)) (WithBot.not_coe_le_bot a₀)
  | coe b => exact ⟨b, rfl⟩

/-- **Lemma 10, `D⊥`.** `liftSup` branches on nonemptiness of the base, not on
directedness, so the branch a *bounded* set takes is already the correct one — the
point `ScottHom`'s module docstring makes about splitting on continuity rather
than directedness. On the nonempty branch the value is `↑(sSup (liftBase s))`, and
bounded completeness of `D` makes that inner supremum a least upper bound; on the
empty branch `s ⊆ {⊥}` and the value is `⊥`. -/
theorem lemma_10_lift [Domain α] [BoundedComplete α] : BoundedComplete (WithBot α) where
  isLUB_sSup_of_bddAbove s hs := by
    show IsLUB s (liftSup s)
    by_cases hne : (liftBase s).Nonempty
    · obtain ⟨u, hu⟩ := hs
      obtain ⟨b, rfl⟩ := exists_coe_of_mem_upperBounds hne hu
      have hlub : IsLUB (liftBase s) (sSup (liftBase s)) :=
        isLUB_sSup_of_bddAbove (bddAbove_liftBase hu)
      rw [liftSup_of_nonempty hne]
      constructor
      · intro x hx
        induction x using WithBot.recBotCoe with
        | bot => exact bot_le
        | coe a => exact WithBot.coe_le_coe.mpr (hlub.1 hx)
      · intro v hv
        obtain ⟨c, rfl⟩ := exists_coe_of_mem_upperBounds hne hv
        exact WithBot.coe_le_coe.mpr
          (hlub.2 fun a ha => WithBot.coe_le_coe.mp (hv (coe_mem_of_mem_liftBase ha)))
    · rw [liftSup_of_empty hne]
      constructor
      · intro x hx
        induction x using WithBot.recBotCoe with
        | bot => exact le_rfl
        | coe a => exact absurd ⟨a, hx⟩ hne
      · intro _ _
        exact bot_le

end Lift

section Strict

/-- **Lemma 10, `D →⊥ E`.** `StrictHom α β` is a subtype of `ScottHom α β` whose
`sSup` is the ambient one — `isStrict_sSup` shows strictness survives *every*
supremum, so there is no branch to get wrong. Bounded completeness therefore
transports along the subtype: a bound in `D →⊥ E` gives a bound on the image in
`D → E`, `ScottHom`'s own `BoundedComplete` instance (Theorem 7's first sentence)
supplies the least upper bound there, and the order on the subtype is the ambient
order restricted, so the same element is least upper bound of `s`. -/
theorem lemma_10_strict [Domain α] [BoundedComplete α] [Domain β] [BoundedComplete β] :
    BoundedComplete (StrictHom α β) where
  isLUB_sSup_of_bddAbove s hs := by
    obtain ⟨u, hu⟩ := hs
    have hb : BddAbove (Subtype.val '' s) := ⟨u.val, by rintro _ ⟨f, hf, rfl⟩; exact hu hf⟩
    have hlub : IsLUB (Subtype.val '' s) (sSup (Subtype.val '' s)) :=
      isLUB_sSup_of_bddAbove hb
    constructor
    · intro f hf
      show f.val ≤ sSup (Subtype.val '' s)
      exact hlub.1 ⟨f, hf, rfl⟩
    · intro v hv
      show sSup (Subtype.val '' s) ≤ v.val
      exact hlub.2 (by rintro _ ⟨f, hf, rfl⟩; exact hv hf)

end Strict

/- Axiom audit, by `#print axioms` (run, then removed so the build emits no `info`
lines): `lemma_10_prod` depends on `[propext, Quot.sound]`; `lemma_10_smash`,
`lemma_10_lift` and `lemma_10_strict` on `[propext, Classical.choice, Quot.sound]` —
`Classical.choice` entering through the `dite` in `smashSup`, in `liftSup` and in
`ScottHom`'s `sSup`. None depends on `sorryAx`. -/

end ScottDomains
