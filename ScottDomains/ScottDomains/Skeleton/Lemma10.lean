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
here. The remaining conjuncts are open, one statement each so they can be
discharged independently.

**Owned by agent1.** No other file's declarations are edited when these are
proved.
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
theorem lem10_prod [Domain α] [BoundedComplete α] [Domain β] [BoundedComplete β] :
    BoundedComplete (α × β) where
  isLUB_sSup_of_bddAbove s hs := by
    have hsup : (sSup s : α × β) = (sSup (Prod.fst '' s), sSup (Prod.snd '' s)) := rfl
    rw [isLUB_prod, hsup]
    exact ⟨isLUB_sSup_of_bddAbove (bddAbove_fst_image hs),
      isLUB_sSup_of_bddAbove (bddAbove_snd_image hs)⟩

end Prod

theorem lem10_smash [Domain α] [BoundedComplete α] [Domain β] [BoundedComplete β] :
    BoundedComplete (Smash α β) := by
  sorry

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
theorem lem10_lift [Domain α] [BoundedComplete α] : BoundedComplete (WithBot α) where
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
theorem lem10_strict [Domain α] [BoundedComplete α] [Domain β] [BoundedComplete β] :
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

end ScottDomains
