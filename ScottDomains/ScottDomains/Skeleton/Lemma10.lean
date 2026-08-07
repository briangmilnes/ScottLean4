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

theorem lem10_lift [Domain α] [BoundedComplete α] : BoundedComplete (WithBot α) := by
  sorry

theorem lem10_strict [Domain α] [BoundedComplete α] [Domain β] [BoundedComplete β] :
    BoundedComplete (StrictHom α β) := by
  sorry

end ScottDomains
