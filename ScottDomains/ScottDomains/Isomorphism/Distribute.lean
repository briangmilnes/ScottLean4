import ScottDomains.Smash
import ScottDomains.CoalescedSum
import Mathlib.Order.Hom.WithTopBot

/-!
# Lemma 9, part 5: the smash product distributes over the coalesced sum

Gunter & Scott, *Semantic Domains*, Lemma 9.5, in its corrected form:

> `D ⊗ (E ⊕ F) ≅ (D ⊗ E) ⊕ (D ⊗ F)`.

(The page prints `(D ⊗ E) ⊕ (D ⊗ E)`, which is false; the refutation is
`Skeleton/Recovered.lean`'s `lemma_9_5_printed_false`, and the recovery evidence is
`docs/StatementRecovery.md`.)

## Both sides are `WithBot` of the same base

`Smash X Y = WithBot (NonBotPair X Y)` and `CoalescedSum X Y =
WithBot (NonBotSum X Y)`, so each side of the law adjoins one bottom to a base,
and the base is the same on both sides:

* the left base is `{(x, w) | x ≠ ⊥, w ≠ ⊥}` with `w` in `E ⊕ F`, and `w ≠ ⊥`
  means `w = ↑q` for a unique injection `q`;
* the right base is the non-bottom injections of `(D ⊗ E) ⊕ (D ⊗ F)`, and a
  non-bottom element of a smash is again a unique non-bottom pair.

Both therefore reduce to `NonBotPair D E ⊕ NonBotPair D F` with `Sum`'s
**disjoint** order (`Mathlib.Data.Sum.Order`), and the law is
`OrderIso.withBotCongr` applied to the composite. No continuity obligation
arises — an order isomorphism between cpos preserves every least upper bound.

The disjointness is what makes the order match. Two elements of the left base
are comparable only when their `E ⊕ F` components are on the same side, because
`Sum`'s order relates only same-side elements; that is precisely the condition
under which the corresponding elements of the right base are comparable.
-/

namespace ScottDomains.Isomorphism

open ScottDomains

variable {α β γ : Type*}
variable [CompletePartialOrder α] [CompletePartialOrder β] [CompletePartialOrder γ]

/-! ### The left base -/

/-- Distributing a fixed non-bottom `x : D` across an injection of `E ⊕ F`. -/
def splitNonBotPair (x : α) (hx : x ≠ ⊥) :
    ∀ s : β ⊕ γ, IsNonBotSum s → NonBotPair α β ⊕ NonBotPair α γ
  | Sum.inl y, h => Sum.inl ⟨(x, y), hx, h⟩
  | Sum.inr z, h => Sum.inr ⟨(x, z), hx, h⟩

/-- The inverse of `splitNonBotPair`: re-pairing into `D ⊗ (E ⊕ F)`'s base. -/
def joinNonBotPair :
    NonBotPair α β ⊕ NonBotPair α γ → NonBotPair α (CoalescedSum β γ)
  | Sum.inl q =>
    ⟨(q.1.1, ((⟨Sum.inl q.1.2, q.2.2⟩ : NonBotSum β γ) : CoalescedSum β γ)),
      q.2.1, WithBot.coe_ne_bot⟩
  | Sum.inr q =>
    ⟨(q.1.1, ((⟨Sum.inr q.1.2, q.2.2⟩ : NonBotSum β γ) : CoalescedSum β γ)),
      q.2.1, WithBot.coe_ne_bot⟩

/-- `D ⊗ (E ⊕ F)`'s base is `NonBotPair D E ⊕ NonBotPair D F`. -/
def distribLeft :
    NonBotPair α (CoalescedSum β γ) ≃o NonBotPair α β ⊕ NonBotPair α γ where
  toFun p :=
    splitNonBotPair p.1.1 p.2.1 (WithBot.unbot p.1.2 p.2.2).1 (WithBot.unbot p.1.2 p.2.2).2
  invFun := joinNonBotPair
  left_inv p := by
    obtain ⟨⟨x, w⟩, hx, hw⟩ := p
    induction w using WithBot.recBotCoe with
    | bot => exact absurd rfl hw
    | coe q =>
      obtain ⟨s, hs⟩ := q
      cases s with
      | inl y => rfl
      | inr z => rfl
  right_inv u := by
    cases u with
    | inl q => rfl
    | inr q => rfl
  map_rel_iff' := by
    intro a b
    obtain ⟨⟨xa, wa⟩, hxa, hwa⟩ := a
    obtain ⟨⟨xb, wb⟩, hxb, hwb⟩ := b
    induction wa using WithBot.recBotCoe with
    | bot => exact absurd rfl hwa
    | coe qa =>
      induction wb using WithBot.recBotCoe with
      | bot => exact absurd rfl hwb
      | coe qb =>
        obtain ⟨sa, hsa⟩ := qa
        obtain ⟨sb, hsb⟩ := qb
        cases sa with
        | inl ya =>
          cases sb with
          | inl yb =>
            constructor
            · intro h
              have h' := Sum.inl_le_inl_iff.mp h
              exact ⟨h'.1, (WithBot.coe_le_coe (α := NonBotSum β γ)).mpr
                (Sum.inl_le_inl_iff.mpr h'.2)⟩
            · intro h
              exact Sum.inl_le_inl_iff.mpr ⟨h.1, Sum.inl_le_inl_iff.mp
                ((WithBot.coe_le_coe (α := NonBotSum β γ)).mp h.2)⟩
          | inr zb =>
            constructor
            · intro h
              exact absurd h (by simp [splitNonBotPair])
            · intro h
              exact absurd (show (Sum.inl ya : β ⊕ γ) ≤ Sum.inr zb from
                (WithBot.coe_le_coe (α := NonBotSum β γ)).mp h.2) (by simp)
        | inr za =>
          cases sb with
          | inl yb =>
            constructor
            · intro h
              exact absurd h (by simp [splitNonBotPair])
            · intro h
              exact absurd (show (Sum.inr za : β ⊕ γ) ≤ Sum.inl yb from
                (WithBot.coe_le_coe (α := NonBotSum β γ)).mp h.2) (by simp)
          | inr zb =>
            constructor
            · intro h
              have h' := Sum.inr_le_inr_iff.mp h
              exact ⟨h'.1, (WithBot.coe_le_coe (α := NonBotSum β γ)).mpr
                (Sum.inr_le_inr_iff.mpr h'.2)⟩
            · intro h
              exact Sum.inr_le_inr_iff.mpr ⟨h.1, Sum.inr_le_inr_iff.mp
                ((WithBot.coe_le_coe (α := NonBotSum β γ)).mp h.2)⟩

/-! ### The right base -/

/-- A non-bottom injection of `(D ⊗ E) ⊕ (D ⊗ F)` names a non-bottom pair. -/
def unsmashSum :
    ∀ s : Smash α β ⊕ Smash α γ, IsNonBotSum s → NonBotPair α β ⊕ NonBotPair α γ
  | Sum.inl z, h => Sum.inl (WithBot.unbot z h)
  | Sum.inr z, h => Sum.inr (WithBot.unbot z h)

/-- The inverse of `unsmashSum`. -/
def resmashSum :
    NonBotPair α β ⊕ NonBotPair α γ → NonBotSum (Smash α β) (Smash α γ)
  | Sum.inl q => ⟨Sum.inl ((q : Smash α β)), WithBot.coe_ne_bot⟩
  | Sum.inr q => ⟨Sum.inr ((q : Smash α γ)), WithBot.coe_ne_bot⟩

/-- `(D ⊗ E) ⊕ (D ⊗ F)`'s base is the same `NonBotPair D E ⊕ NonBotPair D F`. -/
def distribRight :
    NonBotSum (Smash α β) (Smash α γ) ≃o NonBotPair α β ⊕ NonBotPair α γ where
  toFun p := unsmashSum p.1 p.2
  invFun := resmashSum
  left_inv p := by
    obtain ⟨s, hs⟩ := p
    cases s with
    | inl z =>
      apply Subtype.ext
      show Sum.inl ((WithBot.unbot z hs : NonBotPair α β) : Smash α β) = Sum.inl z
      rw [WithBot.coe_unbot]
    | inr z =>
      apply Subtype.ext
      show Sum.inr ((WithBot.unbot z hs : NonBotPair α γ) : Smash α γ) = Sum.inr z
      rw [WithBot.coe_unbot]
  right_inv u := by
    cases u with
    | inl q => rfl
    | inr q => rfl
  map_rel_iff' := by
    intro a b
    obtain ⟨sa, hsa⟩ := a
    obtain ⟨sb, hsb⟩ := b
    cases sa with
    | inl za =>
      cases sb with
      | inl zb =>
        constructor
        · intro h
          exact Sum.inl_le_inl_iff.mpr
            ((WithBot.unbot_le_unbot_iff hsa hsb).mp (Sum.inl_le_inl_iff.mp h))
        · intro h
          exact Sum.inl_le_inl_iff.mpr
            ((WithBot.unbot_le_unbot_iff hsa hsb).mpr (Sum.inl_le_inl_iff.mp h))
      | inr zb =>
        constructor
        · intro h
          exact absurd h (by simp [unsmashSum])
        · intro h
          exact absurd
            (show (Sum.inl za : Smash α β ⊕ Smash α γ) ≤ Sum.inr zb from h) (by simp)
    | inr za =>
      cases sb with
      | inl zb =>
        constructor
        · intro h
          exact absurd h (by simp [unsmashSum])
        · intro h
          exact absurd
            (show (Sum.inr za : Smash α β ⊕ Smash α γ) ≤ Sum.inl zb from h) (by simp)
      | inr zb =>
        constructor
        · intro h
          exact Sum.inr_le_inr_iff.mpr
            ((WithBot.unbot_le_unbot_iff hsa hsb).mp (Sum.inr_le_inr_iff.mp h))
        · intro h
          exact Sum.inr_le_inr_iff.mpr
            ((WithBot.unbot_le_unbot_iff hsa hsb).mpr (Sum.inr_le_inr_iff.mp h))

/-- **Lemma 9.5**, as a named map: `D ⊗ (E ⊕ F) ≅ (D ⊗ E) ⊕ (D ⊗ F)`. -/
def smashDistribCoalescedSum :
    Smash α (CoalescedSum β γ) ≃o CoalescedSum (Smash α β) (Smash α γ) :=
  (distribLeft.trans distribRight.symm).withBotCongr

end ScottDomains.Isomorphism
