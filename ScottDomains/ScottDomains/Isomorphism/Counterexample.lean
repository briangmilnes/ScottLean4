import ScottDomains.Isomorphism.Copair
import ScottDomains.Isomorphism.Distribute
import Mathlib.Order.CompleteLattice.Lemmas

/-!
# Lemma 9, items 3 and 5: the printed statements are false

`docs/StatementRecovery.md` decodes Lemma 9 from the PDF's page content stream
and reports two misprints. The decoding is not in doubt — the bytes are read off
the file and confirmed against the rendered page — but two of the six laws are
**false as printed**:

| # | Item | Printed | Corrected |
| -- | ---- | ------- | --------- |
| 1 | 9.3 | `(E ⊕ F) ◦→ D ≅ (E ◦→ D) × (E ◦→ F)` | `(E ⊕ F) ◦→ D ≅ (E ◦→ D) × (F ◦→ D)` |
| 2 | 9.5 | `D ⊗ (E ⊕ F) ≅ (D ⊗ E) ⊕ (D ⊗ E)` | `D ⊗ (E ⊕ F) ≅ (D ⊗ E) ⊕ (D ⊗ F)` |

Both printed forms drop the third variable from the right-hand side, so each is
refuted by a witness in which the variable it drops carries the only content.
This file puts both refutations under the kernel, following the `lem10_smash`
precedent: a claim the development believes false is stated as a negation and
proved, not left as prose.

## The witnesses, and why these rather than the ones in the prose

`docs/StatementRecovery.md` separates the two sides by **cardinality**, on
`D = E = Prop` and `F = Prop × Prop` (item 3: `10` versus `8`; item 5: `5`
versus `3`). Counting the elements of a strict function space is a large
obligation under the kernel and it proves more than is needed. The witnesses
below separate the two sides by the coarsest invariant an order isomorphism
must preserve — **whether the type has one element or more than one** — which
`Equiv.subsingleton` discharges in one step:

| # | Item | Witness | Printed left side | Printed right side |
| -- | ---- | ------- | ----------------- | ------------------ |
| 1 | 9.3 | `D = PUnit`, `E = F = Prop` | one element | at least two |
| 2 | 9.5 | `D = Prop`, `E = PUnit`, `F = Prop` | at least two | one element |

Each witness is chosen so that the **corrected** law is *not* refuted by it —
`lem9_3`'s corrected right side `(E ◦→ D) × (F ◦→ D)` is `StrictHom Prop PUnit ×
StrictHom Prop PUnit`, a one-element type matching its left side, and
`lem9_5`'s corrected right side `(D ⊗ E) ⊕ (D ⊗ F)` has two elements matching
its left side. So the separation is specific to the misprint and not an artifact
of a degenerate choice of domains.

## Why `PUnit` is the sharp witness

`PUnit` is the cpo with `⊥ = ⊤`. It makes the smash product collapse — no pair
has both coordinates non-`⊥`, so `Prop ⊗ PUnit` is the one-element cpo — and it
makes the coalesced sum forget the summand — `PUnit ∖ {⊥}` is empty. Those two
collapses are exactly what the printed right-hand sides fail to track when they
name `E` where the corrected forms name `F`.
-/

namespace ScottDomains.Isomorphism

open ScottDomains

/-! ### Two general facts about a `WithBot` over an empty base -/

/-- Adjoining a bottom to an empty poset gives a one-element poset. Both
constructions in Lemma 9 are `WithBot` of a base, so this is how a witness makes
a side degenerate. -/
theorem subsingleton_withBot_of_isEmpty {X : Type*} (h : IsEmpty X) :
    Subsingleton (WithBot X) := by
  constructor
  intro a b
  induction a using WithBot.recBotCoe with
  | bot =>
    induction b using WithBot.recBotCoe with
    | bot => rfl
    | coe x => exact (h.false x).elim
  | coe x => exact (h.false x).elim

/-- `True` is not the bottom of `Prop`: `⊥` is `False`. -/
theorem true_ne_bot : (True : Prop) ≠ (⊥ : Prop) := fun h => (iff_of_eq h).mp trivial

/-! ### Item 3: `(E ⊕ F) ◦→ D ≅ (E ◦→ D) × (E ◦→ F)` is false -/

/-- Every strict continuous map into the one-element cpo is the same map. -/
theorem subsingleton_strictHom_punit {X : Type*} [Preorder X] [OrderBot X] :
    Subsingleton (StrictHom X PUnit) :=
  ⟨fun _ _ => Subtype.ext (ScottHom.ext fun _ => Subsingleton.elim _ _)⟩

/-- The identity of `Prop`, as a strict continuous map. It is the second element
of `Prop ◦→ Prop` that the printed right-hand side of item 3 cannot afford. -/
def propId : StrictHom Prop Prop := ⟨⟨_root_.id, ScottContinuous.id⟩, rfl⟩

/-- **Lemma 9.3 is false as printed.** The page prints
`(E ⊕ F) ◦→ D ≅ (E ◦→ D) × (E ◦→ F)`; on the witness `D = PUnit`,
`E = F = Prop` the left side has exactly one element — every map into `PUnit`
is the same map — while the printed right side has at least two, since its
second factor `Prop ◦→ Prop` contains both the constant-`⊥` map and the
identity. An order isomorphism is in particular a bijection, so no such
isomorphism exists.

The corrected law `lem9_3` is not touched by this witness: its right side is
`StrictHom Prop PUnit × StrictHom Prop PUnit`, which has one element, as the
left side does. -/
theorem lem9_3_printed_false :
    ¬ Nonempty (StrictHom (CoalescedSum Prop Prop) PUnit ≃o
      StrictHom Prop PUnit × StrictHom Prop Prop) := by
  rintro ⟨e⟩
  haveI : Subsingleton (StrictHom (CoalescedSum Prop Prop) PUnit) :=
    subsingleton_strictHom_punit
  have hsub : Subsingleton (StrictHom Prop PUnit × StrictHom Prop Prop) :=
    e.symm.toEquiv.subsingleton
  have h2 : (⊥ : StrictHom Prop Prop) = propId :=
    congrArg Prod.snd
      (hsub.allEq ((⊥ : StrictHom Prop PUnit), (⊥ : StrictHom Prop Prop))
        ((⊥ : StrictHom Prop PUnit), propId))
  have h3 : (⊥ : StrictHom Prop Prop).val True = propId.val True := by rw [h2]
  exact (iff_of_eq h3).mpr trivial

/-! ### Item 5: `D ⊗ (E ⊕ F) ≅ (D ⊗ E) ⊕ (D ⊗ E)` is false -/

/-- `Prop ⊗ PUnit` has no non-bottom pair: the second coordinate of one would
have to be a non-bottom element of `PUnit`. -/
theorem isEmpty_nonBotPair_punit : IsEmpty (NonBotPair Prop PUnit) :=
  ⟨fun p => p.2.2 (Subsingleton.elim _ _)⟩

theorem subsingleton_smash_punit : Subsingleton (Smash Prop PUnit) :=
  subsingleton_withBot_of_isEmpty isEmpty_nonBotPair_punit

/-- A coalesced sum of one-element cpo's has no non-bottom injection: both
summands' bottoms are deleted, and there is nothing else in either. -/
theorem isEmpty_nonBotSum_smash_punit :
    IsEmpty (NonBotSum (Smash Prop PUnit) (Smash Prop PUnit)) := by
  constructor
  intro q
  have hq := q.2
  cases hqv : q.val with
  | inl z =>
    rw [IsNonBotSum.eq_def, hqv] at hq
    exact hq (subsingleton_smash_punit.allEq _ _)
  | inr z =>
    rw [IsNonBotSum.eq_def, hqv] at hq
    exact hq (subsingleton_smash_punit.allEq _ _)

/-- **Lemma 9.5 is false as printed.** The page prints
`D ⊗ (E ⊕ F) ≅ (D ⊗ E) ⊕ (D ⊗ E)`; on the witness `D = Prop`, `E = PUnit`,
`F = Prop` the printed right side is `(Prop ⊗ PUnit) ⊕ (Prop ⊗ PUnit)`, and
`Prop ⊗ PUnit` is the one-element cpo, so both summands lose their only element
to the coalesced sum's deletion of bottoms and the whole right side has exactly
one element. The left side `Prop ⊗ (PUnit ⊕ Prop)` has two: the adjoined bottom
and the pair `(True, ↑(Sum.inr True))`.

The corrected law `lem9_5` is not touched by this witness: its right side is
`(Prop ⊗ PUnit) ⊕ (Prop ⊗ Prop)`, whose second summand supplies the second
element. `F` is precisely the variable the printed form drops. -/
theorem lem9_5_printed_false :
    ¬ Nonempty (Smash Prop (CoalescedSum PUnit Prop) ≃o
      CoalescedSum (Smash Prop PUnit) (Smash Prop PUnit)) := by
  rintro ⟨e⟩
  haveI : Subsingleton (CoalescedSum (Smash Prop PUnit) (Smash Prop PUnit)) :=
    subsingleton_withBot_of_isEmpty isEmpty_nonBotSum_smash_punit
  have hsub : Subsingleton (Smash Prop (CoalescedSum PUnit Prop)) := e.toEquiv.subsingleton
  refine WithBot.coe_ne_bot (a := ?_) (hsub.allEq _ ⊥)
  exact ⟨(True, ((⟨Sum.inr True, true_ne_bot⟩ : NonBotSum PUnit Prop) : CoalescedSum PUnit Prop)),
    true_ne_bot, WithBot.coe_ne_bot⟩

end ScottDomains.Isomorphism
