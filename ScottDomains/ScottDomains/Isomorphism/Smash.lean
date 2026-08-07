import ScottDomains.Smash
import Mathlib.Order.Hom.WithTopBot

/-!
# Lemma 9, parts 1 and 2: the smash product is commutative and associative

Gunter & Scott, *Semantic Domains*, Lemma 9:

> 1. `D ⊗ E ≅ E ⊗ D`,
> 2. `(D ⊗ E) ⊗ F ≅ D ⊗ (E ⊗ F)`.

`Smash α β` is `WithBot (NonBotPair α β)`, so both laws factor the same way:
prove the isomorphism on the **base** — the non-bottom pairs — and transport it
across the adjoined bottom with `OrderIso.withBotCongr`. Nothing about suprema
enters, because `≃o` between cpos already preserves every least upper bound;
`Product.lean`'s module docstring fixes that reading of the paper's `≅`.

## Why the associativity proof needs `WithBot.unbot`

Commutativity is a coordinate swap and its four `OrderIso` fields are `rfl` or
`and_comm`. Associativity is not, because the two sides nest the `WithBot`
differently: on the left the *first* coordinate of the base pair is itself a
`Smash`, on the right the second is. The common refinement is `NonBotTriple`,
the triples with no coordinate `⊥`, and reaching it means turning a hypothesis
`p.1.1 ≠ ⊥` into the pair it names. That is exactly `WithBot.unbot`, whose two
computation rules — `unbot ↑a h = a` by `rfl` and `↑(unbot x h) = x` by
`WithBot.coe_unbot` — discharge `right_inv` and `left_inv` respectively.

The order half is `WithBot.unbot_le_unbot_iff`: on non-bottom elements the
`WithBot` order and the base order agree, so the three-way conjunction on
`NonBotTriple` is a reassociation of the two-way one on either side.
-/

namespace ScottDomains.Isomorphism

open ScottDomains

variable {α β γ : Type*}
variable [CompletePartialOrder α] [CompletePartialOrder β] [CompletePartialOrder γ]

/-! ### Lemma 9.1 — commutativity -/

/-- Swapping coordinates on the base of the smash product. Both `left_inv` and
`right_inv` are `rfl`: `Prod` and `Subtype` both have definitional eta, and the
two `≠ ⊥` components are propositions, so proof irrelevance covers them. -/
def nonBotPairComm : NonBotPair α β ≃o NonBotPair β α where
  toFun p := ⟨(p.1.2, p.1.1), p.2.2, p.2.1⟩
  invFun p := ⟨(p.1.2, p.1.1), p.2.2, p.2.1⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

/-- **Lemma 9.1**, as a named map: `D ⊗ E ≅ E ⊗ D`. -/
def smashComm : Smash α β ≃o Smash β α := nonBotPairComm.withBotCongr

/-! ### Lemma 9.2 — associativity -/

/-- The triples with no coordinate `⊥`: the common refinement of the two ways of
bracketing a smash product of three cpos. -/
abbrev NonBotTriple (α β γ : Type*) [CompletePartialOrder α] [CompletePartialOrder β]
    [CompletePartialOrder γ] :=
  {t : α × β × γ // t.1 ≠ ⊥ ∧ t.2.1 ≠ ⊥ ∧ t.2.2 ≠ ⊥}

/-- `(D ⊗ E) ⊗ F`'s base is the non-bottom triples. -/
def smashAssocLeft : NonBotPair (Smash α β) γ ≃o NonBotTriple α β γ where
  toFun p :=
    ⟨((WithBot.unbot p.1.1 p.2.1).1.1, (WithBot.unbot p.1.1 p.2.1).1.2, p.1.2),
      (WithBot.unbot p.1.1 p.2.1).2.1, (WithBot.unbot p.1.1 p.2.1).2.2, p.2.2⟩
  invFun t :=
    ⟨(((⟨(t.1.1, t.1.2.1), t.2.1, t.2.2.1⟩ : NonBotPair α β) : Smash α β), t.1.2.2),
      WithBot.coe_ne_bot, t.2.2.2⟩
  left_inv p := by
    apply Subtype.ext
    show ((↑(WithBot.unbot p.1.1 p.2.1) : Smash α β), p.1.2) = p.1
    rw [WithBot.coe_unbot]
  right_inv _ := rfl
  map_rel_iff' := by
    intro a b
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨(WithBot.unbot_le_unbot_iff a.2.1 b.2.1).mp ⟨h1, h2⟩, h3⟩
    · rintro ⟨h1, h2⟩
      have h := (WithBot.unbot_le_unbot_iff a.2.1 b.2.1).mpr h1
      exact ⟨h.1, h.2, h2⟩

/-- `D ⊗ (E ⊗ F)`'s base is the same non-bottom triples. -/
def smashAssocRight : NonBotPair α (Smash β γ) ≃o NonBotTriple α β γ where
  toFun p :=
    ⟨(p.1.1, (WithBot.unbot p.1.2 p.2.2).1.1, (WithBot.unbot p.1.2 p.2.2).1.2),
      p.2.1, (WithBot.unbot p.1.2 p.2.2).2.1, (WithBot.unbot p.1.2 p.2.2).2.2⟩
  invFun t :=
    ⟨(t.1.1, ((⟨(t.1.2.1, t.1.2.2), t.2.2.1, t.2.2.2⟩ : NonBotPair β γ) : Smash β γ)),
      t.2.1, WithBot.coe_ne_bot⟩
  left_inv p := by
    apply Subtype.ext
    show (p.1.1, (↑(WithBot.unbot p.1.2 p.2.2) : Smash β γ)) = p.1
    rw [WithBot.coe_unbot]
  right_inv _ := rfl
  map_rel_iff' := by
    intro a b
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, (WithBot.unbot_le_unbot_iff a.2.2 b.2.2).mp ⟨h2, h3⟩⟩
    · rintro ⟨h1, h2⟩
      have h := (WithBot.unbot_le_unbot_iff a.2.2 b.2.2).mpr h2
      exact ⟨h1, h.1, h.2⟩

/-- **Lemma 9.2**, as a named map: `(D ⊗ E) ⊗ F ≅ D ⊗ (E ⊗ F)`. -/
def smashAssoc : Smash (Smash α β) γ ≃o Smash α (Smash β γ) :=
  (smashAssocLeft.trans smashAssocRight.symm).withBotCongr

end ScottDomains.Isomorphism
