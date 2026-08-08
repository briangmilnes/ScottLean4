import ScottDomains.Lift
import ScottDomains.Smash
import ScottDomains.CoalescedSum
import ScottDomains.UniformFixedPoint

/-!
# r0038 audit evidence: the duplicate declarations of `Audit.Foundations`

This module proves nothing new about domains. It exists to turn three claims of
the r0038 audit report from "these declarations look the same" into statements
the kernel has checked, which is the one `.lean` addition the round's plan
permits (`plans/r0038-plan-…-theorem-audit.md`, deliverable 3).

It is deliberately import-heavy and result-free: every declaration below is an
`example` or a `theorem` whose statement is an identity between two existing
statements. Nothing in the development imports it.

## Claim 1 — `liftBase`, `smashBase` and `sumBase` are one definition, three times

`Lift.lean`, `Smash.lean` and `CoalescedSum.lean` each build their construction
as `WithBot γ` over a base type `γ` (`α`, `NonBotPair α β`, `NonBotSum α β`), and
each then defines "the non-bottom part of a set" and proves the same two facts
about it:

| # | Lift | Smash | CoalescedSum |
| -- | ---- | ----- | ------------ |
| 1 | `coe_mem_of_mem_liftBase` | `coe_mem_of_mem_smashBase` | `coe_mem_of_mem_sumBase` |
| 2 | `directedOn_liftBase` | `directedOn_smashBase` | `directedOn_sumBase` |

`withBotBase`, `coe_mem_withBotBase` and `directedOn_withBotBase` below are the
one definition and the two lemmas at an abstract `[Preorder γ]`. The six
`example`s then derive each of the six existing statements by application alone —
no tactic, no rewriting — which is the evidence that the six carry no content
beyond the two. `directedOn_withBotBase`'s proof is `directedOn_liftBase`'s,
verbatim except that the ambient type is a variable.

## Claim 2 — `directedOn_val_smashBase` is an instance of `directedOn_val_image_subtype`

`Smash.directedOn_val_smashBase` is `UniformFixedPoint.directedOn_val_image_subtype`
at the predicate `fun p : α × β => p.1 ≠ ⊥ ∧ p.2 ≠ ⊥`. The two modules are in
disjoint import cones, which is why neither cites the other.

## Claim 3 — `eq_kleeneOperator_op` and `theorem3` are the same proposition

`UniformFixedPoint.eq_kleeneOperator_op` restates `theorem3` with
`kleeneOperator.op D f` in place of `kleeneFix ⇑f`, and its proof is the single
term `theorem3 F hF D f`. Since `kleeneOperator.op` reduces to `kleeneFix ⇑·`,
the two statements are not merely equivalent but definitionally equal, which
`Iff.rfl` below records.
-/

namespace ScottDomains.Audit.Foundations

open ScottDomains

/-! ## Claim 1 -/

/-- The non-bottom part of a set in `WithBot γ`. This is `liftBase`, `smashBase`
and `sumBase` with the base type left a variable. -/
def withBotBase {γ : Type*} (s : Set (WithBot γ)) : Set γ :=
  {q : γ | (↑q : WithBot γ) ∈ s}

/-- Membership in the base is membership of the coercion. Needs no order at all:
the proof is the identity, exactly as in all three copies. -/
theorem coe_mem_withBotBase {γ : Type*} {s : Set (WithBot γ)} {q : γ}
    (h : q ∈ withBotBase s) : (↑q : WithBot γ) ∈ s := h

/-- Directedness transfers to the base, because an upper bound of two coerced
elements cannot be the adjoined bottom. This is `directedOn_liftBase`'s script
with `α` replaced by a variable `γ` at `[Preorder γ]`. -/
theorem directedOn_withBotBase {γ : Type*} [Preorder γ] {s : Set (WithBot γ)}
    (hs : DirectedOn (· ≤ ·) s) : DirectedOn (· ≤ ·) (withBotBase s) := by
  intro q₁ h₁ q₂ h₂
  obtain ⟨c, hc, hle₁, hle₂⟩ := hs _ (coe_mem_withBotBase h₁) _ (coe_mem_withBotBase h₂)
  induction c using WithBot.recBotCoe with
  | bot => exact absurd hle₁ (WithBot.not_coe_le_bot q₁)
  | coe q₃ =>
    exact ⟨q₃, hc, (WithBot.coe_le_coe (α := γ)).mp hle₁,
      (WithBot.coe_le_coe (α := γ)).mp hle₂⟩

section Instances

variable {α β : Type*} [CompletePartialOrder α] [CompletePartialOrder β]

-- `Lift.coe_mem_of_mem_liftBase`
example {s : Set (WithBot α)} {a : α} (h : a ∈ liftBase s) : (↑a : WithBot α) ∈ s :=
  coe_mem_withBotBase h

-- `Smash.coe_mem_of_mem_smashBase`
example {s : Set (Smash α β)} {q : NonBotPair α β} (h : q ∈ smashBase s) :
    (↑q : Smash α β) ∈ s :=
  coe_mem_withBotBase h

-- `CoalescedSum.coe_mem_of_mem_sumBase`
example {s : Set (CoalescedSum α β)} {q : NonBotSum α β} (h : q ∈ sumBase s) :
    (↑q : CoalescedSum α β) ∈ s :=
  coe_mem_withBotBase h

-- `Lift.directedOn_liftBase`
example {s : Set (WithBot α)} (hs : DirectedOn (· ≤ ·) s) :
    DirectedOn (· ≤ ·) (liftBase s) :=
  directedOn_withBotBase hs

-- `Smash.directedOn_smashBase`
example {s : Set (Smash α β)} (hs : DirectedOn (· ≤ ·) s) :
    DirectedOn (· ≤ ·) (smashBase s) :=
  directedOn_withBotBase hs

-- `CoalescedSum.directedOn_sumBase`
example {s : Set (CoalescedSum α β)} (hs : DirectedOn (· ≤ ·) s) :
    DirectedOn (· ≤ ·) (sumBase s) :=
  directedOn_withBotBase hs

/-! ## Claim 2 -/

-- `Smash.directedOn_val_smashBase`, from `UniformFixedPoint.directedOn_val_image_subtype`.
example {t : Set (NonBotPair α β)} (ht : DirectedOn (· ≤ ·) t) :
    DirectedOn (· ≤ ·) (Subtype.val '' t) :=
  directedOn_val_image_subtype ht

end Instances

/-! ## Claim 3 -/

universe u

/-- `theorem3` and `eq_kleeneOperator_op` are **the same proposition**, not two
equivalent ones: `Iff.rfl` discharges the equivalence, so the kernel identifies
them up to definitional unfolding of `kleeneOperator.op`. -/
theorem theorem3_statement_eq_eq_kleeneOperator_op_statement :
    (∀ (F : FixedPointOperator.{u}), F.IsUniform →
        ∀ (D : Type u) [CompletePartialOrder D] (f : ScottHom D D),
          F.op D f = kleeneFix ⇑f)
      ↔
    (∀ (F : FixedPointOperator.{u}), F.IsUniform →
        ∀ (D : Type u) [CompletePartialOrder D] (f : ScottHom D D),
          F.op D f = kleeneOperator.op D f) :=
  Iff.rfl

end ScottDomains.Audit.Foundations
