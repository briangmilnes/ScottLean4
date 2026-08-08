import ScottDomains.Skeleton.Sum
import ScottDomains.Isomorphism.Copair
import ScottDomains.Isomorphism.StrictCurry

/-!
# r0038 audit evidence: three duplicate declarations in the `Audit.Skeleton` area

Round r0038 classified the 170 `theorem`/`lemma` declarations of `Skeleton/*`,
`ClosureProperties*` and `Isomorphism/*`. Three pairs came back labelled `D` —
the same statement carried under two names in two modules. "Looks the same" is
not a measurement, so this file turns each claim into something the kernel
checks. It adds no mathematics: every proof below is `rfl`.

**How `rfl` is the evidence.** Each equation names one declaration from each
module and asserts the two are equal. The equation is *well-typed only if the two
declarations have definitionally equal statements* — which is exactly the
duplicate claim. `rfl` then closes it: for the `Prop`-valued pair by Lean 4's
definitional proof irrelevance, for the `smashPair` pair by unfolding two `dite`
bodies that are character-for-character identical. So a build that accepts this
file has checked the duplication, and a later edit that makes either pair diverge
breaks this file rather than passing unnoticed — which is what `docs/PropertiesVsTheorems.md`
§5 item 2 records as having happened once already, in r0028, invisible to
`lake build` for 971 jobs because no module imported both halves.

**Nothing here is deleted or edited.** The audit round changes no proof; the
follow-on round decides which name of each pair survives.

| # | Pair | Declared at | Declared at |
| -- | ---- | ----------- | ----------- |
| 1 | `sumBase_nonempty_of_isLUB_coe` | `Skeleton/Sum.lean:357` | `Isomorphism/Copair.lean:236` |
| 2 | `smashPair` (the `def` both lemma pairs rest on) | `Skeleton/Sum.lean:689` | `Isomorphism/StrictCurry.lean:134` |
| 3 | `smashPair_of_bot`, and `smashPair_of_ne_bot` ≡ `smashPair_of_ne` | `Skeleton/Sum.lean:692,696` | `Isomorphism/StrictCurry.lean:137,140` |

Row 2 is the cause of row 3: the two `smashPair` definitions are the same
`dite`, written twice, so every lemma about either is a lemma about both.
-/

namespace ScottDomains.Audit.Skeleton

open ScottDomains

variable {α β : Type*} [CompletePartialOrder α] [CompletePartialOrder β]

/-! ### Pair 1 — `sumBase_nonempty_of_isLUB_coe`

`ScottDomains.sumBase_nonempty_of_isLUB_coe` (`Skeleton/Sum.lean`, proved by
`rcases Set.eq_empty_or_nonempty`) and
`ScottDomains.Isomorphism.sumBase_nonempty_of_isLUB_coe` (`Isomorphism/Copair.lean`,
proved by `by_contra`) differ in bound-variable names — `r` against `q`, `h`
against `hw` — and in the type variables the enclosing `variable` line supplies,
`(α, β)` against `(β, γ)`. Neither difference is visible in the statement. -/

/-- The two declarations are one proposition: the equation typechecks only if
both sides accept the same `h` and return the same `Prop`. -/
theorem sumBase_nonempty_of_isLUB_coe_dup {s : Set (CoalescedSum α β)}
    {r : NonBotSum α β} (h : IsLUB s (↑r : CoalescedSum α β)) :
    _root_.ScottDomains.sumBase_nonempty_of_isLUB_coe h
      = _root_.ScottDomains.Isomorphism.sumBase_nonempty_of_isLUB_coe h :=
  rfl

/-! ### Pair 2 — `smashPair`

Both modules define, under `open Classical in`,

    noncomputable def smashPair (p : α × β) : Smash α β :=
      if h : p.1 ≠ ⊥ ∧ p.2 ≠ ⊥ then ↑(⟨p, h⟩ : NonBotPair α β) else ⊥

with the same `Classical.propDecidable` instance, so the two are definitionally
equal and `rfl` suffices — no `funext`, no case split on the guard. -/

/-- `Skeleton/Sum.lean`'s pairing and `Isomorphism/StrictCurry.lean`'s are the
same function, not merely extensionally equal ones. -/
theorem smashPair_dup :
    (_root_.ScottDomains.smashPair : α × β → Smash α β)
      = (_root_.ScottDomains.Isomorphism.smashPair : α × β → Smash α β) :=
  rfl

/-! ### Pair 3 — the two lemmas about `smashPair`

Because pair 2 holds definitionally, each lemma statement about one `smashPair`
*is* the corresponding statement about the other, and the same
proof-irrelevance argument as pair 1 applies. -/

/-- `ScottDomains.smashPair_of_ne_bot` and `ScottDomains.Isomorphism.smashPair_of_ne`
are one proposition under two names. -/
theorem smashPair_of_ne_bot_dup {p : α × β} (h : p.1 ≠ ⊥ ∧ p.2 ≠ ⊥) :
    _root_.ScottDomains.smashPair_of_ne_bot h
      = _root_.ScottDomains.Isomorphism.smashPair_of_ne h :=
  rfl

/-- The two `smashPair_of_bot`s share a name as well as a statement; only the
namespace separates them. -/
theorem smashPair_of_bot_dup {p : α × β} (h : ¬ (p.1 ≠ ⊥ ∧ p.2 ≠ ⊥)) :
    _root_.ScottDomains.smashPair_of_bot h
      = _root_.ScottDomains.Isomorphism.smashPair_of_bot h :=
  rfl

end ScottDomains.Audit.Skeleton
