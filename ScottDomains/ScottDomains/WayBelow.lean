import Mathlib.Order.CompactlyGenerated.Basic
import Mathlib.Order.CompletePartialOrder

/-!
# The way-below relation `≪`

Gunter & Scott, *Semantic Domains* (Handbook of Theoretical Computer Science
Vol. B, 1990), §3.1: `x ≪ y` holds when every directed set whose least upper
bound is above `y` already contains a member above `x`. It is the approximation
relation behind compactness — *algebraic*, *domain*, and *bounded complete* are
all defined by quantifying over it — and Mathlib v4.32.2 does not have it
(0 hits for `wayBelow` in `Mathlib/Order/` and `Mathlib/Topology/Order/`).

## Design

Mathlib does have `IsCompactElement`, and its definition is *already* stated at
`[PartialOrder α]` — only the lemmas about it are confined to `CompleteLattice`.
So `WayBelow` is obtained from `IsCompactElement` by letting the element being
approximated and the element being approximated *by* vary independently, rather
than by restating the textbook form. The payoff is `wayBelow_self_iff_isCompactElement`,
which is `Iff.rfl`: on the diagonal the two notions are the same proposition, not
merely equivalent ones.

The definition lives at `[Preorder α]` and takes the least upper bound as a
hypothesis (`IsLUB s u`) rather than an operation, because a preorder has no
`SupSet`. This is the discipline `IsCompactElement` and `ScottContinuous` both
follow. `wayBelow_iff_sSup` derives the `sSup` form once, over
`CompletePartialOrder`, for use downstream.

`s.Nonempty` is a hypothesis of the definition, not a consequence of
`DirectedOn`: Gunter & Scott's *directed* asks every finite subset — including
`∅` — for an upper bound *in the set*, which forces nonemptiness, whereas
Mathlib's `DirectedOn` holds vacuously on `∅`. Carrying it explicitly matches
both conventions, and `bot_wayBelow` is false without it.

## Notation

`≪` is introduced `scoped` in the `ScottDomains` namespace. Mathlib already
uses `≪` at the same precedence for `MeasureTheory.Measure.AbsolutelyContinuous`,
also scoped, so the two coexist.
-/

namespace ScottDomains

variable {α : Type*}

/-- `WayBelow x y` (`x ≪ y`): every nonempty directed set whose least upper bound
lies above `y` already contains an element above `x`. Gunter & Scott §3.1.

Compare `IsCompactElement k`, which is this with `x` and `y` both `k`. -/
def WayBelow [Preorder α] (x y : α) : Prop :=
  ∀ (s : Set α) (u : α), s.Nonempty → DirectedOn (· ≤ ·) s → IsLUB s u → y ≤ u →
    ∃ z ∈ s, x ≤ z

@[inherit_doc] scoped infixl:50 " ≪ " => WayBelow

section Preorder

variable [Preorder α] {x y z : α}

/-- `≪` refines `≤`. Witness the definition with the directed set `{y}`, whose
least upper bound is `y` itself (`isLUB_singleton`). -/
theorem WayBelow.le (h : x ≪ y) : x ≤ y := by
  obtain ⟨w, hw, hxw⟩ :=
    h {y} y (Set.singleton_nonempty y) (directedOn_singleton y) isLUB_singleton le_rfl
  rw [Set.mem_singleton_iff] at hw
  exact hw ▸ hxw

/-- `≪` is monotone in its left argument: weaken the approximant. -/
theorem LE.le.trans_wayBelow (hxy : x ≤ y) (hyz : y ≪ z) : x ≪ z := by
  intro s u hs hd hlub hzu
  obtain ⟨w, hw, hyw⟩ := hyz s u hs hd hlub hzu
  exact ⟨w, hw, hxy.trans hyw⟩

/-- `≪` is monotone in its right argument: strengthen the element approximated.
The hypothesis `z ≤ u` of the goal supplies `y ≤ u` for `hxy` through `y ≤ z`. -/
theorem WayBelow.trans_le (hxy : x ≪ y) (hyz : y ≤ z) : x ≪ z :=
  fun s u hs hd hlub hzu => hxy s u hs hd hlub (hyz.trans hzu)

/-- `≪` is transitive. It factors through `≤`: `WayBelow.le` on the first
hypothesis, then monotonicity in the left argument. -/
theorem WayBelow.trans (hxy : x ≪ y) (hyz : y ≪ z) : x ≪ z :=
  LE.le.trans_wayBelow hxy.le hyz

/-- `⊥` is way below everything. This is where the `s.Nonempty` hypothesis of the
definition is used: it supplies the witness, and `bot_le` does the rest. -/
theorem bot_wayBelow [OrderBot α] (x : α) : (⊥ : α) ≪ x := by
  intro s _ hs _ _ _
  obtain ⟨w, hw⟩ := hs
  exact ⟨w, hw, bot_le⟩

end Preorder

/-- A compact element is exactly one that is way below itself. True by `rfl`:
`WayBelow x x` and `IsCompactElement x` are the same proposition, because
`WayBelow` generalizes `IsCompactElement`'s definition off the diagonal.

Stated outside the `[Preorder α]` section on purpose: `IsCompactElement` asks for
`[PartialOrder α]`, and assuming both in one signature builds an instance diamond
— the two `LE α` instances need not agree, and the two sides then fail to be
definitionally equal. -/
theorem wayBelow_self_iff_isCompactElement [PartialOrder α] (x : α) :
    x ≪ x ↔ IsCompactElement x := Iff.rfl

/-- The `sSup` form of `≪`, available once directed suprema are an operation
rather than a hypothesis. Both directions go through `DirectedOn.isLUB_sSup`;
the reverse also needs `IsLUB.unique` to identify the given bound with `sSup s`. -/
theorem wayBelow_iff_sSup [CompletePartialOrder α] {x y : α} :
    x ≪ y ↔ ∀ s : Set α, s.Nonempty → DirectedOn (· ≤ ·) s → y ≤ sSup s →
      ∃ z ∈ s, x ≤ z := by
  constructor
  · intro h s hs hd hy
    exact h s (sSup s) hs hd hd.isLUB_sSup hy
  · intro h s u hs hd hlub hyu
    exact h s hs hd (hyu.trans_eq (hd.isLUB_sSup.unique hlub).symm)

end ScottDomains
