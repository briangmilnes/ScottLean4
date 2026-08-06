---
round: r0003
from: orchestrator
to: user
subject: way-below
date: 2026-0806-13:31
started: 2026-0806-13:21
finished: 2026-0806-13:31
related:
  - plans/r0003-plan-from-orchestrator-to-orchestrator-way-below.md
  - docs/PaperInventory.md
---

# r0003 — The way-below relation `≪`: result

`ScottDomains/WayBelow.lean` exists: 1 definition, 7 theorems, 117 lines,
0 `sorry`. The kernel accepted every declaration. Elapsed 10 minutes.

Four of the five acceptance criteria are met as stated. Criterion 1's predicted
job count was wrong; the corrected measurement and its cause are below.

| # | Criterion | Measurement |
| -- | --------- | ----------- |
| 1 | The module builds | `lake build` exits 0, **825 jobs** (predicted 4 — see below), 0 errors, 0 warnings, 1.5 s steady state |
| 2 | Nothing asserted unproved | `grep -c sorry` = 0; `#print axioms` on all 8 declarations shows no `sorryAx` |
| 3 | The bridge is definitional | `wayBelow_self_iff_isCompactElement := Iff.rfl`, and it typechecks |
| 4 | Mathlib unchanged, unrebuilt | no edit under `.lake/`; the 822 extra jobs are olean replays from `~/.cache/mathlib`, no elaboration |
| 5 | Inventory updated | `docs/PaperInventory.md` carries both corrections; `INDEX.md` lists the new module |

## What the file contains

| # | Declaration | Statement | Axioms used |
| -- | ----------- | --------- | ----------- |
| 1 | `WayBelow` | `∀ s u, s.Nonempty → DirectedOn (· ≤ ·) s → IsLUB s u → y ≤ u → ∃ z ∈ s, x ≤ z`, at `[Preorder α]` | none |
| 2 | `wayBelow_self_iff_isCompactElement` | `x ≪ x ↔ IsCompactElement x` | none (`Iff.rfl`) |
| 3 | `WayBelow.le` | `x ≪ y → x ≤ y` | `propext` |
| 4 | `LE.le.trans_wayBelow` | `x ≤ y → y ≪ z → x ≪ z` | none |
| 5 | `WayBelow.trans_le` | `x ≪ y → y ≤ z → x ≪ z` | none |
| 6 | `WayBelow.trans` | `x ≪ y → y ≪ z → x ≪ z` | `propext` |
| 7 | `bot_wayBelow` | `(⊥ : α) ≪ x`, at `[OrderBot α]` | none |
| 8 | `wayBelow_iff_sSup` | the `sSup` form, at `[CompletePartialOrder α]` | none |

Six of the eight depend on no axioms at all; two use `propext` only, entering
through the `Set.mem_singleton_iff` rewrite in `WayBelow.le` (and thence into
`WayBelow.trans`, which calls it). Nothing here uses `Classical.choice` or
`Quot.sound` — the development is constructive so far, and cheap to keep that way
if it is worth stating as a property of the theory.

Declaration 2 is the one worth reading. `x ≪ x` and `IsCompactElement x` are not
merely equivalent propositions; after delta-reduction they are the *same* term,
so `Iff.rfl` closes it and the kernel checks it by conversion alone. That is the
return on defining `≪` as Mathlib's `IsCompactElement` with its two occurrences
of `k` split into `x` and `y`, instead of restating the textbook form.

## Three elaboration failures, and what each one teaches

The first build produced two errors and one linter warning. None was a mistake in
the mathematics; all three are Lean 4 facts worth keeping.

**F1 — an instance diamond, reported by the `overlappingInstances` linter.** The
bridge theorem was written inside `section Preorder` (`variable [Preorder α]`)
while adding `[PartialOrder α]` to its own signature. Two instance arguments then
supply `LE α` independently, and Lean has no reason to identify them:
`≪` elaborates against `Preorder.toLE` and `IsCompactElement` against
`PartialOrder.toPreorder.toLE`. `Iff.rfl` failed with
`?m ↔ ?m` against `x ≪ x ↔ IsCompactElement x` — a *definitional* failure caused
by a *typeclass* mistake. Fixed by moving the theorem outside the section so
`[PartialOrder α]` is its only order instance. The general rule: never assume two
classes on the same carrier when one extends the other.

**F2 — dot notation does not survive an unfolded projection.** `hxy.le.trans_wayBelow hyz`
failed with `le hxy has type inst✝.toLE.1 x y which does not have the necessary
form`. Dot notation resolves the namespace from the *head constant* of the type;
`x ≤ y` had already reduced to a raw structure projection, so there was no head
constant `LE.le` to name a namespace. Fixed by writing the application out:
`LE.le.trans_wayBelow hxy.le hyz`. `hxy.le` itself works, because `WayBelow` is a
constant.

**F3** was F1's error message, counted once.

## Correction to the plan's own prediction

The plan asserted criterion 1 as "4 jobs (was 3)". Measured: 825, stable across
four consecutive builds. The cause was isolated rather than guessed — with
`WayBelow.lean` moved out of the library, `lake build` reports 3 jobs; moved back,
825. The file adds one Mathlib module to the library's import closure that was
not already there, `Mathlib.Order.CompactlyGenerated.Basic`
(`Mathlib.Order.CompletePartialOrder` is already reachable from
`ScottDomains.lean`), and lake counts every module in the transitive closure as a
job. The 822 additional jobs are cache replays, not elaboration: total wall clock
is 1.5 s, of which `WayBelow.lean` itself is 1.3 s.

The predicted figure was an assumption that lake counts only the package's own
modules. It counts the closure. Job count is therefore a measure of *import
surface*, not of work performed; wall clock and error/warning counts are the
meaningful acceptance measurements, and the plan should have said so.

## Corrections to `docs/PaperInventory.md`

1. §3.1 compact element was marked `~ IsCompactElement (lattice only → dcpo)`.
   The definition at `Mathlib/Order/CompactlyGenerated/Basic.lean:62` is stated at
   `[PartialOrder α]` and applies to a dcpo verbatim. What is `CompleteLattice`-only
   is the API: all 20 mentions in that file below `variable [CompleteLattice α]`
   (line 70). The row now says so.
2. §3.1 way-below was `✗ define`; it is now `✓ ScottDomains.WayBelow (r0003)`.
   Work counts, bottom line, and the closing tally are updated: **≈12 definitions
   and 28 results remain**, down from ≈13 and 28.

## Files changed

New: `ScottDomains/ScottDomains/WayBelow.lean` (117 lines),
`ScottDomains/plans/r0003-…-way-below.md`, this report.
Modified: `ScottDomains/docs/PaperInventory.md` (5 edits), `INDEX.md` (1 line).
Unmodified, deliberately: `ScottDomains/ScottDomains/ExistingTheories.lean` — its
docstring reserves it for *existing* Mathlib theories, and states that new
Scott-domain declarations get their own files.

## Open, for the user

1. **Next target.** Algebraic cpo and `ScottDomain`, both quantifying over `≪`
   and `IsCompactElement`, then bounded-complete — which Thm 7, Lem 10, Lem 13
   and Thm 14 all assume. This is r0004 unless you want a different order.
2. **Upstream or local.** `WayBelow` fills a real gap in `Mathlib/Order/` and
   follows Mathlib's conventions (`Preorder`-general, `IsLUB` rather than `sSup`,
   scoped notation). Whether to prepare a pull request is your call; it would
   change the naming discipline for everything built on it.
3. **Notation scope.** `≪` is `scoped[ScottDomains]`. If the tutoring sessions
   want it available without `open ScottDomains`, say so before more files depend
   on the current form.
