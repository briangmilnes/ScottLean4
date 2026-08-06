---
round: r0003
from: orchestrator
to: orchestrator
subject: way-below
date: 2026-0806-13:20
status: done
related:
  - reports/r0003-report-from-orchestrator-to-user-way-below.md
  - plans/r0002-plan-from-orchestrator-to-orchestrator-session-restart.md
  - reports/r0001-report-from-orchestrator-to-user-toolchain-audit.md
  - docs/PaperInventory.md
---

# r0003 — The way-below relation `≪`

The first mathematics round. r0001 built the toolchain and advanced no
mathematics; `ScottDomains` is 2 modules and 59 lines, one of which is a
`#check` catalog. `docs/PaperInventory.md` names the first target: `WayBelow`,
because *compact element*, *algebraic*, *domain*, and *bounded complete* all sit
on it.

Deliverable: one new module, `ScottDomains/WayBelow.lean` — 1 definition and 7
theorems, no `sorry`.

## What Mathlib v4.32.2 does and does not have (measured, not assumed)

| # | Query | Result |
| -- | ----- | ------ |
| 1 | `wayBelow` / `WayBelow` / `way_below` in `Mathlib/Order/`, `Mathlib/Topology/Order/` | 0 hits. One bibliography line naming *continuous lattices* in `Topology/Order/HullKernel.lean:48`. The relation is absent |
| 2 | `IsCompactElement` | `Mathlib/Order/CompactlyGenerated/Basic.lean:62`, stated for `[PartialOrder α]` |
| 3 | Its lemma API | Every lemma about it lies under `variable [CompleteLattice α]` (line 70) inside `namespace CompleteLattice` (lines 72–295, 542–575). 20 mentions in the file; 0 usable on a dcpo |
| 4 | `≪` notation | Taken only by `scoped[MeasureTheory] infixl:50 " ≪ " => MeasureTheory.Measure.AbsolutelyContinuous` (`MeasureTheory/Measure/AbsolutelyContinuous.lean:53`). Scoped, so a second scoped `≪` does not collide |
| 5 | `CompletePartialOrder` | `extends PartialOrder α, SupSet α, OrderBot α` — pointed by construction; `⊥ = sSup ∅` |
| 6 | `ScottContinuous` | `ScottContinuity.lean:148`, quantifies over **nonempty** directed sets, so it does not require strictness (`f ⊥ = ⊥`) |

**Correction to `docs/PaperInventory.md`.** The §3.1 row marks compact element
`~ IsCompactElement (lattice only → dcpo)`. The classification is right about the
API and wrong about the definition: `IsCompactElement` is already stated at
`[PartialOrder α]`, so it applies verbatim to a dcpo. What is lattice-only is
every lemma proved about it. The consequence for this round is favorable — see
step 2.

## Design decisions, with the reason for each

1. **Define `≪` by generalizing Mathlib's own `IsCompactElement`, not by
   restating the textbook form.** Mathlib's definition is `IsCompactElement k :=
   ∀ (s : Set α) (u : α), s.Nonempty → DirectedOn (· ≤ ·) s → IsLUB s u → k ≤ u
   → ∃ x ∈ s, k ≤ x`. Replacing the two occurrences of `k` by `x` and `y`
   independently yields `x ≪ y`. Then `x ≪ x` is *definitionally*
   `IsCompactElement x`, and the bridge theorem is `Iff.rfl` — a kernel-checked
   identity, not a proof. Any other formulation costs a real proof and buys
   nothing.

2. **State the definition at `[Preorder α]`, using `IsLUB`, not `sSup`.** This is
   the discipline `IsCompactElement` and `ScottContinuous` both follow: a
   preorder has no `SupSet`, so the least upper bound must be a hypothesis
   (`IsLUB s u`) rather than an operation. The `sSup` form is then derived once,
   in the `CompletePartialOrder` section, as the rewriting lemma the later
   development will actually use.

3. **Notation `scoped[ScottDomains] infixl:50 " ≪ "`.** Row 4 above: `≪` at
   precedence 50 is exactly the shape `MeasureTheory` uses, and scoping keeps
   both usable in one file. Do not declare it globally.

4. **Nonemptiness stays in the definition.** Gunter & Scott's §2.1 *directed*
   requires an upper bound in `M` for every finite `u ⊆ M`, including `u = ∅`,
   which forces `M` nonempty. Mathlib's `DirectedOn` is vacuously true on `∅`
   and carries the nonemptiness separately. Keeping `s.Nonempty` explicit
   matches both the paper and `IsCompactElement`; dropping it would make `⊥ ≪ x`
   false and break step 6.

## Steps, each with its verification

| # | Step | Verify |
| -- | ---- | ------ |
| 1 | `def WayBelow [Preorder α] (x y : α) : Prop` + scoped `≪` + module docstring citing Gunter & Scott §3.1 | elaborates |
| 2 | `theorem wayBelow_self_iff_isCompactElement [PartialOrder α] (x : α) : x ≪ x ↔ IsCompactElement x := Iff.rfl` | `Iff.rfl` typechecks — if it does not, the definition in step 1 is misaligned and must be fixed there, not patched here |
| 3 | `theorem WayBelow.le : x ≪ y → x ≤ y` | witness `s := {y}`, `u := y`; `isLUB_singleton` |
| 4 | `theorem LE.le.trans_wayBelow : x ≤ y → y ≪ z → x ≪ z` | monotone in the left argument; `le_trans` on the witness |
| 5 | `theorem WayBelow.trans_le : x ≪ y → y ≤ z → x ≪ z` | antitone in the right argument; weaken the `z ≤ u` hypothesis |
| 6 | `theorem WayBelow.trans : x ≪ y → y ≪ z → x ≪ z` | steps 3–5 compose: `(h₁.le).trans_wayBelow h₂` |
| 7 | `theorem bot_wayBelow [OrderBot α] (x : α) : ⊥ ≪ x` | needs only `s.Nonempty` and `bot_le`; this is where decision 4 pays |
| 8 | `theorem wayBelow_iff_sSup [CompletePartialOrder α] : x ≪ y ↔ ∀ s, s.Nonempty → DirectedOn (· ≤ ·) s → y ≤ sSup s → ∃ z ∈ s, x ≤ z` | `DirectedOn.isLUB_sSup` in each direction |
| 9 | `lake build` | 4 jobs (was 3), 0 errors, 0 warnings, 0 `sorry` |
| 10 | Update `docs/PaperInventory.md` §3.1 rows for `≪` and compact element | the two corrections above recorded, `~`/`✗` marks re-derived |
| 11 | Update root `INDEX.md` with `ScottDomains/WayBelow.lean` | per `CLAUDE.md` repository-workflow section |

Steps 3–8 are independent of one another given step 1; only step 6 consumes
3–5. Span is therefore 3 sequential elaborations, not 8.

## Acceptance criteria

| # | Criterion | Measurement |
| -- | --------- | ----------- |
| 1 | The module builds | `cd ScottDomains && lake build` exits 0, 4 jobs, 0 errors, 0 warnings |
| 2 | Nothing is asserted unproved | `grep -c sorry ScottDomains/WayBelow.lean` = 0; the kernel accepted all 7 theorems |
| 3 | The bridge is definitional | step 2 is `Iff.rfl`, not a tactic proof |
| 4 | Mathlib is unchanged and unrebuilt | no edit under `.lake/`; build does not re-elaborate Mathlib (disk is at 97%, 15 GiB free — r0001 §Facts) |
| 5 | The inventory reflects what was learned | `docs/PaperInventory.md` carries the two corrections |

## Explicitly out of scope for r0003

`algebraic` cpo, `ScottDomain`, `bounded complete`, embedding–projection pairs,
finitary projections, and every one of the paper's 30 numbered results. Those
are r0004 and later. This round delivers the single relation the four
definitions above all quantify over, and nothing else.

The full remaining work stands at ≈13 definitions and 28 results
(`docs/PaperInventory.md`); this round closes 1 definition, leaving ≈12.

## Open question for the user

`WayBelow` follows Mathlib's naming and generality conventions closely enough to
be upstreamable — the way-below relation is a genuine gap in `Mathlib/Order/`.
Whether to prepare it as a Mathlib pull request, or keep the development local to
`ScottDomains`, is a decision for after the file exists, not before.
