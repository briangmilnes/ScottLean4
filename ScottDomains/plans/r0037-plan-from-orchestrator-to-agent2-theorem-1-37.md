---
round: r0037
from: orchestrator
to: agent2
subject: theorem-1-37
date: 2026-0807-11:09
status: pending
related:
  - plans/r0037-plan-from-orchestrator-to-orchestrator-last-four.md
---

# r0037 stream 2 — agent2 — Theorem 18's step 1: Jung's Theorem 1.37

Worktree `/home/milnes/projects/ScottLean4-agent2`, branch `agent2`.
Namespace **`ScottDomains.JungNets`**.

## The goal

Jung 1989's **Theorem 1.37**: if `[D → D]` is continuous then `K(D)` has
**property m** — every finite subset has a *complete* set of minimal upper
bounds. This is Gunter & Scott's Figure 3a, and it is step 1 of the five-step
route to Theorem 18 mapped in `ScottDomains/Section62.lean:157–163`.

You wrote `JungSFP.lean` last round, so you know the terrain. What you left is
precisely this: `JungSFP.lemma217` **carries `HasCompleteMub (compacts D)
{a₁, a₂}` as an explicit hypothesis** (`JungSFP.lean:101`, `:186`), because
Jung's Lemma 2.17 needs "exactly one", not "at most one", and property m is what
supplies it. Discharging that hypothesis is this stream.

## Why this is a separate development, not a proof script

Your own r0037 hand-off said it, and this plan takes it at face value: Theorem
1.37 needs **ordinal-indexed codirected nets, an interpolation step, and a
retraction onto `A ∪ αᵒᵖ`**, and nothing in `ScottDomains/` quantifies over any
of it. Expect to build machinery before proving anything.

This is the **largest unbuilt prerequisite left in the whole development**, and
the orchestrator's forecast is that it may not land. That is planned for: see the
ranked acceptance list. Do not compress the machinery to reach the headline —
a correct partial development that another round finishes is worth more than a
rushed whole.

## Suggested order

1. **Read Theorem 1.37 and its supporting numbered results in Jung 1989
   directly** before writing any Lean, and write down the actual dependency list.
   The plan's three-item summary above is second-hand, from a report; the source
   is on disk. If Jung's proof routes through results the development already has
   — `MinimalUpperBounds.lean` has `mubIter`, `mubClosure`, and
   `isPlotkinOrder_iff_mubClosure` — say so and take the shortcut.
2. **Survey Mathlib for the net/ordinal machinery** before building it.
   `Order.Ideal`, `Filter`, `Ordinal`, `Set.Finite` and the `Directed` API are
   all present; the question is whether codirected nets indexed by an ordinal are
   expressible over them without a new structure. Report the measurement either
   way — it is worth knowing even if the answer is no.
3. Only then build.

## Where it plugs in

`HasCompleteMub` is already defined in `JungSFP.lean` (see the docstring at
`:29`, and `:180` for why it quantifies over upper bounds *in `A`*). Your
conclusion should be exactly `HasCompleteMub (compacts D) u` for finite `u`, so
that `lemma217`'s hypothesis is discharged by application and nothing has to be
restated. **Match the existing shape rather than inventing a new one** — if the
shapes disagree, that is a finding to report, not a reason to change
`JungSFP.lean`.

## Acceptance, ranked

1. Theorem 1.37 proved: `[D → D]` continuous ⟹ property m for `K(D)`, with
   `lemma217`'s hypothesis discharged. Combined with agent1's stream this closes
   `thm18` and takes the development to **0 `sorry`**.
2. The net/ordinal machinery built and the proof reduced to a named, precisely
   located remainder — stated as a `Prop`, not a `sorry`.
3. The machinery alone, general and reusable, with a written statement of what
   Theorem 1.37 still needs from it.
4. A precise written obstruction: which of Jung's steps has no counterpart here,
   what it would cost, and whether Mathlib supplies any of it. `Section62.lean`
   is the template for how to write one, and that write-up was r0034's accepted
   deliverable for this same theorem.

**No new `sorry`.**

## Process rules

1. Namespace `ScottDomains.JungNets`. Import `JungSFP` and `MinimalUpperBounds`;
   do not add declarations to them. In particular **do not edit `JungSFP.lean`** —
   agent1 is reading it this round.
2. Edit/Write only. Never a heredoc, never `sed -i`.
3. One command per Bash call. Never chain, never `cd`.
4. Multi-step work becomes a script in `scripts/` — standing-authorized — but
   **check `scripts/` first and prefix any new script with your stream name**;
   r0036 lost a merge to two agents writing the same filename.
5. Build with `/home/milnes/projects/ScottLean4-agent2/scripts/compile.sh -r r0037`.
6. Read Jung 1989 directly; Abramsky & Jung 1994 §4.3 covers the same material
   and is also in `ScottDomains/papers/`.
7. **This plan is not evidence** — and this stream's description in particular is
   second-hand from your own r0036 report rather than from the source. The source
   wins; say so in the report.
8. Commit at every stopping point with
   `/home/milnes/projects/ScottLean4-agent2/scripts/gitcp.sh`. Do not push.
9. Report to
   `ScottDomains/reports/r0037-report-from-agent2-to-orchestrator-theorem-1-37.md`
   with `started`/`finished`, the Mathlib survey result, and what remains.
