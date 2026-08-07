---
round: r0030
from: orchestrator
to: agent3
subject: theorem-18
date: 2026-0806-19:55
status: pending
related:
  - plans/r0030-plan-from-orchestrator-to-orchestrator-remaining-theorems.md
  - reports/r0028-report-from-agent4-to-orchestrator-minimal-upper-bounds.md
---

# r0030 agent3 — Theorem 18, and the construction it needs first

## Goal

> **Theorem 18** (Gunter & Scott, §6.2) If `D` and `D → D` are domains, then `D`
> is bifinite.

This is the **only `sorry` in the development**. It has been attacked once and the
attempt produced a precise diagnosis rather than a proof; your task is the
construction that diagnosis names, and then the theorem.

## Worktree and ownership

Work only in `/home/milnes/projects/ScottLean4-agent3`, branch `agent3`. Never
touch `/home/milnes/projects/ScottLean4` or a sibling worktree.

You own:

- `ScottDomains/ScottDomains/ContinuousConstruction.lean` — new, yours to create;
- **`thm18`'s body only**, in `ScottDomains/ScottDomains/Skeleton/Section6.lean`.
  Every other declaration in that file — `IsClosure`, `lubClosure`, `prop15`,
  `lem19`, the shared closure API, and their helpers — is read-only for you, as
  are its imports beyond what `thm18` needs.

**Every declaration you write in your own file goes in
`namespace ScottDomains.ContinuousConstruction`.** In r0028 two agents each
defined `isClosure_sSup` and `IsClosure.apply_sSup_of_directed`; `lake build`
passed at 971 jobs because no module imported both, and the clash surfaced only
when an axiom audit finally imported the pair.

## What is already done — read this before starting

`ScottDomains/MinimalUpperBounds.lean` (r0028, 455 lines) supplies the §6.1
vocabulary the paper's proof quantifies over, all kernel-accepted:
`minimalUpperBounds`, `HasCompleteMub`, `IsMubClosed`, `mubStep` (the paper's
`U`), `mubIter` (`Uⁿ`), `mubClosure` (`U^∞`), each relativized to a subset.

Its headline result is the reduction you should start from:

    isPlotkinOrder_iff_mubClosure :
      IsPlotkinOrder A ↔ (every finite v ⊆ A has a complete set of minimal upper
                          bounds) ∧ (every finite u ⊆ A has finite mubClosure)

and `isBifinite_iff_mubClosure`, the same criterion for `IsBifinite α`. So
Theorem 18 is already reduced to exactly two obligations, to be discharged from
`[Domain α] [Domain (ScottHom α α)]`: property M on `K(D)`, and finiteness of
`U^∞(u)`. `exists_of_not_isPlotkinOrder` states Smyth's Figure 3 case split as a
theorem rather than prose.

## The obstacle, and therefore the deliverable

r0028's attempt did **not** complete any of Smyth's three cases, and case (a)
blocks first, so König's lemma was never reached. The block is prior to the case
analysis:

- the perturbing family `qₙ` that shows the compact-looking `g ⊑ id` is not
  compact has no general construction here — every natural formula, such as
  `qₙ z = ⨆ {g w | w ∈ K(D), w ⊑ z, w ∉ ↓sₙ}`, takes the least upper bound of a
  **bounded, non-directed** set, which a domain that is not bounded complete need
  not have;
- `CompactFunction.lean`'s decomposition of a compact function into a finite join
  of step functions carries `[BoundedComplete β]` — precisely the hypothesis
  Theorem 18 exists to do without.

**So the first deliverable is a constructor for continuous functions on a domain
that is not bounded complete**, in `ContinuousConstruction.lean`. Report it as a
result in its own right: it is what every later §6.2 argument will need, and it is
worth merging even if the theorem does not follow this round.

Two facts r0028 established by hand, to save you re-deriving them:

1. The witness must contradict **directedness** of `compactsBelow h`, not the
   least-upper-bound conjunct. In the worked counterexample
   `D = {⊥, a, b} ∪ {xᵢ}` with `x₀ > x₁ > …` the upper bounds of `{a, b}`, every
   `ubStep`- or step-function-shaped `h` does satisfy `⨆ compactsBelow h = h`;
   what fails is that `step a a` and `step b b`, both compact and `⊑ id`, have no
   compact upper bound `⊑ id`.
2. The entry point generalizes: algebraicity of `ScottHom α α` plus
   `exists_mem_upperBounds_of_directedOn` yields, for any finite `u ⊆ K(D)`, a
   compact `g ⊑ id` with `g k = k` on `u`.

## What to do

1. Build the constructor. State precisely what it constructs and under which
   hypotheses, and prove it continuous.
2. With it, discharge Smyth's cases: (a) a finite `u ⊆ K(D)` with no complete set
   of minimal upper bounds, (b) one whose complete set of minimal upper bounds is
   infinite, (c) one whose `U^∞(u)` is infinite. Case (c) additionally needs
   König's lemma against `Domain.countable_compacts`; search Mathlib for a
   König-style lemma before rolling your own.
3. If a case resists, land the cases that work and leave `thm18` with its `sorry`,
   reporting exactly which case blocked and why.

**Do not weaken the statement of `thm18` under any circumstances.** Its hypotheses
are `[Domain α] [Domain (ScottHom α α)]` and its conclusion is `IsBifinite α`.

## Rules

1. Build with `scripts/compile.sh` from the worktree root — it logs timing and
   peak memory. Never prefix a build with the `timeout` command; raise your Bash
   tool's own timeout parameter instead.
2. Drive errors and warnings to zero, except the `declaration uses 'sorry'`
   warning for `thm18` if you do not land it. No `set_option` to silence a linter.
3. Edit/Write only — never `sed -i`, heredocs, or shell redirection into a file.
4. Commit with `scripts/gitcp.sh` on branch `agent3`. **Do not push and do not set
   an upstream**; its push step failing with "no tracking information" is
   expected. The orchestrator reviews, merges and pushes.

## Report

Write `reports/r0030-report-from-agent3-to-orchestrator-theorem-18.md` containing:
the constructor's exact statement and what it required; whether `thm18` is proved
and kernel-accepted, with `#print axioms` showing no `sorryAx` if so; which of
Smyth's three cases are complete; the exact remaining `sorry` count; the verbatim
final `lake build` line; your commit SHAs; and for anything unproved, the specific
obstacle with the failing goal state.
