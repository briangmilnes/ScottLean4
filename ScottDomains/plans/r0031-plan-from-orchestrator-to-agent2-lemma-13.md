---
round: r0031
from: orchestrator
to: agent2
subject: lemma-13
date: 2026-0806-20:20
status: pending
supersedes: plans/r0030-plan-from-orchestrator-to-agent1-powerdomain-bounded-complete.md
---

# r0031 agent2 — Lemma 13: the powerdomains of a bounded complete domain

## Goal

> **Lemma 13** (Gunter & Scott, §4.5) If `D` is bounded complete then so are the
> powerdomains `D]` and `D[`.

Round r0029 built all three powerdomains, so this is now a proof task over
existing constructions.

## Worktree and ownership

Work only in `/home/milnes/projects/ScottLean4-agent2`, branch `agent2`. Never
touch `/home/milnes/projects/ScottLean4` or a sibling worktree.

You own one new file:
`ScottDomains/ScottDomains/Powerdomain/BoundedComplete.lean`. Everything else is
read-only — in particular the three powerdomain modules. If a shared module
genuinely must change, stop and report rather than change it.

**Every declaration goes in `namespace ScottDomains.PowerdomainBC`.** Three
sibling agents run this round; r0029's namespace-per-agent rule produced zero
collisions against two in r0028, and it is not optional.

## What to read first

| # | File | Why |
| -- | ---- | --- |
| 1 | `ScottDomains/Powerdomain/Hoare.lean` | `Pf` the finite **non-empty** subsets of `K(D)`, the lower pre-order, `Powerdomain = IdealCompletion (Pf K(D))` |
| 2 | `ScottDomains/Powerdomain/Smyth.lean` | the upper pre-order, and `not_finsetLE_empty` — under Smyth, `∅` is a *top*, so the carrier's non-emptiness is load-bearing in the opposite direction from Hoare |
| 3 | `ScottDomains/Powerdomain/Plotkin.lean` | Egli–Milner; `principal_eq_principal_iff` shows the completion performs the convex quotient itself, and `not_single_le_pair` shows the pre-order is not a `SemilatticeSup` |
| 4 | `ScottDomains/IdealCompletion.lean` | Theorem 11 — every powerdomain is an ideal completion, so its suprema are computed there, and `idealSup` branches on `Order.IsIdeal`, not on directedness |
| 5 | `ScottDomains/Domain.lean` | the exact definition of `BoundedComplete` here |
| 6 | `ScottDomains/Skeleton/Lemma10.lean` and `Skeleton/Sum.lean` | the six r0027–r0028 proofs of bounded completeness — the model to follow |

## Statements

`lem13_hoare` and `lem13_smyth`, and `lem13_plotkin` if the paper's `D]` and `D[`
cover the convex case. Say in a docstring which of the paper's two symbols each
corresponds to; if you conclude the symbols map differently than assumed here,
say why and cite the PDF.

Hypotheses are `[Domain α] [BoundedComplete α]` on the underlying domain, matching
`Skeleton/Lemma10.lean` exactly. Do not add a hypothesis the paper does not state
without recording that you did and why.

## The obstacle to expect

Bounded completeness is about **bounded** sets, not directed ones. Three times in
this development a supremum was defined by branching on a merely *sufficient*
condition — directedness — and twice that made a `BoundedComplete` claim **false**:
`ScottHom` (repaired r0006–r0011) and `Smash` (repaired r0027, after an agent
proved the claim false by the kernel). `IdealCompletion.idealSup` branches on
`Order.IsIdeal (⋃₀ …)`, which is the membership condition and therefore correct —
but check it rather than assume it, and if a powerdomain's supremum turns out to
branch on directedness, you have found the defect a third time. Report it with a
witness; do not repair a shared module yourself.

## Rules

1. Build with `scripts/compile.sh` from the worktree root. Never prefix a build
   with the `timeout` command; raise your Bash tool's own timeout instead.
2. Errors **and** warnings to zero. No `set_option` to silence a linter.
3. Edit/Write only — never `sed -i`, heredocs, or shell redirection into a file.
4. Never weaken, generalize away, or delete a statement to make it provable. If a
   statement is false as written, prove it false and report — that is a result.
5. Commit with `scripts/gitcp.sh` on branch `agent2`. **Do not push, do not set an
   upstream**; the "no tracking information" failure is expected.

## Report

Write `reports/r0031-report-from-agent2-to-orchestrator-lemma-13.md`: which
statements are proved and kernel-accepted; `#print axioms` for each, no `sorryAx`;
which paper symbol each conjunct is; the exact `sorry` count; the verbatim final
`lake build` line; your commit SHAs; and for anything unproved, the specific
obstacle with the failing goal state.
