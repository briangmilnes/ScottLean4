---
round: r0030
from: orchestrator
to: agent1
subject: powerdomain-bounded-complete
date: 2026-0806-19:55
status: pending
related:
  - plans/r0030-plan-from-orchestrator-to-orchestrator-remaining-theorems.md
---

# r0030 agent1 — Lemma 13: the powerdomains of a bounded complete domain

## Goal

> **Lemma 13** (Gunter & Scott, §4.5) If `D` is bounded complete then so are the
> powerdomains `D]` and `D[`.

Prove it over the powerdomain constructions that round r0029 landed.

## Worktree and ownership

Work only in `/home/milnes/projects/ScottLean4-agent1`, branch `agent1`. Never
touch `/home/milnes/projects/ScottLean4` or a sibling worktree.

You own exactly one new file: `ScottDomains/ScottDomains/Powerdomain/BoundedComplete.lean`.
Everything else is read-only. If a shared module genuinely must change, stop and
report rather than change it.

**Every declaration you write goes in `namespace ScottDomains.PowerdomainBC`.**
Four agents run this round. In r0028 two of them each defined `isClosure_sSup`
and `IsClosure.apply_sSup_of_directed`; `lake build` passed at 971 jobs because
no module imported both, and the clash surfaced only when an axiom audit finally
imported the pair. A namespace per agent makes that impossible.

## What to read first

| # | File | Why |
| -- | ---- | --- |
| 1 | `ScottDomains/Powerdomain/Hoare.lean`, `Smyth.lean`, `Plotkin.lean` | the r0029 constructions — the carriers, the pre-orders, the `Domain` instances |
| 2 | `ScottDomains/IdealCompletion.lean` | Theorem 11; every powerdomain is an ideal completion, so its suprema are computed there |
| 3 | `ScottDomains/Domain.lean` | the exact definition of `BoundedComplete` in this development |
| 4 | `ScottDomains/Skeleton/Lemma10.lean` | the four r0027 proofs of bounded completeness for `×`, `⊗`, `()⊥`, `→⊥` — the model to follow |
| 5 | `papers/Gunter Scott 1990.pdf`, §4.5 and §5 | the statement and the paper's argument |

## Statements to prove

State one theorem per powerdomain, named `lem13_hoare`, `lem13_smyth`, and
`lem13_plotkin` if the paper's `D]` and `D[` cover it. Say in a docstring which
of the paper's two symbols each corresponds to; the PDF's `]` and `[` are the
Hoare and Smyth powerdomains, and if you conclude otherwise, say why.

Hypotheses are `[Domain α] [BoundedComplete α]` on the underlying domain, matching
`Skeleton/Lemma10.lean`'s shape exactly. Do not add hypotheses the paper does not
state without recording that you did and why.

## The obstacle to expect

Bounded completeness is a statement about **bounded** sets, not directed ones.
Twice in this development a supremum was defined by branching on a merely
*sufficient* condition — directedness — and each time it made a `BoundedComplete`
claim **false**: `ScottHom` (repaired r0006–r0011) and `Smash` (repaired r0027,
after an agent proved the claim false by the kernel). If a powerdomain's `sSup`
turns out to branch on directedness, you have found the same defect a fourth
time. Report it with a witness; do not repair a shared module yourself.

## Rules

1. Build with `scripts/compile.sh` from the worktree root — it logs timing and
   peak memory. Never prefix a build with the `timeout` command; raise your Bash
   tool's own timeout parameter instead.
2. Drive errors **and** warnings to zero. No `set_option` to silence a linter.
3. Edit/Write only — never `sed -i`, heredocs, or shell redirection into a file.
4. Never weaken, generalize away, or delete a statement to make it provable. If a
   statement is false as written, prove it false and report — that is a result.
5. Commit with `scripts/gitcp.sh` on branch `agent1`. **Do not push and do not set
   an upstream**; its push step failing with "no tracking information" is
   expected. The orchestrator reviews, merges and pushes.

## Report

Write `reports/r0030-report-from-agent1-to-orchestrator-powerdomain-bounded-complete.md`
containing: which statements are proved and kernel-accepted; `#print axioms` for
each, showing no `sorryAx`; the exact remaining `sorry` count in your file; the
verbatim final `lake build` line; your commit SHAs; and for anything unproved,
the specific mathematical or Lean obstacle with the failing goal state.
