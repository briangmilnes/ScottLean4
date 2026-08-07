---
round: r0030
from: orchestrator
to: agent2
subject: powerdomain-universal
date: 2026-0806-19:55
status: pending
related:
  - plans/r0030-plan-from-orchestrator-to-orchestrator-remaining-theorems.md
---

# r0030 agent2 — Lemma 30 and Lemma 28's powerdomain conjuncts

## Goal

Two §5/§7 results about the powerdomains that round r0029 constructed:

> **Lemma 30** The universal / closure property of the powerdomains (§5.3).

> **Lemma 28** The operators `→, ×, ⊗, +, ()⊥, ()], ()[` are representable over
> the universal domain `U`.

Lemma 28's function-space conjunct is **already proved** — it is Lemma 23
(`ScottDomains.lem23`, r0028). Your part is the powerdomain conjuncts `()]` and
`()[`, plus whichever of `×, ⊗, +, ()⊥` fall out of the same argument. Do not
restate Lemma 23.

## Worktree and ownership

Work only in `/home/milnes/projects/ScottLean4-agent2`, branch `agent2`. Never
touch `/home/milnes/projects/ScottLean4` or a sibling worktree.

You own exactly one new file: `ScottDomains/ScottDomains/Powerdomain/Universal.lean`.
Everything else is read-only. If a shared module genuinely must change, stop and
report rather than change it.

**Every declaration you write goes in `namespace ScottDomains.PowerdomainRep`.**
In r0028 two agents each defined `isClosure_sSup` and
`IsClosure.apply_sSup_of_directed`; `lake build` passed at 971 jobs because no
module imported both, and the clash surfaced only when an axiom audit finally
imported the pair. A namespace per agent makes that impossible.

## What to read first

| # | File | Why |
| -- | ---- | --- |
| 1 | `ScottDomains/UniversalDomain.lean` | `IsRepresentable`, `IsRepresentable₂`, `Cpo`, `ClosurePoset`, Theorem 22 and Lemma 23 — the vocabulary Lemma 28 is stated in, and the model to imitate |
| 2 | `ScottDomains/Powerdomain/Hoare.lean`, `Smyth.lean`, `Plotkin.lean` | the r0029 constructions |
| 3 | `ScottDomains/IdealCompletion.lean` | Theorem 11, which is how each powerdomain is a domain |
| 4 | `papers/Gunter Scott 1990.pdf`, §5.3 and §7 | the statements; §5.3 is where Lemma 30's universal property is stated |

You wrote `IdealCompletion.lean` in r0028 and the Smyth powerdomain in r0029, so
the ideal-completion machinery is yours already.

## Statements to prove

1. **Lemma 30.** State the universal property the paper gives in §5.3 — the sense
   in which the powerdomain is free, i.e. that a continuous map from `D` into a
   suitable structure extends uniquely to the powerdomain. Quote the paper's own
   phrasing in a docstring and say exactly which reading you formalized. Do not
   invent a categorical statement the paper does not make.
2. **Lemma 28, powerdomain conjuncts.** `IsRepresentable (Set ℕ) F` for `F` the
   Hoare and Smyth powerdomain operators, in the same shape as `lem23`.

If the paper's §5.3 statement cannot be recovered from the PDF with confidence —
the 1990 Type-3 fonts garble several §5 displays — state precisely what is
illegible and leave Lemma 30 unstated rather than guessing. A recorded blocker is
a result; a guessed statement is a defect.

## The obstacle to expect

`IsRepresentable` quantifies over `Fc(U)`, the finitary closures on `U`. r0028's
agent5 recorded that identifying `ClosurePoset U` with the paper's `Fc(U)` appeals
to Lemma 19 at a strength the development did not then have — it had only that
`im(r)` carries a `CompletePartialOrder`. That gap is now closed:
`IsClosure.domain_range` (r0028, `FinitaryProjectionPoset.lean`) proves `im(r)` is
a **domain**, with the basis `{r(k) | k ∈ K(D)}`. Use it, and say in your report
whether it fully discharges the appeal.

## Rules

1. Build with `scripts/compile.sh` from the worktree root — it logs timing and
   peak memory. Never prefix a build with the `timeout` command; raise your Bash
   tool's own timeout parameter instead.
2. Drive errors **and** warnings to zero. No `set_option` to silence a linter.
3. Edit/Write only — never `sed -i`, heredocs, or shell redirection into a file.
4. Never weaken, generalize away, or delete a statement to make it provable. If a
   statement is false as written, prove it false and report — that is a result.
5. Commit with `scripts/gitcp.sh` on branch `agent2`. **Do not push and do not set
   an upstream**; its push step failing with "no tracking information" is
   expected. The orchestrator reviews, merges and pushes.

## Report

Write `reports/r0030-report-from-agent2-to-orchestrator-powerdomain-universal.md`
containing: which statements are proved and kernel-accepted; `#print axioms` for
each, showing no `sorryAx`; which phrasing of §5.3 you formalized and the evidence
for that reading; whether `IsClosure.domain_range` discharges the `Fc(U)` appeal;
the exact remaining `sorry` count; the verbatim final `lake build` line; your
commit SHAs; and the specific obstacle for anything unproved.
