---
round: r0032
from: orchestrator
to: agent1
subject: lemma-24-theorem-25
date: 2026-0806-20:30
status: pending
---

# r0032 agent1 — Lemma 24 and Theorem 25: universality of `P N`

## Goal

> **Lemma 24** `U` a cpo; `×` and `→` representable over `U` ⟹ the setup for
> universality.

> **Theorem 25** `U` a non-trivial domain representing `×` and `→` ⟹ `U` is
> **universal**.

One chain, one agent: Theorem 25 consumes Lemma 24, so splitting them across two
agents would leave one blocked on the other.

## Why this is unblocked now

Both of Lemma 24's hypotheses exist as of r0031:

| # | Hypothesis | Where |
| -- | ---------- | ----- |
| 1 | `→` representable over `P N` | `ScottDomains.lem23` (r0028, `UniversalDomain.lean`) |
| 2 | `×` representable over `P N` | `ScottDomains.PowerdomainRep.isRepresentable_prod` (r0031, `Powerdomain/Universal.lean`) |

`isRepresentable_prod` was written as the critical-path item precisely to unblock
this plan. `Powerdomain/Universal.lean` also carries a **generic** scheme —
`repOf`, `isClosure_repOf`, `repRangeOrderIso`, `scottContinuous_repOf` for an
arbitrary closure family — so further conjuncts cost only their own family.

## Worktree and ownership

Work only in `/home/milnes/projects/ScottLean4-agent1`, branch `agent1`. **Verify
it is at `main` before you start** — run `git log --oneline -1` in both and
fast-forward if not. Two r0031 agents found their worktree behind while their plan
claimed otherwise. Never touch `/home/milnes/projects/ScottLean4` or a sibling.

You own one new file: `ScottDomains/ScottDomains/Universality.lean`. Everything
else is read-only; if a shared module must change, stop and report.

**Every declaration goes in `namespace ScottDomains.Universality`.** Namespace per
agent has held at zero collisions for two rounds; before it, five agents sharing
one namespace produced two clashes invisible to `lake build`.

## What to read first

| # | File | Why |
| -- | ---- | --- |
| 1 | `ScottDomains/UniversalDomain.lean` | `IsRepresentable`, `IsRepresentable₂`, `Cpo`, `ClosurePoset`, `IsClosurePair`, Theorem 22, Lemma 23 |
| 2 | `ScottDomains/Powerdomain/Universal.lean` | `isRepresentable_prod` and the generic `repOf` scheme |
| 3 | `ScottDomains/RecursiveDomain.lean` | `IsUniversal` and `IsUniversalRetract` — the paper's two phrasings of *universal domain*, already formalized (r0029). **Theorem 25's conclusion should be one of these two**; say which and why |
| 4 | `ScottDomains/Powerset.lean` | `P N` |
| 5 | `papers/Gunter Scott 1990.pdf`, §7.2 | the statements. Extract with `pdftotext -layout` and quote them — r0031 found three separate errors in a plan's paraphrase of §7 |

## What to deliver

1. **Lemma 24**, stated from the paper's own text. Its content is the *setup*: say
   precisely what it provides and do not fold it into Theorem 25.
2. **Theorem 25**, with its conclusion pinned to `IsUniversal` or
   `IsUniversalRetract` from `RecursiveDomain.lean` — do not introduce a third
   formalization of universality.
3. The instance at `U = P N`, discharging non-triviality from `Powerset.lean` and
   representability from Lemma 23 and `isRepresentable_prod`. That is the point of
   the chain: `P N` is universal for the class the paper names.

If the paper's "non-trivial" is a condition the development cannot yet express,
state it as an explicit hypothesis rather than assuming it silently, and say so.

## Rules

1. Build with `scripts/compile.sh` from the worktree root. Never prefix a build
   with the `timeout` command; raise your Bash tool's own timeout instead.
2. Errors **and** warnings to zero. No `set_option` to silence a linter.
3. Edit/Write only — never `sed -i`, heredocs, or shell redirection into a file.
4. Never weaken a statement to make it provable. If it is false as stated, prove
   that and report — three refutations have been first-class results here.
5. Commit with `scripts/gitcp.sh` on branch `agent1`. **Do not push, do not set an
   upstream.**

## Report

Write `reports/r0032-report-from-agent1-to-orchestrator-lemma-24-theorem-25.md`:
the statements proved, kernel-accepted, with `#print axioms` showing no `sorryAx`;
which universality predicate Theorem 25 concludes and why; whether `P N` is shown
universal; the exact `sorry` count; the verbatim final `lake build` line; commit
SHAs; and the specific obstacle for anything unproved.
