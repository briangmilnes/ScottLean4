---
round: r0032
from: orchestrator
to: agent3
subject: theorem-12
date: 2026-0806-20:30
status: pending
related:
  - reports/r0031-report-from-agent4-to-orchestrator-lemmas-28-30.md
---

# r0032 agent3 — Theorem 12: initiality of a continuous algebra satisfying `T`

## Goal

> **Theorem 12** (Gunter & Scott, §5.3) Initiality of a continuous algebra
> satisfying the axioms `T`.

## Why this is now reachable

`docs/PaperInventory.md` recorded Theorem 12 as **not statable** — "axioms `T` is
never defined in the legible text". r0031 refuted that: `pdftotext -layout`
extracts the axioms cleanly. As reported:

> a continuous algebra `⊕ : E × E → E` with associativity, commutativity and
> idempotence; `T♯` adds `s ⊕ t ⊑ s`, and `T♭` adds `s ⊑ s ⊕ t`.

**Verify that reading yourself against the PDF before formalizing it.** It is
second-hand here, and r0031 found three separate errors in one plan's paraphrase
of a section. Quote the paper's own text in a docstring, and say which of `T`,
`T♯`, `T♭` each of your definitions corresponds to.

## Worktree and ownership

Work only in `/home/milnes/projects/ScottLean4-agent3`, branch `agent3`. **Verify
it is at `main` before you start**; two r0031 agents found their worktree behind
while their plan claimed otherwise. Never touch `/home/milnes/projects/ScottLean4`
or a sibling.

You own one new file: `ScottDomains/ScottDomains/ContinuousAlgebra.lean`.
Everything else is read-only; if a shared module must change, stop and report.

**Every declaration goes in `namespace ScottDomains.ContinuousAlgebra`.**

## What to read first

| # | File | Why |
| -- | ---- | --- |
| 1 | `papers/Gunter Scott 1990.pdf`, §5.3 | the definition of `T`, `T♯`, `T♭`, the theorem, and its proof sketch — read it first and quote it |
| 2 | `ScottDomains/Powerdomain/Hoare.lean`, `Smyth.lean`, `Plotkin.lean` | the three powerdomains (r0029) — Theorem 12's initial algebras are these, which is why it sits in §5.3 beside Lemma 13 |
| 3 | `ScottDomains/Powerdomain/BoundedComplete.lean` | r0031's Lemma 13, and the `idealSup` defect note — **do not** claim a `BoundedComplete` instance for an ideal completion this round; agent2 is repairing that |
| 4 | `ScottDomains/ScottHom.lean`, `Product.lean` | continuous maps and `E × E`, which the algebra's operation lives on |
| 5 | `ScottDomains/IdealCompletion.lean` | Theorem 11, how each powerdomain is a domain |

## What to deliver

1. **The algebra.** A continuous binary operation on a domain with the `T` axioms
   as a predicate — associativity, commutativity, idempotence — and the two
   strengthenings `T♯` and `T♭` as separate predicates, not one flag.
2. **Initiality.** State what "initial" means here explicitly: for every algebra
   of the class and every continuous map from the generators, a **unique**
   continuous homomorphism factoring it. Both existence and uniqueness.
3. **The instance.** Whichever powerdomain the paper names as the initial algebra
   for each axiom set — `D♭` for `T♭`, `D♯` for `T♯` if that is what §5.3 says.
   Check rather than assume; the ♯/♭ correspondence is where a paraphrase would
   most easily invert.

If initiality needs a bounded-completeness fact about the powerdomain, say so and
stop there — that fact is blocked until agent2's `idealSup` repair lands this
round. Do not work around it by assuming an instance that is currently false.

## Rules

1. Build with `scripts/compile.sh` from the worktree root. Never prefix a build
   with the `timeout` command; raise your Bash tool's own timeout instead.
2. Errors **and** warnings to zero. No `set_option` to silence a linter.
3. Edit/Write only — never `sed -i`, heredocs, or shell redirection into a file.
4. Never weaken a statement to make it provable. A uniqueness clause dropped is a
   weakened theorem.
5. Commit with `scripts/gitcp.sh` on branch `agent3`. **Do not push, do not set an
   upstream.**

## Report

Write `reports/r0032-report-from-agent3-to-orchestrator-theorem-12.md`: the `T`
axioms as you read them from the PDF, quoted, and whether they match r0031's
report; your definition of initiality; what is proved and kernel-accepted with
`#print axioms` showing no `sorryAx`; which powerdomain is initial for which axiom
set; the exact `sorry` count; the verbatim final `lake build` line; commit SHAs;
and the specific obstacle for anything unproved.
