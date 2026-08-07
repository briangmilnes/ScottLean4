---
round: r0030
from: orchestrator
to: agent5
subject: statement-recovery
date: 2026-0806-19:55
status: pending
related:
  - plans/r0030-plan-from-orchestrator-to-orchestrator-remaining-theorems.md
---

# r0030 agent5 — Recover Lemma 9, Theorem 12 and Theorem 14 from the PDF

## Goal

Three of the paper's numbered results have never been stated in Lean, and not
because they are hard to prove: **their statements cannot be read off the PDF.**
The 1990 Type-3 fonts drop characters and mangle math. Your task is textual and
evidential, not a proof task.

| # | Result | What is wrong with the printed text |
| -- | ------ | ----------------------------------- |
| 1 | **Lemma 9** | "Product / function-space iso laws over `D, E, F`" — the PDF drops every `⊗` and every `⊥`, so which operators the laws range over is unreadable |
| 2 | **Theorem 12** | "Initiality of a continuous algebra satisfying axioms `T`" — `T` is never defined in the legible text |
| 3 | **Theorem 14** | "Equivalent characterizations of an (algebraic / bounded complete) domain" — the list of characterizations is garbled |

This is the round's one non-Lean stream, and it unblocks a later round: nothing
can prove these until someone establishes what they say.

## Worktree and ownership

Work only in `/home/milnes/projects/ScottLean4-agent5`, branch `agent5`. Never
touch `/home/milnes/projects/ScottLean4` or a sibling worktree.

You own two new files:

- `ScottDomains/docs/StatementRecovery.md` — the evidence and the argument;
- `ScottDomains/ScottDomains/Skeleton/Recovered.lean` — the recovered statements
  as Lean theorems with `sorry` bodies, in `namespace ScottDomains.Recovered`.

Everything else is read-only. If a shared module genuinely must change, stop and
report rather than change it.

## Method

1. Extract the relevant pages with `pdftotext -layout "papers/Gunter Scott 1990.pdf"`
   and read them directly. Do not work from the inventory's paraphrase — it is a
   summary written from the same broken text, and r0029 already found one place
   where a paraphrase had lost a load-bearing distinction (`Pf` is the finite
   **non-empty** subsets, not all finite subsets).
2. For each result, reconstruct the statement from three kinds of evidence, and
   say which you used: surrounding prose that references the result; the paper's
   own later uses of it; and the standard form of the result in the domain-theory
   literature, cited by name.
3. Where a character is genuinely missing, infer it from the algebra — e.g. an
   isomorphism law that only typechecks if the operator is `⊗` rather than `×`
   tells you which symbol was dropped. Show the reasoning.
4. Assign each recovered statement a confidence: **certain** (the text is legible
   once the font damage is undone), **inferred** (reconstructed from use or
   algebra, with the argument given), or **unrecoverable** (say what is missing).

## Deliverables

`StatementRecovery.md`: per result, the raw extracted text verbatim, the
reconstruction, the evidence, and the confidence. Quote the PDF rather than
summarizing it.

`Skeleton/Recovered.lean`: a Lean statement with a `sorry` body for every result
you rate certain or inferred, each with a docstring giving the paper's wording and
your confidence. **Nothing rated unrecoverable gets a statement** — leave it out
and say so. Match the file conventions of `Skeleton/Lemma10.lean` and
`Skeleton/Section6.lean`: fixed statements, `sorry` bodies, one file, no proofs.

**A guessed statement is worse than an absent one.** The development already
records seven results as "not yet statable" with their blockers, and that count
going down honestly is the metric — not the count of statements going up. If all
three are unrecoverable, that is a complete and successful execution of this plan.

## Rules

1. Build with `scripts/compile.sh` from the worktree root — it logs timing and
   peak memory. Never prefix a build with the `timeout` command; raise your Bash
   tool's own timeout parameter instead.
2. Errors and warnings to zero, except the `declaration uses 'sorry'` warnings for
   the statements you deliberately leave open. No `set_option` to silence a
   linter.
3. Edit/Write only — never `sed -i`, heredocs, or shell redirection into a file.
4. Every declaration in `namespace ScottDomains.Recovered`. Four sibling agents
   run this round; in r0028 two agents minted the same name and the clash was
   invisible to `lake build` because no module imported both.
5. Commit with `scripts/gitcp.sh` on branch `agent5`. **Do not push and do not set
   an upstream**; its push step failing with "no tracking information" is
   expected. The orchestrator reviews, merges and pushes.

## Report

Write `reports/r0030-report-from-agent5-to-orchestrator-statement-recovery.md`
containing: per result, the confidence and the one-line justification; which
statements are now in `Recovered.lean` and which are not, with reasons; the exact
`sorry` count you added; the verbatim final `lake build` line; and your commit
SHAs.
