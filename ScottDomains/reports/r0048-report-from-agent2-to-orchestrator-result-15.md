---
round: r0048
from: agent2
to: orchestrator
subject: result-15
date: 2026-0809-13:53
started: 2026-0809-13:46
finished: 2026-0809-13:53
related:
  - plans/r0048-plan-from-orchestrator-to-orchestrator-find-two-and-fifteen.md
  - ScottDomains/Skeleton/Section6.lean
---

# r0048 — Gunter & Scott's numbered result 15

## Outcome: 2, in its strongest form

The result exists in the paper, and it is **already stated and already proved** in
this package — under a declaration name that **does carry its number**. No new
statement was written, and none should be.

| # | Field | Value |
| -- | ---- | ----- |
| 1 | Kind | **Proposition**, not Theorem and not Lemma |
| 2 | Printed folio | **31** |
| 3 | Physical PDF page | **32** of `ScottDomains/papers/Gunter Scott 1990.pdf` |
| 4 | Section | §6.2, "Closure properties." — its first result |
| 5 | Declaration | `ScottDomains.prop15`, `ScottDomains/Skeleton/Section6.lean:134` |
| 6 | Proof state | proved, no `sorry` |
| 7 | Axioms | `[propext, Classical.choice, Quot.sound]` |

## The verbatim printed sentence

Read from a 600 dpi render of physical page 32, then re-read from a 600 dpi crop
of the statement line alone (`pdf-crop.sh … 32 600 550 4230 2700 220`), because
`pdftotext` finds neither "PROPOSITION 15" nor "bifinite" anywhere in this file:

> **Proposition 15** *A bounded complete domain is bifinite.*

Set in bold `Proposition 15` followed by the statement in italic, which is this
paper's house style for a numbered result. It is one sentence and one claim.

## Why the round thought result 15 was missing — a tool defect, not a record gap

`Skeleton/Section6.lean` has quoted this result since it was written, in the
module docstring at line 15 and again on the declaration. Two independent
measurements missed it for the same reason: **both search for `thm|theorem|lem|lemma`
and neither searches for `prop|proposition`.**

| # | Measurement | Pattern | Why it missed result 15 |
| -- | ---------- | ------- | ----------------------- |
| 1 | `scripts/numbered-status.sh` | `(thm\|theorem\|lem\|lemma)_?${n}([^0-9]\|$)` over declaration names | `prop15` has the prefix `prop`, absent from the alternation |
| 2 | the follow-up docstring grep | `**Theorem N**` / `**Lemma N**` | the docstring quotes `**Proposition 15**` |

So the reported figure "28 of 30 numbered results quoted in the tree" undercounts.
Result 15 is quoted, stated and proved; the count for §6 is complete.

### The exact fix, with its false-positive count measured

In `scripts/numbered-status.sh`, extend the alternation in both the `hits` and the
`c` greps:

    (thm|theorem|lem|lemma)_?${n}([^0-9]|$)
    (thm|theorem|lem|lemma|prop|proposition|cor|corollary)_?${n}([^0-9]|$)

I enumerated every `prop`/`cor`-numbered identifier in `ScottDomains/ScottDomains`
before recommending this. The complete set is `prop15`, `prop122`, `cor136`,
`Prop134` and `thm137`. Over `n` in 1…30 the widened pattern adds **exactly one
hit — `prop15` at `n=15` — and zero false positives**: `prop122` fails at `n=1`
and `n=12` because the next character is a digit, `cor136` fails at `n=1` and
`n=13` for the same reason, and `StructuresVsTypeClassesVsPropsInLean4` fails
because `Props` is not followed by a digit. `prop122` and `cor136` are Jung's
numbering, not Gunter & Scott's, and correctly stay out of the table.

`numbered-status.sh` hardcodes `root=/home/milnes/projects/ScottLean4`, the main
checkout, so I did not edit it from this worktree — it is the orchestrator's to
change, and plan step 4 re-runs it.

## The statement is faithful — no added instance binder

The printed hypotheses are exactly two, "bounded complete" and "domain"; the
conclusion is "bifinite". The Lean statement is

    theorem prop15 [Domain α] [BoundedComplete α] : IsBifinite α

with `[CompletePartialOrder α]` in scope as the ambient order structure. Checked
against the definitions rather than assumed:

| # | Paper | Lean | Match |
| -- | ---- | ---- | ----- |
| 1 | domain = algebraic cpo with countable basis | `Domain` extends `IsAlgebraic`, adds `countable_compacts` (`Domain.lean:128`) | yes |
| 2 | bounded complete = every bounded subset has a lub (least element carried by the cpo) | `BoundedComplete.isLUB_sSup_of_bddAbove` (`Domain.lean:168`) | yes |
| 3 | bifinite | `IsBifinite α := IsPlotkinOrder (compacts α)` (`Bifinite.lean:62`) | yes |

Nothing is added and nothing is dropped — this is not one of r0044's
under-specified rows.

## The one defect found: the docstring quote was a paraphrase

The module docstring read `> **Proposition 15** Every bounded-complete domain is
bifinite.` and the declaration docstring read `**Proposition 15.** Every bounded
complete domain is bifinite.` Both are universally equivalent to the printed
sentence, but neither is the printed sentence: the paper writes "**A** bounded
complete domain", with no hyphen in "bounded complete".

I corrected both docstrings to the verbatim sentence and recorded the folio and
physical page alongside, per the round's transcription rule. **No `def` and no
theorem statement was edited** — the change is documentation only, and `prop15`'s
type, proof and axiom footprint are byte-identical to before.

## Build

`scripts/compile.sh -r r0048`: **1364 jobs, 0 errors, 0 warnings, 0 `sorry`**,
wall 0:05.36, peak 1796 MiB single / 2402 MiB tree pss. Log
`ScottDomains/logs/compile-20260809-135202.agent2.log`.

`scripts/axioms.sh -i ScottDomains.Skeleton.Section6` over the declaration and
its two helpers:

    ScottDomains.prop15                            [propext, Classical.choice, Quot.sound]
    ScottDomains.isCompactElement_of_isLUB_finite  [propext, Classical.choice, Quot.sound]
    ScottDomains.exists_upperBound_mem_of_finite   [propext, Classical.choice, Quot.sound]

No `sorryAx`.

## What the orchestrator should change

| # | Document | Change |
| -- | ------- | ------ |
| 1 | `docs/Status.md` | result 15 is not missing — it is `prop15`, proved, axioms clean. Drop the sentence saying nobody has checked the printed text for 15 |
| 2 | `docs/PaperInventory.md`, `docs/PropertiesVsTheorems.md` | result 15 is a **Proposition**; the §6 numbered results are complete |
| 3 | `scripts/numbered-status.sh` | widen the alternation as above; measured at +1 true hit, 0 false positives |
| 4 | the "28 of 30 quoted" figure | it is at least 29 of 30 on account of result 15 alone; agent1 reports on result 2 |

Note that the "30 numbered results" total itself remains unverified against the
printed text — this round checked result 15, not the count. Whether the paper's
numbering runs to 30 without a skip is still open, and outcome 3 was **not**
reached here: for result 15 the numbering does not skip.
