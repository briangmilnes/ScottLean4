---
round: r0048
from: orchestrator
to: orchestrator
subject: find-two-and-fifteen
date: 2026-0809-13:55
status: pending
related:
  - docs/Status.md
  - analyses/numbered-status.20260809-132707.orchestrator.tsv
---

# r0048 — the two numbered results nothing in the tree mentions

`scripts/numbered-status.sh` measured the declarations carrying each of Gunter &
Scott's numbered results, and a follow-up grep for `**Theorem N**` / `**Lemma N**`
quotations found **28 of the 30 numbered results quoted in the tree**. Two are
absent from every `.lean` file and every document:

| # | Missing | Neighbours that ARE present |
| -- | ------ | --------------------------- |
| 1 | **result 2** | Theorem 1 (`theorem1`), Theorem 3 (`theorem3`) |
| 2 | **result 15** | Theorem 14 (`thm14`), Theorem 16 (`thm16`) |

**This is a gap in our record. It is not yet a claim about the paper.** Nobody has
checked the printed text for either number. `docs/Status.md` says so, and this
round is what makes that sentence unnecessary.

## Three possible outcomes, all acceptable

Each stream must decide which of these holds, from the **printed page**, before
writing any Lean:

| # | Outcome | What follows |
| -- | ------ | ------------ |
| 1 | the result exists in the paper and is **not** in the tree | transcribe it and prove it — the round's target |
| 2 | the result exists and **is already stated** under a name carrying no number | no new statement; record the mapping so the next `numbered-status.sh` run finds it |
| 3 | the paper's numbering **skips** it | the count is 28, not 30, and `Status.md`, `PaperInventory.md` and `PropertiesVsTheorems.md` all need correcting |

**Outcome 2 is live and should be checked first.** r0043's agent1 reported that
"all 15 conjuncts of Theorems 1–3, Lemmas 4–5 and Theorem 7 are stated and
proved", which asserts result 2 is stated. Lemmas 4, 5 and 8 are each quoted in a
module docstring but carry **no numbered declaration name** — `NormalSubposet.lean`,
`FinitaryProjection.lean`, `Product.lean` — so a result being stated without its
number in any identifier is the normal case here, not an anomaly.

**Outcome 3 is equally live and must not be ruled out by wishful reading.** The
figure "30 numbered results" comes from `PropertiesVsTheorems.md` and has never
been verified against the printed text. If the numbering skips, say so.

**Do not invent a theorem to fill a slot.** If the printed text does not carry
one, the honest deliverable is outcome 3 with the page evidence.

## Reading this PDF

`ScottDomains/papers/Gunter Scott 1990.pdf`. **`pdftotext` is unreliable on it** —
Type 3 bitmap fonts with no usable `ToUnicode` map: `→` and `⇸` both extract as
`!`, `×`/`⊗`/`⊕` extract as nothing, and `♯`/`♭`/`♮` extract as `]`/`[`/`\`.
Every statement recovered in earlier rounds was read from a **rendered image at
600 dpi**, and two printed defects were confirmed only that way.

The tooling exists — read each script's header before use:

    scripts/pdf-find-page.sh <pdf> <pattern>   # physical page index for a string
    scripts/pdf-render.sh                      # page → image at a given dpi
    scripts/pdf-crop.sh                        # crop a rendered page
    scripts/pdf-section.sh                     # extract a page range

The printed folio is **offset from the physical page index**; `pdf-find-page.sh`
exists because of that. Quote the **printed folio** in your report, and give the
physical index alongside it so the next reader can re-render.

## Streams

### agent1 — result 2

Theorem 1 is §2's fixed-point theorem, whose printed conclusion is a conjunction
(least fixed point **and** below every fixed point) — `PaperInventory.md` records
that the inventory once counted it as one conjunct when it is two. Theorem 3 is
the existence half with `theorem3_existsUnique`. Result 2 sits between them.

Check outcome 2 first: `Skeleton/`, `Kleene/`, `FixedPoint`-related modules, and
anything r0043's agent1 touched. `scripts/a1-r0040-decls-still-present.sh` and
the r0043 report list the §2/§3 declarations by name.

### agent2 — result 15

Theorem 14 is the characterization `thm14` (`thm14_forward`, `thm14_converse`);
Theorem 16 is `thm16`/`thm16_positive`. Result 15 sits between them, which places
it at the §5/§6 boundary — the powerdomain material into the bifinite material.

Check outcome 2 first across `Powerdomain*`, `JungSFP`, `JungFinite`,
`Section62.lean`, `Skeleton/Recovered.lean`. Note `docs/StatementRecovery.md`
records **Lemma 9 and Theorem 14 recovered from the PDF after being marked "not
statable"**, so this neighbourhood has a history of results that were present but
unfindable.

## If you reach outcome 1

Transcribe and prove, under the standing rules:

* Quote the printed sentence **verbatim** in the module docstring, with the
  printed folio and the physical page index.
* State it as the paper states it. **An added instance binder is not a
  transcription** — it is a weakening, and r0044 measured that as this
  development's dominant defect mode, 9 of 12 under-specified rows.
* Prove it, or say precisely what blocks it. **No `sorry`** — the package is at 0
  and stays at 0. A `Prop`-valued `def` nobody attempts is *worse* than an honest
  "open" here, because `sorry` cannot see it.
* If the printed statement appears false, **check it three times before saying
  so**. Nine printed defects are on record; three further suspicions were checked
  and every one turned out to be **our** transcription error — Theorem 26's
  arity-0 argument refutes the paper's *proof* rather than its theorem, Theorem
  29's second sentence lost the word "domain", and our step-function guard tests
  compactness where the paper tests boundedness.

## Hard rules

* Namespace per agent (`ScottDomains.R48.AgentN`), new files prefixed `A<N>`.
* No `sorry`. Build with `scripts/compile.sh -r r0048`; zero errors, zero
  warnings. `#print axioms` every theorem added.
* Do not edit an existing `def` or theorem statement. If you find one that is
  wrong, report it.
* One command per Bash call; never chain; never `cd`. `Edit`/`Write` only — no
  heredocs, no `sed -i`. Commit with your worktree's `scripts/gitcp.sh`; do not
  push.

## Deliverable

`reports/r0048-report-from-agentN-to-orchestrator-result-<n>.md`: which outcome,
the printed folio and physical page, the verbatim sentence if it exists, the
declaration if you wrote one, and its axiom footprint.

## Orchestrator steps

1. Fast-forward worktrees; launch two agents.
2. Merge; composition check.
3. Correct `Status.md`, `PaperInventory.md` and `PropertiesVsTheorems.md` to
   whichever outcome holds — including the "30 numbered results" figure, which is
   itself unverified.
4. Re-run `scripts/numbered-status.sh` and confirm the gap is closed or explained.
