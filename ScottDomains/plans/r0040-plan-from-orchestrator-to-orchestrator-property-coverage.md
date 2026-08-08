---
round: r0040
from: orchestrator
to: orchestrator
subject: property-coverage
date: 2026-0808-11:33
status: pending
related:
  - docs/PaperInventory.md
  - docs/PropertiesVsTheorems.md
  - analyses/theorem-audit.2026-0808-10:04.orchestrator.md
---

# r0040 — Does every one of the paper's 100 properties have a Lean statement?

## The question, and why it has no answer yet

`PaperInventory.md` row 2e records **1** paper result with no Lean statement at
all — Theorem 7's second sentence — and marks it a **lower bound**. It is a lower
bound because nobody has looked. This round makes it a measurement.

**This is the opposite direction from r0038.** That round went development →
paper: it took each of the 1298 theorems and asked what it serves. A search in
that direction can find a theorem serving nothing; it can **never** find a
property served by nothing, because nothing points at the gap. This round goes
**paper → development**: take each property the paper asserts and ask whether a
Lean declaration states it.

`sorry` cannot answer this either. A `sorry` is a hole in a *stated* theorem; a
result nobody wrote down produces no warning, no count and no build signal. A
development can reach 0 `sorry` while leaving paper results unstated, and this
one is two results away from exactly that.

## The 100 properties

87 conjuncts across the 30 numbered results, plus 13 unnumbered prose claims.
The per-result conjunct counts are in `docs/PropertiesVsTheorems.md` §1.

**Do not trust that column.** Three of its counts have already moved once —
Lemma 28 went 7 → 9, Lemma 30 went 9 → 10, Lemma 17 went 5 → 10 when dropped
glyphs were recovered — and the prose-claim list moved 12 → 13 in r0038 when an
agent found that one listed claim is not one the paper makes and two the paper
does make were omitted. **Re-derive your own section's counts from the PDF.** A
changed count is a finding, not a nuisance.

## Classification

Every property gets exactly one label:

| # | Label | Meaning |
| -- | ----- | ------- |
| 1 | `S+P` | **stated and proved** — name the declaration |
| 2 | `S+H` | **stated, proof open** — a `sorry`, or a named `Prop` standing in for the open step. Name both |
| 3 | `S≠` | **stated, but not the paper's statement** — different hypotheses, weaker conclusion, or a repaired form. Name the declaration and say exactly how it differs |
| 4 | `P` | **prose only** — the development asserts it in a docstring but never puts it under the kernel |
| 5 | `N` | **not stated** — no Lean declaration says this, in any form |

`S+P` requires you to **name the declaration and confirm it exists**. A docstring
saying "**Lemma 17**" is a claim to check, not evidence. r0038 found two files
asserting things about themselves that were false, and r0039 found a figure whose
lines the source file does not contain — in this project, the artifact is checked,
not the description of it.

`N` is the row this round exists to count, so it carries the burden of proof:
before labelling `N`, grep the development for the concept under at least three
names, and say in the report which three.

## The five streams

| # | Agent | Sections | Properties | Notes |
| -- | ----- | -------- | ----: | ----- |
| 1 | agent1 | §2, §3 | ~14 + its prose claims | Thm 1–3, Lem 4–5, Thm 6–7. **Six of the 13 prose claims are the body of Theorem 7** — this stream owns the one confirmed `N`, Theorem 7's second sentence, and should check whether §3.2's effective-presentation material hides more |
| 2 | agent2 | §4.1–4.5 through Lemma 10 | ~17 | Lem 8 (4), Lem 9 (6), Lem 10 (7). Lemma 9's items 3 and 5 are **false as printed** and the development proves kernel-checked negations — decide and state whether a refutation of a misprinted claim counts as stating it |
| 3 | agent3 | §4.5 from Theorem 11, and §5 | ~12 | Thm 11 (2), Thm 12 (6), Lem 13 (2), Thm 14 (2), plus §5's powerdomain prose. Thm 12 is three theories × existence and uniqueness; check all six are stated, not three |
| 4 | agent4 | §6 | ~16 | Prop 15, Thm 16 (2), Lem 17 (10), Thm 18, Lem 19, Lem 20. Thm 16's second conjunct is **refuted**, and `thm16_positive` states a repaired form — that is `S≠` plus a refutation, not `S+P` |
| 5 | agent5 | §7 | ~28 | Thm 21–27, Lem 28 (9), Thm 29 (2), Lem 30 (10). The largest and the least complete; several conjuncts are stated only as components of a conjunction, which still counts as stated — say so explicitly |

## Deliverable

`reports/r0040-report-from-agentN-to-orchestrator-property-coverage-<section>.md`,
with **one row per property**: the paper's sentence (quoted or precisely
paraphrased), section and printed page, the label, the declaration name if any,
and the evidence. Then per-label totals, and the `N` and `P` rows called out
separately.

Also report: your re-derived conjunct count per numbered result, and whether it
differs from `PropertiesVsTheorems.md` §1.

**No `.lean` file is edited this round.** The build, the `sorry` count and the
numbered-result count must be identical at the end. This is a measurement, and a
measurement that changes its subject is not one.

## Method

1. Read your sections in the PDF. `scripts/pdf-section.sh`, `pdf-render.sh`,
   `pdf-crop.sh`, `pdf-find-page.sh` are on `main`. `pdftotext` mangles the
   operator glyphs — `♮`/`♯`/`♭` extract as `\`/`]`/`[`, `→` and `⇸` both as `!`
   — so read the rendered page as an image wherever an operator list matters.
2. Enumerate the properties your sections assert, before looking at any Lean.
3. Only then search the development. `scripts/lean-decls.py --list <files>` gives
   declaration names with line numbers, comment-aware.
4. Label, with evidence.

## Process rules

One command per Bash call; never chain; never `cd`. `Edit`/`Write` only — no
heredocs, no `sed -i`. New scripts in `scripts/` prefixed with your stream name
after checking what exists. Commit at every stopping point with your worktree's
`scripts/gitcp.sh`; do not push. **The plan is not evidence** — r0034 had four
wrong stream descriptions, r0036 three, r0037 three, r0039 two. Contradicting
this plan from the paper is the expected behaviour.

## Orchestrator steps

1. Commit this plan; fast-forward the worktrees.
2. Launch five agents.
3. Spot-check: pick two `S+P` rows and confirm the named declaration says what
   the row claims; pick every `N` row and confirm independently, since `N` is the
   round's product.
4. Consolidate into `analyses/property-coverage.YYYY-MMDD-HH:MM.orchestrator.md`.
5. **Replace `PaperInventory.md` row 2e's "≥ 1" with the measured number**, and
   restate the property total if any conjunct count moved.
