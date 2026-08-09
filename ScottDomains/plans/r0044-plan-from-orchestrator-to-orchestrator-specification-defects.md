---
round: r0044
from: orchestrator
to: orchestrator
subject: specification-defects
date: 2026-0808-17:20
status: pending
related:
  - analyses/property-coverage-remeasure.2026-0808-16:55.orchestrator.md
  - analyses/property-coverage.2026-0808-11:59.orchestrator.md
  - docs/PaperInventory.md
---

# r0044 — the three unmeasured defect classes

r0043 produced one number worth trusting: **36 of the paper's 239 properties are
not specified** (26 `N`, 10 `P`), re-derived from scratch rather than by
subtraction. Three other figures were quoted alongside it and **none is a
measurement**:

| # | Class | Quoted | What it actually is |
| -- | ---- | -----: | ------------------- |
| 1 | under- **or** incorrectly specified (`S≠`) | 18 | a merged label; the split was never recorded |
| 2 | vacuously specified — labelled `S+P`, hypotheses unused | ≥2 | two instances noticed in passing |
| 3 | undischarged `def` — stated, unproved, not a `sorry` | ≥1 | one instance noticed in passing |
| 4 | artifacts asserting things that are false | 7 sites | every one found incidentally, looking for something else |

Classes 2, 3 and 4 have **no instrument at all**. Nobody has ever swept for them.
Their counts are discovery counts, and a discovery count reported as a
measurement is precisely the defect this project has now been burned by three
times — the "13 prose claims" that counted our own output, the 1308 theorem count
wrong in both directions, and the "≈22" that was 62 − 40.

**This round builds the instruments and runs them.**

## Why eight agents, and why it is safe

`docs/Performance.md` settles the parallel limits; they are not re-measured here.
The binding constraint at 8 is **declaration collisions** (~6 agents, ~5 clashes
projected at 8) — but that constraint is derived from agents *adding
declarations*. This round is read-only. No agent edits a `.lean` file. r0043 ran
five agents under the same rule with zero conflicts. The CPU-burst ceiling is ~8
(Performance.md row 2), so this round sits at the ceiling and not past it.

Script-name collisions are the one real risk: **prefix every script you create
with your stream name** (`a3-`, `a7-`, …), as r0043 did.

## Streams

### Class 1 — split the 18 `S≠` rows (agents 1, 2)

Each `S≠` row was labelled "stated, but not the paper's statement." That merges
three distinct situations, and only the third is a defect:

| # | Kind | Definition |
| -- | ---- | ---------- |
| 1 | **under-specified** | the Lean statement is a strict weakening — some conjunct of the paper's claim is missing, or it is stated at a special case |
| 2 | **incorrectly specified** | the Lean statement is not a weakening; it says something the paper does not say |
| 3 | **deliberately divergent** | the paper's printed statement is false and ours is the repair — this is correct work, not a defect |

Row 18's `⊢♮` characterization is kind 3 and must not be counted as a defect.
Expect more of these: the paper has **nine** known printed defects.

For each row: quote the paper's sentence, quote the Lean statement as
**elaborated** (`#check @d`, not read off the source), and classify. Where the
kind is 1, say which conjunct is missing. Where it is 2, say what ours asserts
that the paper does not. Where it is 3, name the printed defect.

* **agent1** — the 9 `S≠` rows in §2, §3, §4.
* **agent2** — the 9 `S≠` rows in §5, §6, §7.

The 18 are listed per-agent in `analyses/property-coverage.2026-0808-11:59.orchestrator.md`
and its r0043 successor. If your area's count differs from 9, report the real
number; do not pad or borrow.

### Class 2 — the vacuity sweep (agents 3, 4, 5)

**The round's most valuable stream, and the hardest.** A theorem whose hypotheses
go unused is labelled `S+P` and establishes nothing. Two instances are known,
both from `Effective.nonempty_effectivePresentation`: `Classical.dec` fills
`EffectivePresentation`'s decidability fields at no cost, so *every* domain has
one, and any theorem taking that structure as a hypothesis is vacuous.

Build a real instrument. Candidate methods, in the order I would try them:

1. **Lean's own linters.** `#lint` carries `unusedArguments` among others. If it
   runs over this package it is the cheapest complete answer available. Try this
   first and report whether it works, including if it does not — a negative
   result here is worth reporting precisely.
2. **Hypothesis deletion.** For a theorem `∀ (h : P), Q`, if `Q` elaborates
   without `h`, the hypothesis is dead. Mechanizable per-declaration.
3. **Trivially-inhabited structures.** For each `structure`/`class` in the
   package, ask whether an instance is derivable for *every* type. Any theorem
   quantifying over such a structure is suspect. `EffectivePresentation` is the
   known case; find the others.
4. **Proofs closed by `trivial`, `rfl`, `simp` alone** where the statement looks
   substantive — a weak proxy, useful for ranking, not for concluding.

Split by module, roughly a third of the package each — **agent3** takes the
`Effective/`, `Kleene/` and `Isomorphism/` trees plus `Skeleton/`; **agent4** takes
the powerdomain and flat-cpo modules (`Flat*`, `Powerdomain*`, `ContinuousAlgebra`,
`Plotkin`); **agent5** takes the rest, including `IdealCompletion`, `Universality`,
`RecursiveDomain`, `Morphism`, `JungCor136`, `PropertyM`, `Iwamura`, `Thm18`.

Report **a count and a list**, not a characterization. If the instrument finds
zero in your area, that is a result — say so, and say what the instrument would
have caught.

### Class 3 — undischarged `def`s (agent 6)

`StepFunctionsDecidable` is stated, unproved, and not a `sorry`, so the `sorry`
count of 0 does not see it. Sweep the whole package for the shape: a `def`
returning a `Prop`, or an `axiom`, or a structure field never instantiated, that
stands in for a claim nobody proved.

Also enumerate **`Prop`-valued `def`s that are never used** as a hypothesis or
conclusion anywhere — a stated claim with no consumer is a different flavour of
the same problem.

This is the smallest stream. If it finishes early, extend it to a census of
**every `axiom` declaration** in the package (expected: zero) and every
`@[simp]`-tagged lemma that never fires — the latter was offered in an earlier
round and never run.

### Class 4 — artifacts asserting false things (agents 7, 8)

Seven sites are known, all found incidentally. Build the sweep.

The mechanizable half already exists: `scripts/r0043-verify-citations.sh` checks
backticked declaration names in the r0043 reports against the real declaration
list. **Generalize it** to every docstring in every `.lean` file and every file
under `docs/`, `analyses/`, `plans/` and `reports/`. A docstring naming a
declaration that does not exist is a mechanical catch, and
`FlatPowerdomain.lean:34` proves the class is populated.

* **agent7** — the mechanical sweep: names cited anywhere that do not resolve.
  Report every hit with its file, line, and the name it probably meant. Take care
  with the known false-positive sources r0043 documented — structure and class
  *fields* are not top-level declarations, and a name cited as a zero-hit grep is
  cited as evidence of absence, where unresolved is correct.
* **agent8** — the reading half: docstrings and doc prose whose *claim* is false
  even though every name in it resolves. `smyth_natBot_orderIso`'s docstring
  claims a directed-supremum clause its statement lacks; `PaperInventory.md` row
  554 and `PRepFun.lean:98` assert no powerdomain map action exists.
  **Also fix `PaperInventory.md` row 3's arithmetic**: it says 146 prose claims,
  91 proved, 60 unstated, and 146 − 91 = 55. Determine which of the three numbers
  is wrong from the r0040 per-section data and report it; do not guess.

## Standing rules

**No `.lean` file is edited by any agent.** At the end the build must be
identical: 1339 jobs, 0 errors, 0 warnings, `sorry` 0, 100 modules, 37300 lines,
1773 theorems. Verify with `scripts/counts.sh` and `scripts/compile.sh` before
you report.

One command per Bash call; never chain; never `cd`. `Edit`/`Write` only — no
heredocs, no `sed -i`. New scripts in `scripts/`, **prefixed with your stream
name**. Commit at every stopping point with your worktree's `scripts/gitcp.sh`;
do not push.

**Evidence rules, carried forward from r0043 because they worked:**

* A claim about a declaration is checked against the **built `.olean`**
  (`#check @d`, `#print axioms d`), not read off a source line. agent2's r0043
  stream did this and caught what a name-only check would have missed.
* **A negative result is a result.** agent5's r0043 stream moved zero rows and
  produced the round's sharpest finding — that r0041 changed expressibility
  rather than statedness. Do not manufacture movement.
* **Do not inflate your own number.** agent3's r0043 stream ruled its own row
  `S≠` rather than `S+P` when the honest reading required it.
* **Correct the other streams.** agent4 corrected agent1 in r0043 and was right.
  If a finding of mine or of another agent looks wrong, say so with the evidence.
* **The plan is not evidence.** If this plan asserts something about the tree
  that turns out to be false, report that as a finding.

## Deliverable

`reports/r0044-report-from-agentN-to-orchestrator-<class>-<area>.md`, with a
count, a list, and the instrument you built. Name the script that reproduces it.

## Orchestrator steps

1. Commit this plan; launch eight agents.
2. Spot-check the vacuity findings hardest — a false positive there impugns an
   `S+P` row, which is the development's strongest claim, so the cost of a wrong
   call is asymmetric.
3. Consolidate into `analyses/specification-defects.YYYY-MMDD-HH:MM.orchestrator.md`.
4. Replace `PaperInventory.md`'s prose about classes 1–4 with the measured counts,
   and add a row for vacuity if the sweep finds a population.
