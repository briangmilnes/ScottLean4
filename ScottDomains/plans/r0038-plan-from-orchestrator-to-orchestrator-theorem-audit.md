---
round: r0038
from: orchestrator
to: orchestrator
subject: theorem-audit
date: 2026-0807-14:45
status: pending
related:
  - docs/PropertiesVsTheorems.md
  - docs/PaperInventory.md
---

# r0038 — Audit: 1308 theorems against 99 paper properties

The user's question, restated as a measurable one: **is the development carrying
theorems that serve neither a paper property nor a proof of one?**

`docs/PropertiesVsTheorems.md` establishes the baseline — 1308 theorem-ish
declarations, 99 paper properties, 130 names cited nowhere but their own
declaration. This round classifies every theorem and produces a recommendation.

## What this round is not

**It is not a deletion round.** No agent removes a declaration. The r0020
precedent is the model: speculative API was **commented out in place, with a note
on why it exists and what is instructive about it**, and the build was confirmed
unchanged — which also proved the three `@[simp]` ones among them had never been
firing. Agents classify and recommend; the orchestrator and the user decide what
goes.

The `sorry` count, the numbered-result count and every existing proof must be
unchanged at the end of this round. An audit that improves the metrics is an
audit that broke something.

## Classification

Every `theorem`/`lemma` gets exactly one label:

| # | Label | Meaning | Evidence required |
| -- | ----- | ------- | ----------------- |
| 1 | `P` | states a paper property | name the § and the numbered result or prose claim |
| 2 | `S` | support, and something cites it | name one citing declaration |
| 3 | `A` | projection/`simp` API — `_apply`, `_coe`, `_bot` | say whether it is `@[simp]` and whether removing the tag changes the build |
| 4 | `U` | uncited, not a paper property, not API | say what it was written for, if that is recoverable from its docstring or round |
| 5 | `D` | duplicate — same statement as another declaration under a different name | name the other one |
| 6 | `W` | proved at a strength nothing consumes | name the consumer and the weaker statement that would serve |

`P` is not decided by the docstring's claim. A docstring saying "**Lemma 17**" is
a claim to check against the paper's text, and `PropertiesVsTheorems.md` §1 warns
that three conjunct counts have already moved once.

## Streams

Six agents. The split is by area rather than by file count, so that one agent
holds all the modules that could duplicate each other — `D` and `W` are
cross-module labels and cannot be found by an agent that sees one side.

| # | Agent | Namespace for any new file | Modules | Thms |
| -- | ----- | -------------------------- | ------- | ---- |
| 1 | agent1 | `Audit.Foundations` | `WayBelow`, `Domain`, `Powerset`, `ScottHom`, `StepFunction`, `FunctionSpaceDomain`, `CompactFunction`, `FunctionSpaceCountable`, `Product`, `Currying`, `Lift`, `StrictHom`, `Smash`, `CoalescedSum`, `FixedPoint`, `UniformFixedPoint`, `EffectivePresentation`, `ComputableFunction`, `ExistingTheories` | ~131 |
| 2 | agent2 | `Audit.Projections` | `Projection`, `FinitaryProjection`, `NormalSubposet`, `NormalProjection`, `Theorem6`, `FinitaryProjectionPoset`, `FinitaryProjectionEmbedding`, `Bifinite`, `MinimalUpperBounds`, `Section62`, `SFP` | ~172 |
| 3 | agent3 | `Audit.Skeleton` | `Skeleton/*` (5 files), `ClosureProperties*` (4 files), `Isomorphism/*` (5 files) | ~163 |
| 4 | agent4 | `Audit.Powerdomains` | `IdealCompletion`, `Powerdomain/*` (5 files), `ContinuousAlgebra` | ~197 |
| 5 | agent5 | `Audit.SectionSeven` | `UniversalDomain`, `Universality`, `RecursiveDomain`, `Combinator`, `CombinatorRep`, `Dyadic`, `Atomless`, `PRepresentable`, `PRep`, `PRepFun`, `PRepSum`, `Lemma28AtU` | ~419 |
| 6 | agent6 | `Audit.Bifinite` | `BifiniteUniversal`, `Colimit`, `LemThirty`, `JungSFP`, `JungFinite`, `JungNets`, `ContinuousConstruction` | ~228 |

Stream 5 is the largest and the one where duplication is most likely, because
Lemma 28 has been attacked at two different notions by four agents across three
rounds. It gets the whole §7 representability stack for that reason.

## The two questions each stream must answer beyond the labels

1. **Is `ContinuousConstruction` (35 theorems) still needed?** It implements
   r0031's route to Theorem 18, whose (★) r0036 measured as *equivalent* to
   Theorem 18 rather than below it, and which Jung's proof never passes through.
   agent6 decides: which of its 35 are cited by the live route, which are
   evidence worth keeping as a recorded dead end, which are neither.
2. **Is `CombinatorRep` (29 theorems) still needed?** It proves Lemma 28's
   conjuncts at the *closure* reading, which r0037 kernel-checked as not
   transferring to the projection notion the paper means. agent5 decides. Note
   the `⊗`/`⊕` counterexample lives here and **is** load-bearing evidence — the
   answer is likely "reduce", not "remove".

## Deliverable, per agent

1. `reports/r0038-report-from-agentN-to-orchestrator-audit-<area>.md` with a
   table: declaration, module, label, evidence. One row per theorem. This is
   long and that is the point — the round's value is the table.
2. A summary count per label, and the `U`/`D`/`W` rows called out separately.
3. **No edits to any `.lean` file.** Recommendations only. The one exception:
   an agent that finds a `D` pair may add a `theorem` in its own audit namespace
   proving the two statements equivalent, which converts "looks the same" into
   evidence.

## Method notes for the agents

- `scripts/module-counts.sh` gives per-module counts; `scripts/unused-theorems.sh`
  gives the 130-name candidate list with its stated limits — read the script
  header before quoting the number, since it under-reports by design.
- For `S`, grep the corpus for the name. For `A`, check the `@[simp]` tag against
  `scripts/module-counts.sh`'s `simp` column.
- For `W`, the tell is a hypothesis in the statement that no call site supplies —
  r0032 and r0034 both found results proved at strictly weaker hypotheses than
  declared (`thm25` at cpo strength, `thm12` needing only `[IsAlgebraic D]`).
- Read the paper for `P`. `scripts/pdf-render.sh`, `pdf-section.sh`,
  `pdf-crop.sh`, `pdf-find-page.sh` are on `main`.

## Where each artifact goes

GRASE rule 8.4 reserves `analyses/` for the orchestrator: agents do not write
there. So the round has two tiers, and they are different documents rather than
the same document copied.

| # | Tier | Author | Path | Content |
| -- | ---- | ------ | ---- | ------- |
| 1 | per-area report | agentN | `reports/r0038-report-from-agentN-to-orchestrator-audit-<area>.md` | the full per-declaration table for that agent's modules — one row per theorem, with label and evidence. Long by design; this is the raw data |
| 2 | consolidated analysis | orchestrator | `analyses/theorem-audit.YYYY-MMDD-HH:MM.orchestrator.md` | the six tables merged, deduplicated across area boundaries, with the per-label totals, the rate against r0020's 3%, and the recommended action list |

The split matters for more than filing. A `D` (duplicate) or `W` (over-strength)
pair can straddle two agents' areas, and neither agent will see both halves — the
same blindness that let r0028's duplicate declaration survive 971 green jobs, and
that r0037 hit twice with stale cross-stream claims. **Finding those pairs is the
orchestrator's job at tier 2**, not a gap in the agents' work, and the
consolidated analysis is where it happens.

Tier 2 also carries the answer to the user's actual question in one line: how many
of 1308 theorems serve neither a paper property nor a proof of one.

## Expected outcome

The useful result is a **number with a list behind it**: how many of 1308 serve
nothing. r0020's rate was 6 of ~199, about 3%. If the current rate is near that,
the answer to the user's concern is that the ratio is the cost of formalizing a
paper that elides its own foundations, and the file `PropertiesVsTheorems.md` §5
says which four things would show otherwise. If it is far above 3%, the audit
produces the list to act on.

Either way this round changes no proof and no count. The follow-on round acts on
the list, and acts the way r0020 did — comment out in place with a note, rebuild,
confirm the build is unchanged.

## Orchestrator steps

1. Commit this plan to `main` and fast-forward the six worktrees.
2. Launch six agents, one per area.
3. On each report: spot-check the labels rather than accept them — pick two `P`
   rows and confirm the paper says what the row claims, and two `U` rows and
   confirm nothing cites them. A label is a claim like any other.
4. **Consolidate into `analyses/theorem-audit.YYYY-MMDD-HH:MM.orchestrator.md`**,
   merging the six tables and searching across area boundaries for the `D` and
   `W` pairs no single agent could see.
5. Re-run `scripts/counts.sh` and `scripts/compile.sh` and confirm both are
   unchanged from `702def0`. This round must move no number.
6. Update `docs/PropertiesVsTheorems.md` §4 and §5 from the measured rate.

Six agents is at the top of `docs/Performance.md`'s recommended 4–6. The
constraint that normally binds at six — declaration collisions — does not apply
here, because agents write no Lean beyond an optional equivalence theorem in
their own `Audit.*` namespace. Review bandwidth is the real cost, and it is
accepted: the tables are the deliverable and reading them is the work.
