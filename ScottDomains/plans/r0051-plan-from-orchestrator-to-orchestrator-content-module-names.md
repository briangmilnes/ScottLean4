---
round: r0051
from: orchestrator
to: orchestrator
subject: content-module-names
date: 2026-0810-15:05
status: pending
related:
  - plans/r0050-plan-from-orchestrator-to-orchestrator-numbered-name-standard.md
---

# r0051 — module names say what is in them, not who typed them

24 of the package's 124 modules are named `A<n>*`, where `<n>` is the **agent
number** of whoever wrote them. `A6ProjectionBifinite.lean` records that agent6
typed it; git already records that, and nothing records what it contains.

Run this **after r0050 lands**, not folded into it: r0050 already has three
sequenced phases, and module renames cascade through `import` lines, so mixing
them makes a merge failure harder to attribute.

## Why the prefix exists, and why it is not needed

Each agent works in its own worktree, so nothing collides while they work.
Collisions happen only at merge, in two forms:

1. **Two agents create the same filename with different content.** Git reports an
   add/add conflict — loud, and fixable.
2. **Two agents create the same declaration name in the same namespace.** Git
   merges cleanly, and the *package* then fails to compile. Silent at merge time,
   which is why `scripts/axioms.sh -i` exists.

The `A<n>` filename prefix buys immunity to (1) and the `R<NN>.Agent<n>`
namespace buys immunity to (2), and both do it without the orchestrator having
to think. That is the entire justification: it let a plan say "agent6, prove
`FpImagesBifinite V`" without also saying where to put it.

**That is a job the plan should do.** A round's topic assignments are already
disjoint, so disjoint content names follow from them directly.

## The rule that stops it recurring

**Every future plan assigns each agent its module name alongside its theorem.**
A rename without this just re-accumulates `A9*.lean` next round. Add the module
name to the per-agent table in every plan from r0052 on.

Namespaces keep `R<NN>.Agent<n>` for now — flattening them touches hundreds of
qualified references and is a separate round with a different risk profile.

## The 24 renames

Names are taken from each module's own `#` heading. Verify the heading before
renaming; if it does not support the name below, choose from the heading and say
so in the report.

| # | From | To |
| -- | ---- | -- |
| 1 | `A1Theorem2.lean` | `Theorem2.lean` |
| 2 | `A1Lemma24.lean` | `Gunter87Lemma24.lean` |
| 3 | `A1R46.lean` | `UniversalClosures.lean` |
| 4 | `A2Lemma28.lean` | `Lemma28Residue.lean` |
| 5 | `A2Thm29Universal.lean` | `Theorem29NormalInput.lean` |
| 6 | `A3Lemma30Schemes.lean` | `Lemma30Schemes.lean` |
| 7 | `A3Thm29.lean` | `Theorem29Necessity.lean` |
| 8 | `A4FunctionSpaceBifinite.lean` | `FunctionSpaceBifinite.lean` |
| 9 | `A4Lemma17Fun.lean` | `Lemma17FunctionSpace.lean` |
| 10 | `A4PowerdomainRep.lean` | `PowerdomainRepresentation.lean` |
| 11 | `A4RepArrow.lean` | `Lemma30ArrowObstruction.lean` |
| 12 | `A5Thm137.lean` | `JungTheorem137.lean` |
| 13 | `A5Thm29Finite.lean` | `Theorem29FiniteBasis.lean` |
| 14 | `A5Unfinished.lean` | `UnfinishedProofs.lean` |
| 15 | `A6ProjectionBifinite.lean` | `ProjectionBifinite.lean` |
| 16 | `A7SneqRows.lean` | `PaperStatementRows.lean` |
| 17 | `A7Thm26Arity.lean` | `Theorem26Arity.lean` |
| 18 | `Effective/A1FlatRecursive.lean` | `Effective/FlatRecursivePresentation.lean` |
| 19 | `Effective/A2Compactness.lean` | `Effective/StepFunctionBoundedness.lean` |
| 20 | `Effective/A3FreeCarrier.lean` | `Effective/FreeCarrier.lean` |
| 21 | `Effective/A3Operator.lean` | `Effective/Operator.lean` |
| 22 | `Effective/A3StepDecidable.lean` | `Effective/StepFunctionsDecidable.lean` |
| 23 | `Effective/A3StrictRecursive.lean` | `Effective/StrictFunctionEnumeration.lean` |
| 24 | `Effective/A4Recursion.lean` | `Effective/Recursion.lean` |

Three needed a name chosen rather than derived, because they were named for a
round or a mood: `A1R46` (its heading is "two refuted universal closures and the
record of one restatement"), `A5Unfinished` ("the `S+H` rows re-measured"), and
`Effective/A3FreeCarrier`. Their proposed names above come from the headings.

### Collisions to check first

`Lemma28AtU.lean`, `PowerdomainMapRep.lean`, `Theorem6.lean` and
`JungCor136.lean` already exist. None of the 24 targets duplicates one, but
confirm with a directory listing before the first `git mv` rather than
discovering it at the eighth.

## Method

One module at a time, single-agent, sequential:

1. `git mv <old> <new>`.
2. Build. The elaborator names every file whose `import` is now stale.
3. Fix exactly those `import` lines, and the package root `ScottDomains.lean`.
4. Rebuild to **0 errors, 0 warnings**. Then the next module.

No grep decides which imports change — the compiler does. Do not batch the
`git mv`s: a batch turns one attributable failure into 24 simultaneous ones.

Also fix, in the same round, the three `section` names r0050's agent2 found and
correctly left alone: `section Thm27` at `Atomless.lean:605` and
`Dyadic.lean:448`, and `section Thm26` at `Combinator.lean:522`. They are
`section`s, not `namespace`s, so they change no full name and no reference — but
they are what a reader greps for.

## Hard rules

* A rename changes a name and nothing else. No statement, no proof, no binder.
* **No `sorry`.** The package is at 0 and stays at 0.
* Build with `scripts/compile.sh -r r0051`; 0 errors, 0 warnings.
* One shell command per Bash call; never chain; never `cd`. `Edit`/`Write` only.
* Commit with `scripts/gitcp.sh`; agents do not push.

## Deliverable

`reports/r0051-report-from-agentN-to-orchestrator-content-module-names.md`: the
24 renames as executed, any name changed from this table and why, the count of
`import` lines fixed per module, and the build's error and warning counts.
