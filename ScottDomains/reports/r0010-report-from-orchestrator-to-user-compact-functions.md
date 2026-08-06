---
round: r0010
from: orchestrator
to: user
subject: compact-functions
date: 2026-0806-14:30
started: 2026-0806-14:24
finished: 2026-0806-14:30
related:
  - plans/r0010-plan-from-orchestrator-to-orchestrator-compact-functions.md
  - reports/r0009-report-from-orchestrator-to-user-function-space-algebraic.md
---

# r0010 — Every compact function is a finite join of step functions

`ScottDomains/CompactFunction.lean`: 146 lines, 2 definitions, 7 theorems,
0 `sorry`, 0 warnings. The mathematics built on the first attempt; the only
follow-up edit was to drop a hypothesis the linter reported as unused. Elapsed
6 minutes.

| # | Criterion | Measurement |
| -- | --------- | ----------- |
| 1 | Builds | 0 errors, 0 warnings |
| 2 | Nothing unproved | 0 `sorry`, no `sorryAx` |
| 3 | Stated as the paper needs it | for compact `g`, a **finite** `S ⊆ stepsBelow g` with `IsLUB S g` |
| 4 | No unnecessary induction | the proof never shows that a finite join of compacts is compact |

## The theorem and the shortcut in its proof

`finiteJoinsBelow f` is the set of elements that are a least upper bound of some
finite set of step functions below `f`. It is nonempty (`⊥` joins the empty set),
directed (the union of two finite subsets is finite and bounded by `f`, so r0007's
`BoundedComplete (ScottHom α β)` supplies the join), contained in `↓f`, and its
least upper bound is `f` — the last by r0009's argument, since a single step
function is already the join of a one-element set.

Applying compactness of `g` to that directed set gives `J ∈ finiteJoinsBelow g`
with `g ≤ J`, and `J ≤ g`, so `g = J`.

The plan flagged what this avoids and it held: **nowhere does the proof show that
a finite join of compact elements is compact.** That would be an induction over
the finite set using `isCompactElement_of_isLUB_pair`. It is unnecessary, because
`J` turns out to *be* `g` — the compactness of the join comes for free from the
element it equals.

For the second round running, the `unusedSectionVars` linter sharpened the
statement: `isLUB_finiteJoinsBelow` needs only algebraicity of `D` and `E`, not
bounded completeness of `E`. The same split of hypotheses that
`FunctionSpaceDomain.lean` records holds here.

## A correction to how I have been reporting progress

You asked whether any of the development's theorems are from the paper. They are,
and the progress table was hiding it. `docs/PaperInventory.md` counted only the
paper's 30 **numbered** results, so it read "0 of 28" while eight substantive
claims the paper makes *in prose* were already formally verified — six of them
the body of Theorem 7 itself. The table now lists those eight explicitly, with
the page or proof each comes from, and states plainly that the remaining ~47
theorems are supporting API the paper assumes or elides.

Current totals: 55 theorems, 15 definitions, 12 instances, 7 modules, 1131 lines,
0 `sorry`.

## Theorem 7

| # | Conjunct | Status |
| -- | -------- | ------ |
| 1 | `D → E` is a cpo | done, r0006 |
| 2 | `D → E` is bounded complete | done, r0007 |
| 3 | `D → E` is algebraic | done, r0009 |
| 4 | `K(D → E)` is countable | r0011 — and this round is what makes it reachable |

Countability now follows a clear path: a compact function is a finite join of
step functions, each named by a pair in `K(D) × K(E)`, so `K(D → E)` is covered
by the finite subsets of a countable set — the same
`Set.countable_setOf_finite_subset` that r0005 used.
