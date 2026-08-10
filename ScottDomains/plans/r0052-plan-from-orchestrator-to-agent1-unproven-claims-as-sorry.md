---
round: r0052
from: orchestrator
to: agent1
subject: unproven-claims-as-sorry
date: 2026-0810-15:40
status: pending
---

# r0052 — make the unproven work visible to the build

Every unproven paper result in this development is recorded as a `Prop`-valued
`def` that nothing proves, with consumers taking it as a hypothesis. That
convention asserts nothing false and propagates no `sorryAx` — and it is
**invisible to every automatic check**: no `sorry`, no warning, no failing build.
Four rounds were spent building instruments to recover the visibility it gave up.

This round makes the unproven work visible: each unproven claim gets a
`theorem … := sorry`.

## Task 1 — the right count

`scripts/a6-env-scan.sh` + `a6-summarize.py` report **120 Prop-valued defs, 72
with no unconditional proof**. That 72 mixes two different things:

* **claims** — a paper result stated as a `def` because nobody has proved it;
* **concepts** — genuine definitions (`Flat.le`, `Atomless.Legal`,
  `IsStepEnumeration`, `JoinIdxAt`, `HasTwoMubBelow`), which belong as `def`s.

The last adjudication split 55 as **19 claims / 36 concepts**, and the population
has grown by 17 since. **Redo it over all 72.** For each, record: claim or
concept, and the one-line reason. A `def` is a *claim* if it states something the
paper (or a cited paper) asserts; it is a *concept* if it names a property that
theorems are stated about.

Note 9 of the 120 are r0050 `alias` defs (`Thm29Normal := Theorem29Normal` and
the like). They are scaffolding, deleted in r0050 phase 2 — exclude them from the
census and say how many you excluded.

Publish the adjudication as `analyses/claim-census.<stamp>.agent1.tsv`.

## Task 2 — convert every claim to a `sorry`

My provisional list is **8**; your census decides the real number, and the census
governs. The 8 I can defend:

| # | Claim | Refs (both names) |
| -- | ---- | ----------------: |
| 1 | `LemThirty.Theorem29Normal` | 92 |
| 2 | `Effective.StepFunctionsDecidable` | 43 |
| 3 | `LemThirty.Theorem29SecondAtDomains` | 74 |
| 4 | `LemThirty.Lemma30AtV` | 27 |
| 5 | `Colimit.Lemma30Arrow` | 16 |
| 6 | `Effective.Theorem7ArrowRecursive` | 32 |
| 7 | `Effective.Theorem7StrictRecursive` | 19 |
| 8 | `Effective.PreservesRecursivePresentation` | 21 |

**Do not convert a refuted claim.** `Colimit.Theorem29Second`,
`R49.Agent7.Theorem26Printed` and `R45.Agent3.Theorem29NormalWithoutDomain` are
proved **false**; a `sorry` asserting them would be asserting a falsehood. They
stay `def`s. If your census finds others in that state, treat them the same and
list them.

### The form to use, and why

**Keep the `def`. Add a sorried theorem beside it.**

    def Theorem29Normal : Prop := …          -- unchanged
    theorem theorem29Normal_unproven : Theorem29Normal := sorry

Not `theorem Theorem29Normal : <body> := sorry` replacing the `def`. The reason
is concrete: ~300 reference sites take these as hypotheses
(`theorem foo (h : Thm29Normal) : …`), and those conditional theorems are the
**proved output of rounds r0045–r0049** — the reduction chain that took
`Lemma30AtV` from arity 3 to arity 1 and `Thm29Normal` to its finite-basis case.
Replacing the `def` deletes the type those hypotheses are written at and erases
that chain. Adding the sorried theorem keeps every reduction and makes the hole
visible, which is the whole point.

Name each `<claimNameLowerCamel>_unproven`. Give each a one-line docstring saying
what must be proved to remove the `sorry`.

## Consequences to expect, and to report

* **`sorry` goes from 0 to N**, first time since r0042. That is the intended
  outcome, not a regression. `scripts/compile.sh` will report it; do not try to
  drive it back to 0.
* Every consumer can now discharge its hypothesis from the sorried theorem.
  **Do not do that.** Leave the conditional theorems conditional — a theorem that
  silently routes through `sorryAx` is exactly what this convention was avoiding.
  Report how many consumers *could* now be made unconditional; change none.
* `#print axioms` on anything applying a sorried theorem will show `sorryAx`.
  Check that **no existing theorem's axiom footprint changes** — if one does, a
  consumer got rewired and must be reverted.

## Hard rules

* Build with `scripts/compile.sh -r r0052`; **0 errors, 0 warnings other than the
  `sorry` warnings**, and the `sorry` count equal to N.
* Change no statement, no proof, no binder of any existing declaration.
* One shell command per Bash call; never chain; never `cd`. `Edit`/`Write` only.
* Commit with your worktree's `scripts/gitcp.sh`; do not push.

## Deliverable

`reports/r0052-report-from-agent1-to-orchestrator-unproven-claims-as-sorry.md`:
the census totals (claims / concepts / aliases excluded / refuted), the list
converted, the `sorry` count, the count of consumers that could be made
unconditional and were not, and the build's error and warning counts.
