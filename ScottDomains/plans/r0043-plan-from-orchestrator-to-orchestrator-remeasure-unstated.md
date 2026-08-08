---
round: r0043
from: orchestrator
to: orchestrator
subject: remeasure-unstated
date: 2026-0808-15:05
status: pending
related:
  - analyses/property-coverage.2026-0808-11:59.orchestrator.md
  - docs/PaperInventory.md
---

# r0043 — Re-measure row 2e

`PaperInventory.md` row 2e currently reads **"≈22, and zero of them numbered"**.
The 22 is **subtraction, not measurement**: r0040 measured 62 unstated
properties, r0041 was believed to have closed about 40, and 62 − 40 was written
down. That is exactly the kind of derived figure this project has twice been
burned by — the "13 prose claims" that turned out to be a count of our own
output, and the 1308 theorem count that was wrong in both directions.

**This round produces the real number.**

## Scope: the 62 rows, and only those

Each r0040 stream recorded its `N` rows with the paper's sentence and printed
page. Re-check **each of your own area's `N` rows** against the tree as it stands
now, and assign the r0040 label afresh: `S+P`, `S+H`, `S≠`, `P`, or `N`.

| # | Agent | Area | `N` rows to re-check |
| -- | ----- | ---- | ----: |
| 1 | agent1 | §2, §3 | 24 |
| 2 | agent2 | §4 → Lemma 10 | 12 |
| 3 | agent3 | Thm 11 → §5 | 9 |
| 4 | agent4 | §6 | 4 |
| 5 | agent5 | §7 | 13 |

Do **not** re-survey the sections. The 177 rows that were not `N` are out of
scope; only a row that was `N` can have changed in the direction this round
measures. If you notice a non-`N` row that has *regressed*, report it as a
finding but do not go looking.

## What changed under you

r0041 and r0042 added 22 modules. The ones most likely to have closed your rows:

* `Flat`, `FlatOmega`, `FlatPowerdomain`, `FlatSection6` — the flat cpo, `N⊥`,
  `T`, and §5's `N⊥` powerdomain calculations;
* `Morphism` — `f × g`, `f ⊗ g`, `f ⊕ g`, `f + g` and the multiary forms;
* `PowerdomainMap`, `PowerdomainMapRep`, `PowerdomainCompacts` — `f♮`/`f♯`/`f♭`;
* `Effective/Powerset`, `Effective/FunctionSpace` — effective presentations,
  Theorem 7's second and third sentences;
* `Kleene/*` — `fix` as a `ScottHom`, Theorem 3's existence half, the factorial
  and grammar examples, `f*`, `G_f`;
* `JungCor136`, `PropertyM`, `Iwamura`, `JungBicomplete`, `Thm18`, `Closure`.

**A row is `S+P` only if you name the declaration and confirm it exists.** A
plausible-looking module name is not evidence; r0038 found two files asserting
false things about themselves.

**A row stays `N` only after grepping three ways**, as in r0040. The bar does not
drop because the number is expected to be smaller.

## Deliverable

`reports/r0043-report-from-agentN-to-orchestrator-remeasure-<area>.md`: one row
per previously-`N` property — the paper's sentence, its r0040 label, its label
now, and the declaration or the three greps. Then the count: how many of your `N`
rows are now stated, and how many remain.

**No `.lean` file is edited.** The build, the `sorry` count (**0**) and the
numbered-result count must be identical at the end.

## Process rules

One command per Bash call; never chain; never `cd`. `Edit`/`Write` only — no
heredocs, no `sed -i`. New scripts in `scripts/` prefixed with your stream name.
`scripts/lean-decls.py --list <files>` gives comment-aware declaration names.
Commit at every stopping point with your worktree's `scripts/gitcp.sh`; do not
push. **The plan is not evidence.**

## Orchestrator steps

1. Commit this plan; fast-forward the worktrees; launch five agents.
2. Spot-check every row that moved `N → S+P`, since that is the round's product.
3. Consolidate into `analyses/property-coverage-remeasure.YYYY-MMDD-HH:MM.orchestrator.md`
   and replace row 2e's estimate with the measured figure.
