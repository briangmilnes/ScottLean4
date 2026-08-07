---
round: r0036
from: orchestrator
to: orchestrator
subject: five-way-open-results
date: 2026-0807-08:32
status: pending
related:
  - plans/r0035-plan-from-orchestrator-to-orchestrator-session-restart.md
  - docs/PaperInventory.md
  - docs/Performance.md
---

# r0036 — Five-way plan for the six open numbered results

Five agents, one stream each, covering **all six** results the paper numbers and
the development has not proved. Nothing open is left unassigned; Lemma 30 rides
with Theorem 29 because it is provably unstatable until `V` exists.

## Baseline, measured this session

`main` at `615e08e`, working tree clean apart from one untracked log and one
untracked PDF. All quantities re-measured, not carried forward:

| # | Quantity | Value | Measured by |
| -- | -------- | ----- | ----------- |
| 1 | Build | `Build completed successfully (1137 jobs).`, 0 errors, 0 diagnostics, 0 non-`sorry` warnings, wall 1.76 s replay, peak RSS 790 MiB | `scripts/compile.sh -r r0035` |
| 2 | Modules / lines / theorems | 61 / 19497 / 906 | `scripts/counts.sh` |
| 3 | `sorry` | **2** — `Skeleton/Recovered.lean:258` (`thm14`), `Skeleton/Section6.lean:197` (`thm18`) | `scripts/counts.sh` |
| 4 | Worktrees | agent1–agent6 all at `615e08e`, merged, 0 behind, 0 dirty, packages symlinked | `scripts/worktree-sync.sh --ff` |
| 5 | Numbered results complete | 22 of 29; Thm 16 settled in all three directions and counted in neither column | `docs/PaperInventory.md` rows 2, 2a |

## The six open results, and why each stream is unblocked

r0035's candidate table ranked Theorem 18 last, "only if the user collects
`[Smy83a]`". **That ranking is wrong and this plan corrects it.** Reading
`ScottDomains/Section62.lean` lines 142–229 — written by r0034's agent6 — shows
the proof was recovered in full from **Jung 1989, which is in
`ScottDomains/papers/`**, with a five-step map naming exactly which steps are
absent. `[Smy83a]` is needed only for *attribution*, not for the mathematics, and
Section62 states plainly that `f_S` cannot be Smyth's construction anyway.
Theorem 18 is therefore a scheduled proof stream, not research.

| # | Result | Status now | Why it can start today |
| -- | ------ | ---------- | ---------------------- |
| 1 | Thm 14 | `sorry` | Four gaps enumerated in `thm14`'s docstring; gap 2 is a named missing bridge lemma |
| 2 | Thm 18 | `sorry` | Jung's proof mapped to five steps in `Section62.lean`; steps 1–3 absent, step 5 already proved as `isBifinite_iff_mubClosure` |
| 3 | Thm 27 | conditional | Blocked only on `IsNormallyRepresented`. Mathlib has **zero** `IsAtomless` (grepped this session, both `Order/Atoms.lean` and all of `Mathlib/`), but it has `Order.iso_of_countable_dense` — Cantor's isomorphism theorem by back-and-forth over `PartialIso` — which is the template |
| 4 | Lem 28 | 3 of 9, wrong notion | `PRepresentable.IsPRepresentable` exists (r0034) and is kernel-checked distinct from `IsRepresentable` |
| 5 | Thm 29 | first sentence only | The second sentence needs `V` as the ω-colimit of `Mⁿ(1)`; `Plus D` and `MPair` already exist |
| 6 | Lem 30 | 0 of 9, unstatable | Statable the moment `V` exists — so it is stream 5's second deliverable, not a sixth agent |

## The five streams

| # | Agent | Namespace | Result | Deliverable if the whole thing does not land |
| -- | ----- | --------- | ------ | -------------------------------------------- |
| 1 | agent1 | `ScottDomains.SFP` | Theorem 14 | gap 2's bridge lemma alone |
| 2 | agent2 | `ScottDomains.JungSFP` | Theorem 18 | Jung's Lemma 2.13 (step 2) alone — it is *the* gap |
| 3 | agent3 | `ScottDomains.Atomless` | Theorem 27 | the countable atomless Boolean algebra with its back-and-forth isomorphism |
| 4 | agent4 | `ScottDomains.PRep` | Lemma 28 | the nine-conjunct statement at `IsPRepresentable` plus one re-proved conjunct |
| 5 | agent5 | `ScottDomains.Colimit` | Theorem 29 second sentence, `V`, Lemma 30 | `V` with its `Domain` instance |

Namespace per agent is process rule 1 (below). None of the five collides with an
existing namespace: `Isomorphism`, `ClosureProperties`, `Dyadic`, `Combinator`,
`CombinatorRep`, `BifiniteUniversal`, `PRepresentable`, `Section62`,
`Universality`, `Recursive`, `Hoare`, `Smyth`, `Plotkin`, `IdealCompletion`,
`ContinuousAlgebra`, `PowerdomainBC`. Note `PRep` ≠ the existing `PRepresentable`
— agent4 *imports* the latter and adds to `PRep`.

## Why five, and what five costs

`docs/Performance.md` measures the constraints and recommends 4 to 6 agents. Five
sits inside that and clears the two that bind:

| # | Constraint | Binds at | This round |
| -- | ---------- | -------- | ---------- |
| 1 | Declaration collisions | ~6 agents | namespace per agent; zero collisions r0029–r0034 under this rule |
| 2 | Review bandwidth | ~5 agents | at the limit — accepted, because all five streams close numbered results |
| 3 | Memory | ~5 concurrent builds | agents build rarely and not in lockstep; 2.3 GiB PSS each against 31 GiB |
| 4 | CPU | ~8 agents in bursts | five agents drew ~1.2 of 20 cores in r0028, a 9% duty cycle |

These figures are settled; do not re-measure them.

## Dependencies

Only one, and it is merge-order rather than launch-order:

1. Stream 4's Lemma 28 instantiates at `Dyadic.U`, which is already **on `main`**
   from r0034 — so unlike r0034's stream 4, this one has no waiting to do.
2. Stream 5's Lemma 30 needs its own `V`, built in the same stream. Internal.

Launch all five at once.

## Expected outcome

| # | Case | Numbered results complete | `sorry` |
| -- | ---- | ------------------------- | ------- |
| 1 | Baseline | 22 of 29 | 2 |
| 2 | Streams 1 and 2 land | 24 of 29 | **0** |
| 3 | Streams 3 and 4 also land | 26 of 29 | 0 |
| 4 | Stream 5 lands including Lem 30 | **29 of 29** | 0 |

Case 2 is the metric that matters most: it takes the development to zero `sorry`
for the first time. Case 4 is the optimistic bound, not the forecast — Lemma 30
has nine conjuncts over a carrier that does not yet exist.

## Process rules for every agent plan

Restated in each per-agent plan; check the reports for compliance.

1. **Namespace per agent** — as assigned above. Two clashes among five agents
   before this rule; zero across r0029–r0034 under it.
2. **Edit/Write only, never heredocs, never `sed -i`.**
3. **One command per Bash call. Never chain, never `cd`.** 133 prompts in one
   measured day contained `&&`/`;`/`|`/`$(…)`; 58 began with `cd`.
4. **Multi-step work becomes a script in `scripts/`** — standing-authorized.
5. **Read the PDF, not the paraphrase.** Four separate corrections to the r0034
   plan came from agents doing this.
6. **The plan is not evidence.** Four of six r0034 stream descriptions were wrong
   on the mathematics. Contradicting this plan from the source is the expected
   behaviour, and the report should say so when it happens.
7. **Commit on the agent branch at every stopping point**, including with build
   errors. A stream watchdog stopped four of six r0034 agents at 600 s of
   silence; the two that had committed lost nothing.
8. **Agents commit, only the orchestrator pushes.** "No tracking information" on
   push is the expected outcome for an agent, not an error.
9. **State the ranked deliverable.** Each plan names what a partial landing looks
   like; land the smaller complete result rather than leaving a `sorry`.

## Orchestrator steps

1. ~~`scripts/compile.sh -r r0035`, `scripts/counts.sh`, `scripts/worktree-sync.sh --ff`~~ — done, table above.
2. ~~Cut five per-agent plans~~ — done, `plans/r0036-plan-from-orchestrator-to-agentN-*.md`.
3. Commit the plans to `main` and fast-forward the worktrees so every agent sees
   the whole round, per `scripts/collect-agent-plans.sh`'s rationale.
4. Launch five agents, one per worktree.
5. On each report: review the diff, run `scripts/axioms.sh` on the new modules,
   merge, rebuild, then push.
6. **Composition check after the merges** — `scripts/axioms.sh -i <module> …`
   importing every new module together. `lake build` cannot catch a cross-module
   duplicate; that is how r0028's clash survived 971 green jobs.
7. Update `docs/PaperInventory.md` rows 2, 2c, 2d, 5 and 6 from the measured
   counts, not from this plan's expectations.
