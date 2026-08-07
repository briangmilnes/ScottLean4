---
round: r0030
from: orchestrator
to: orchestrator
subject: remaining-theorems
date: 2026-0806-19:55
status: pending
related:
  - plans/r0028-plan-from-orchestrator-to-orchestrator-five-fold-parallel.md
  - reports/r0028-report-from-agent3-to-orchestrator-fp-fc-posets.md
  - reports/r0028-report-from-agent4-to-orchestrator-minimal-upper-bounds.md
---

# r0030 — The remaining 14 numbered results

After r0028, **15 of the paper's 29 provable numbered results are formally
verified**. Round r0029, in flight, closes the last four definitions (the Hoare,
Smyth and Plotkin powerdomains, and `D∞`). This plan covers what is left to
prove, and says how many agents each part admits.

## What remains

| # | Result | Statement | Blocked on |
| -- | ------ | --------- | ---------- |
| 1 | Lem 9 | product / function-space iso laws over `D, E, F` | **statement recovery** — the 1990 Type-3 fonts drop every `⊗` and `⊥` |
| 2 | Thm 12 | initiality of a continuous algebra satisfying axioms `T` | **statement recovery** — "axioms `T`" is undefined as printed |
| 3 | Lem 13 | `D` bounded complete ⟹ powerdomains `D]`, `D[` bounded complete | r0029 powerdomain definitions |
| 4 | Thm 14 | equivalent characterizations of an (algebraic / BC) domain | **statement recovery** — the characterizations are garbled |
| 5 | Thm 16 | second conjunct: `Fp(D) ↪ (D → D)` is an embedding | a documented mathematical obstacle, below |
| 6 | Thm 18 | `D`, `D → D` domains ⟹ `D` bifinite | a missing construction, below |
| 7 | ~~Thm 21~~ | `F` representable over `U` ⟹ a domain `D` with `D ≅ F(D)` | **proved in r0029** — `ScottDomains.Recursive.thm21`, kernel-clean, together with `recursiveDomain_funSpace : IsSolvable (fun X => Cpo.funSpace X X)`, the reflexive domain |
| 8 | Lem 24 | `U` cpo, `×` and `→` representable ⟹ setup for universality | **Lem 28's `×` conjunct** (wave A, agent2) — `→` is Lem 23, already proved |
| 9 | Thm 25 | `U` non-trivial domain representing `×`, `→` ⟹ `U` universal | Lem 24 |
| 10 | Thm 26 | any signature: combinators solving the equations | Thm 25 |
| 11 | Thm 27 | any bounded-complete `D`: a projection of the universal domain onto `D` | Thm 25 |
| 12 | Lem 28 | operators `→, ×, ⊗, +, ()⊥, ()], ()[` representable over `U` | r0029 powerdomains, Lem 23 |
| 13 | Thm 29 | `D` bifinite ⟹ `D+` bifinite; solving `D ≅ D+` | Thm 21 |
| 14 | Lem 30 | §5 universal / closure property of the powerdomains | r0029 powerdomains |

Two of these are not proof tasks at all until someone reads the PDF and recovers
a statement, and one is not a proof task until a missing construction exists.
Those three are what set the wave structure.

## Two recorded obstacles, both specific

**Theorem 18** (r0028, agent4). The reduction is done: `isPlotkinOrder_iff_mubClosure`
turns Theorem 18 into two obligations, property M on `K(D)` and finiteness of
`U^∞(u)`. What blocks it is prior to Smyth's case analysis — the perturbing
family `qₙ` needs least upper bounds of **bounded, non-directed** sets, which a
domain that is not bounded complete need not have, and
`CompactFunction.lean`'s decomposition of a compact function into a finite join of
step functions carries `[BoundedComplete β]` — exactly the hypothesis Theorem 18
exists to do without. **The prerequisite is a constructor for continuous functions
on a domain that is not bounded complete.** That is the deliverable, and the
theorem follows it.

**Theorem 16, second conjunct** (r0028, agent3). The paper's sketch takes
`S_f = {x ∈ K(D) | x ⊑ f(x)}`, but `S_f` is not normal; the least normal
`N_f ⊇ S_f` is strictly larger, and a minimal upper bound `m` of `a, b ∈ S_f` must
lie in `N_f` while `f(m)` need only be *an* upper bound of `{a, b}`, not above the
minimal one. So `m ⊑ f(m)` can fail, and with it the projection half `p_{N_f} ⊑ f`.

## Wave A — five agents, all independent

Each agent's work is specified in full in its own plan; those files are the
authoritative instructions, and an agent needs nothing but its own to work. This
table is the coordination view — who owns what, so no two agents collide.

| # | Agent | Owns | Work | Its plan |
| -- | ----- | ---- | ---- | -------- |
| 1 | agent1 | `Powerdomain/BoundedComplete.lean` | **Lemma 13** | `r0030-plan-from-orchestrator-to-agent1-powerdomain-bounded-complete.md` |
| 2 | agent2 | `Powerdomain/Universal.lean` | **Lemma 30**, **Lemma 28** powerdomain conjuncts | `r0030-plan-from-orchestrator-to-agent2-powerdomain-universal.md` |
| 3 | agent3 | `ContinuousConstruction.lean`, `thm18` | **Theorem 18** | `r0030-plan-from-orchestrator-to-agent3-theorem-18.md` |
| 4 | agent4 | `FinitaryProjectionEmbedding.lean` | **Theorem 16**'s embedding conjunct | `r0030-plan-from-orchestrator-to-agent4-theorem-16-embedding.md` |
| 5 | agent5 | `docs/StatementRecovery.md`, `Skeleton/Recovered.lean` | **Lem 9, Thm 12, Thm 14** statement recovery | `r0030-plan-from-orchestrator-to-agent5-statement-recovery.md` |

Wave A needs no ordering between streams. Agents 1 and 2 depend on r0029 landing
first; agents 3, 4 and 5 do not depend on anything in flight.

## Wave B — two agents, not four

An earlier draft of this plan put Lemmas 24 and Theorems 25, 26, 27, 29 in one
four-agent wave. That was wrong: they are **not** independent. Theorem 25 consumes
Lemma 24; Theorems 26 and 27 both consume Theorem 25. Assigning them to four
concurrent agents would have had three of them blocked on a sibling's unfinished
work — the failure mode this project avoids by partitioning on the dependency
graph, not on the section number.

The genuine partition:

| # | Agent | Work | Depends on |
| -- | ----- | ---- | ---------- |
| 1 | agent1 | **Lemma 24** then **Theorem 25** — one chain, one agent | Lem 28's `×` conjunct from wave A |
| 2 | agent2 | **Theorem 29** — `D` bifinite ⟹ `D+` bifinite, and `D ≅ D+` | Thm 21 only, which is proved |

Theorem 29 can in fact start immediately — Theorem 21 landed in r0029 — so it may
be pulled into wave A as a sixth stream if the collision and review limits below
allow. Everything else in §7 waits for Theorem 25.

## Wave B2 — two agents, after Theorem 25

| # | Agent | Work |
| -- | ----- | ---- |
| 1 | agent1 | **Theorem 26** — combinators solving a signature's equations |
| 2 | agent2 | **Theorem 27** — every bounded-complete `D` a projection of `U` |

## Wave D — three agents, after wave A's recovery

Whatever agent5 recovers in wave A becomes one stream each for **Lemma 9**,
**Theorem 12** and **Theorem 14**. If a statement cannot be recovered with
evidence, it stays unstated and is reported as such — the inventory already
records seven results that were once "not yet statable", and the count going down
honestly is the metric, not the count going up.

## How many agents, and why

Measured in `docs/Performance.md`, not guessed:

| # | Constraint | Binds at |
| -- | ---------- | -------- |
| 1 | CPU, average — 0.25 cores per agent against the 12-core budget | ~48 agents |
| 2 | CPU, bursts — a 9% duty cycle puts ~4 builds in flight, the 12-core ceiling | ~8 agents |
| 3 | Memory — 2.3 GiB PSS per concurrent build | ~5 concurrent builds |
| 4 | **Declaration collisions** — 2 clashes among 5 agents in r0028, pairs grow as N(N−1)/2 | **~6 agents** |
| 5 | Orchestrator review — r0028 was ~3,800 lines of Lean to read, merge and audit | ~5 agents |

**Five agents per wave.** Constraint 4 is the binding one, and it is mitigated,
not eliminated, by the namespace rule below: r0029 gives every agent its own
namespace so two agents cannot mint the same fully-qualified name.

## Where the work is specified

An agent's instructions live in **its own plan**, `to-agentN`, and each is
self-contained: the statements, the files it owns, its authorized exceptions, the
obstacles to expect, the standing rules, and what its report must contain. An
agent reads its own plan and needs no other file to work.

Prompts are the user↔assistant conversation. They are not a carrier of task
specification: a prompt is not archived under `plans/`, so anything stated only
in a prompt leaves no artifact and cannot be paired with a report. Round r0028
made that mistake — the per-agent specifics existed only in launch prompts.

Each agent writes **its own report**, `reports/r0030-report-from-agentN-to-orchestrator-<subject>.md`,
pairing with its own plan by round and recipient per GRASE rule 7.6.

## Acceptance criteria

| # | Criterion | Measurement |
| -- | --------- | ----------- |
| 1 | Build | `Build completed successfully`, 0 errors, 0 warnings beyond declared `sorry`s |
| 2 | Numbered results | **16 after r0029 merges** (Thm 21) → 21 after wave A (Lem 13, Lem 28, Lem 30, Thm 16, Thm 18, less any that report an obstacle) |
| 3 | — after waves B and B2 | → 25 (Lem 24, Thm 25, Thm 26, Thm 27, Thm 29) |
| 4 | — after wave D | → 28 of 29, leaving only what cannot be recovered from the PDF |
| 5 | Axioms | every new result depends only on `propext`, `Classical.choice`, `Quot.sound` |
| 6 | **Composition** | every new module imports together in one file — the check that would have caught r0028's clash, and which a green `lake build` does not perform |
