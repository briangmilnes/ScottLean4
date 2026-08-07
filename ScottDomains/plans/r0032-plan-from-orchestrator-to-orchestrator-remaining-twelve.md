---
round: r0032
from: orchestrator
to: orchestrator
subject: remaining-twelve
date: 2026-0806-20:30
status: pending
related:
  - plans/r0030-plan-from-orchestrator-to-orchestrator-remaining-theorems.md
  - reports/r0031-report-from-agent2-to-orchestrator-lemma-13.md
  - reports/r0031-report-from-agent4-to-orchestrator-lemmas-28-30.md
---

# r0032 — The remaining 12 numbered results

**17 of 29 proved.** This is the coordination record; each agent's work is
specified in full in its own `to-agentN` plan, which is self-contained and
authoritative. Prompts carry nothing.

## What remains, and what actually blocks each

| # | Result | Blocked on | Changed by r0031? |
| -- | ------ | ---------- | ----------------- |
| 1 | Lem 9 | statement recovery — the PDF drops every `⊗` and `⊥` | no |
| 2 | Thm 12 | **nothing** — the `T` axioms were recovered | **yes: was "not statable"** |
| 3 | Thm 14 | statement recovery — the characterizations are garbled | no |
| 4 | Thm 16 (embedding conjunct) | a documented gap in the paper's `S_f` sketch | no |
| 5 | Thm 18 | **in flight** (r0031 agent3) — the development's only `sorry` | pending |
| 6 | Lem 24 | **nothing** — `isRepresentable_prod` landed | **yes: unblocked** |
| 7 | Thm 25 | Lem 24 | via Lem 24 |
| 8 | Thm 26 | Thm 25 | via Lem 24 |
| 9 | Thm 27 | Thm 25 | via Lem 24 |
| 10 | Lem 28 | §7.3's universal domain `U` (dyadic half-open intervals) **and** p-representability over `Fp(U)` — neither exists here | **yes: was thought to be about `P N`** |
| 11 | Thm 29 | bifinite machinery; the paper defers the full proof to [Gun87] | no |
| 12 | Lem 30 | §7.4's bifinite universal domain `V`, plus p-representability | **yes: same correction** |

Two corrections from r0031 drive this plan. Lemmas 28 and 30 are **not** about
`P N` and **not** about `Fc(U)`: both are stated for *p-representability* over
`Fp(U)` — finitary **projections** — over universal domains the development has
not built. They are therefore the deepest items here, not the shallow ones the
r0030 plan assumed. And Theorem 12 moved the other way: its axioms extract
cleanly, so it is ready to prove.

## A defect that outranks the theorem work

`IdealCompletion.idealSup` branches on the union being an ideal, which is the
membership condition for the *union* rather than for the least upper bound of a
**bounded** family. r0031 proved `BoundedComplete` false for all three
powerdomains as a consequence. This is the third instance of one defect class —
`ScottHom` (r0006–r0011), `Smash` (r0027), `IdealCompletion` (r0031) — and until
it is repaired no bounded-completeness instance can be claimed for any ideal
completion, which includes every powerdomain. It gets an agent of its own in
wave 1, ahead of new results.

## Wave 1 — five agents, no ordering between them

| # | Agent | Work | Its plan |
| -- | ----- | ---- | -------- |
| 1 | agent1 | **Lemma 24** then **Theorem 25** — one chain, one agent | `…-to-agent1-lemma-24-theorem-25.md` |
| 2 | agent2 | **`idealSup` repair**, then reinstate the powerdomain bounded-completeness instances | `…-to-agent2-idealsup-repair.md` |
| 3 | agent3 | **Theorem 12** — initiality of a continuous algebra satisfying `T` | `…-to-agent3-theorem-12.md` |
| 4 | agent4 | **Theorem 16**'s embedding conjunct — repair, or refute the sketch, or refute the conjunct | `…-to-agent4-theorem-16-embedding.md` |
| 5 | agent5 | **Lemma 9** and **Theorem 14** statement recovery — no proofs | `…-to-agent5-statement-recovery.md` |

Five is the measured ceiling (`docs/Performance.md`): declaration collisions bind
at about six agents and orchestrator review at about five, while CPU and memory do
not bind until far more. Namespace-per-agent, adopted in r0029, has held at zero
collisions across two rounds and is mandatory in every plan.

## Wave 2 — after Theorem 25

| # | Agent | Work |
| -- | ----- | ---- |
| 1 | agent1 | **Theorem 26** — combinators solving a signature's equations |
| 2 | agent2 | **Theorem 27** — every bounded-complete `D` a projection of `U` |
| 3 | agent3 | **Theorem 29** — `D` bifinite ⟹ `D+` bifinite, and `D ≅ D+`. Read [Gun87]'s status first: the paper defers the full proof, so establish what it actually asserts before proving |

## Wave 3 — the two universal domains, then Lemmas 28 and 30

Lemmas 28 and 30 need constructions that do not exist yet, so wave 3 builds them:

| # | Agent | Work |
| -- | ----- | ---- |
| 1 | agent1 | §7.3's universal domain `U` — the ideal completion of the dyadic half-open intervals |
| 2 | agent2 | **p-representability** over `Fp(U)`, the notion §7.3 defines afresh, distinct from `IsRepresentable` over `Fc(U)` |
| 3 | agent3 | §7.4's bifinite universal domain `V` (Theorem 29's setting) |
| 4 | agent4 | **Lemma 28** over `U`, then **Lemma 30** over `V` |

## Acceptance criteria

| # | Criterion | Measurement |
| -- | --------- | ----------- |
| 1 | Build | `Build completed successfully`, 0 errors, 0 warnings beyond declared `sorry`s |
| 2 | Numbered results | 17 → **21** after wave 1 (Lem 24, Thm 25, Thm 12, Thm 16, plus Thm 18 if r0031 lands it) |
| 3 | — after wave 2 | → **24** (Thm 26, Thm 27, Thm 29) |
| 4 | — after wave 3 | → **26** (Lem 28, Lem 30), leaving Lem 9 and Thm 14 pending recovery |
| 5 | Axioms | every new result depends only on `propext`, `Classical.choice`, `Quot.sound` |
| 6 | Composition | every new module imports together in one file — the check a green `lake build` does not perform |
| 7 | Bounded completeness | after agent2's repair, the powerdomain instances hold and `not_boundedComplete_*` are retired |

## Process corrections carried into this round

1. **Verify worktree sync before launching, do not assert it.** Both r0031
   agent2 and agent4 reported their worktree was behind `main` while their plan
   said it was synced; each fast-forwarded itself. Sync and check, then launch.
2. **Do not tell an agent a guard is correct.** The r0031 plan asserted
   `idealSup`'s guard was the membership condition; it was not, and the agent had
   to discover that against the plan's claim. State what is known and let the
   agent measure.
3. **Read the PDF before describing a result in a plan.** The r0031 descriptions
   of Lemmas 28 and 30 were wrong in three ways at once.
