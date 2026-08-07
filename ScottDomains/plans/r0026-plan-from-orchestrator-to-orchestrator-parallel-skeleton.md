---
round: r0026
from: orchestrator
to: orchestrator
subject: parallel-skeleton
date: 2026-0806-16:45
status: active
related:
  - reports/r0025-report-from-orchestrator-to-user-smash-bifinite.md
---

# r0026 — Finish the definitions, skeleton the remaining results, go three-fold parallel

The user's plan: land the remaining definitions, state every outstanding numbered
result as a theorem with a `sorry` body, then split the proving across three
agent worktrees.

## Why the skeleton comes before the split

Three reasons, in order of weight:

1. **The statements are where the risk is, not the proofs.** Lemma 9's text in
   the source PDF drops every `⊗` and every `⊥` subscript — part 5 reads
   `D (E × F) ≅ (D E) × (D E)`. Reconstructing those statements is a judgement
   call that must be made once, centrally, and reviewed, not made three times in
   parallel by agents who cannot see each other's readings.
2. **Fixed signatures mean no conflicts.** Agents fill in `sorry` bodies; nobody
   edits a declaration another agent depends on.
3. **`sorry` count becomes the burn-down metric.** It goes 22 → 0 and is
   measurable every round, replacing "how far along are we" with a number.

The cost is that the development carries `sorry`s for the first time in 25
rounds. That is a deliberate, temporary exception and the count is tracked in
`docs/PaperInventory.md` so it is never ambiguous.

## Phase 1 — the remaining definitions

| # | Definition | Status | Notes |
| -- | ---------- | ------ | ----- |
| 1 | sum `D + E` | this round | the paper's **coalesced** sum: `(D∖{⊥}) × {0} ∪ (E∖{⊥}) × {1} ∪ {⊥}`. Same `WithBot`-over-a-subtype shape as the smash product, over `Sum` instead of `Prod` |
| 2 | `D∞` | own round | inverse limit of a chain of embedding–projection pairs. The largest single construction left |
| 3 | the three powerdomains | blocked | need the ideal completion (Theorem 11), which is itself one of the results to prove |

## Phase 2 — the skeleton, and what it can honestly cover

A statement can only be written if its vocabulary exists. Auditing the 22
outstanding results against what is defined:

| # | Result | Statable now? | Blocked on |
| -- | ------ | ------------- | ---------- |
| 1 | Lem 9 | after phase 1.1 | sum |
| 2 | Lem 10 | after phase 1.1 | sum |
| 3 | Thm 11 (ideal completion) | **yes** — `Order.Ideal` is in Mathlib | — |
| 4 | Thm 12 (initiality of a continuous algebra) | no | "continuous algebra satisfying axioms `T`" is undefined |
| 5 | Lem 13 | no | powerdomains |
| 6 | Thm 14 (equivalent characterizations) | **yes** | — |
| 7 | Prop 15 (bounded complete ⟹ bifinite) | **yes** | — |
| 8 | Thm 16 (`Fp(D)` an algebraic lattice) | partly | `Fp(D)` needs a poset structure |
| 9 | Lem 17 | after phase 1.1 | sum |
| 10 | Thm 18 | **yes** | — |
| 11 | Lem 19 (closures) | **yes** | — |
| 12 | Lem 20 (`Fc(D)`) | partly | `Fc(D)` needs defining |
| 13 | Thm 21–Lem 30 (§7) | no | `D∞`, representability |

So the skeleton is **not** 22 statements. It is roughly 6 now, ~9 after the sum,
and the §7 block only after `D∞`. Claiming a 22-statement skeleton would be
claiming vocabulary that does not exist.

## Phase 3 — the worktrees

`agent1` exists and builds (957 jobs). Recipe, now verified:

```
git worktree add ~/projects/ScottLean4-agentN -b agentN
mkdir -p ~/projects/ScottLean4-agentN/ScottDomains/.lake
ln -s ~/projects/ScottLean4/ScottDomains/.lake/packages \
      ~/projects/ScottLean4-agentN/ScottDomains/.lake/packages
```

Measured cost: **323 MiB working tree + 15 MiB own build per agent**; the shared
`.lake/packages` (7.4 GiB) is not written to during a build, confirmed by
`find -newer`. Three agents ≈ 1 GiB against 34 GiB free.

## Phase 4 — the partition

| # | Agent | Scope | Prerequisites |
| -- | ----- | ----- | ------------- |
| 1 | agent1 | §4.5 — Lemmas 9, 10, 13; Theorems 11, 12, 14 | sum; Thm 11 unblocks the powerdomains |
| 2 | agent2 | §6 — Proposition 15; Theorems 16, 18; Lemmas 17, 19, 20 | all present |
| 3 | agent3 | §7 — Theorems 21, 22, 25, 26, 27, 29; Lemmas 23, 24, 28, 30 | `D∞`, hence last to start |

## Acceptance criteria

| # | Criterion | Measurement |
| -- | --------- | ----------- |
| 1 | Sum defined and building | 0 errors, 0 warnings |
| 2 | Skeleton statements checked against the paper's text | each carries the quoted source line in its docstring |
| 3 | `sorry` count reported | in `docs/PaperInventory.md`, every round |
| 4 | Worktrees build | 957 jobs each, shared packages unwritten |
| 5 | No statement invented | anything the PDF garbles beyond reconstruction is recorded as unstatable, not guessed |
