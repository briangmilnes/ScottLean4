---
round: r0028
from: orchestrator
to: orchestrator
subject: five-fold-parallel
date: 2026-0806-18:45
status: pending
related:
  - plans/r0027-plan-from-orchestrator-to-orchestrator-session-restart.md
  - reports/r0027-report-from-orchestrator-to-user-parallel-proving.md
---

# r0028 — Five-fold parallelism to all definitions and the §4–§7 results

Target state: **every definition the paper defines** and as many of the 20
outstanding numbered results as the dependency structure admits, run at
**5 agents wide**.

## State this plan starts from

| # | Quantity | Value |
| -- | -------- | ----- |
| 1 | Build | `Build completed successfully (962 jobs).`, 0 errors |
| 2 | `sorry` | **1** — `thm18` |
| 3 | Numbered results complete | **9 of 29**; Lem 10 partial (5 of 6 conjuncts), Lem 17 partial (3 of 5) |
| 4 | Definitions | 10 of ≈13 — remaining: **sum `D + E`**, **the three powerdomains**, **`D∞` / universal domain** |
| 5 | Modules / lines / theorems | 27 / 4440 / 199 |

## Why the streams are cut this way

Two constraints set the partition. **File ownership:** no two agents may edit one
file, so each stream owns new modules and its own skeleton file. **Dependency:**
three results are prerequisites for whole sections, so they go first and alone —
Theorem 11 (ideal completion) unblocks all of §5, and Theorems 22 and Lemma 23
unblock §7's universal domain, which is how the paper builds recursive domains
(by representability over a universal domain, not by an inverse limit).

Everything else in §4–§6 is independent of both, which is what makes five
concurrent streams honest rather than three streams and two agents blocked.

## Wave 1 — five streams, no ordering between them

| # | Agent | Owns | Work |
| -- | ----- | ---- | ---- |
| 1 | agent1 | `CoalescedSum.lean` (finish), `Skeleton/Sum.lean` | Give `D + E` its `sSup` and `CompletePartialOrder` instance, **branching on landing in `NonBotSum`, never on directedness** (see below). Then state and prove `lem10_sum` and `lem17_sum`, and `lem17_smash`, which r0026 simply omitted. Completes Lemmas 10 and 17 against the paper's full operator list |
| 2 | agent2 | `IdealCompletion.lean` | **Theorem 11** — the ideal completion of a countable pre-order is a domain, and every domain arises as one. Mathlib's `Order.Ideal` is the starting point. This is the single highest-value item: §5 cannot start without it |
| 3 | agent3 | `FinitaryProjectionPoset.lean`, `Skeleton/Section6b.lean` | **Theorem 16** (`D` bifinite ⟹ `Fp(D)` is an algebraic lattice) and **Lemma 20** (`D` a domain ⟹ `Fc(D)`, the finitary closures, is a cpo). One agent owns both because both first need `Fp(D)` / `Fc(D)` as posets — the missing construction the r0027 notes recorded as the blocker. `IsClosure` (r0027, `Section6.lean`) is the closure half and is read-only for this agent |
| 4 | agent4 | `MinimalUpperBounds.lean`, and `thm18` in `Skeleton/Section6.lean` | **Theorem 18**, the one open `sorry`. Requires a new development first: minimal upper bounds, complete sets of them, the operator `U` and its iterate `U^∞` — r0027 measured **0** occurrences of that vocabulary in `ScottDomains/`. Then Smyth's three Figure-3 cases; case (c) needs König's lemma against `Domain.countable_compacts`. Exception to file ownership: this agent alone may edit `thm18`'s body, no other declaration in that file |
| 5 | agent5 | `UniversalDomain.lean` | **Theorem 22** (every countably-based algebraic lattice is the image of a closure `r : P(ℕ) → L`) and **Lemma 23** (the function-space operator is representable over `P(ℕ)`). `Powerset.lean` supplies `P(ℕ)`; `IsClosure` and `lem19` supply the closure machinery. Opens §7 |

`Skeleton/` keeps the r0026 convention that made r0027 merge without a single
conflict: one file per agent, statements fixed before proving.

## Wave 2 — unblocked by wave 1, same five-wide shape

| # | Depends on | Work |
| -- | ---------- | ---- |
| 1 | Thm 11 (agent2) | **Define the three powerdomains** — Hoare, Smyth, Plotkin. Independent of each other once the ideal completion exists, so three agents wide by themselves |
| 2 | the powerdomains | **Lemma 13** (bounded completeness of `D]`, `D[`), **Lemma 28**, **Lemma 30** |
| 3 | Thm 22, Lem 23 (agent5) | **`D∞` / the universal domain** as a definition, then **Theorems 21, 24, 25, 26, 27, 29** |
| 4 | — | **Lemma 9** and **Theorem 14**, both held back deliberately: the 1990 Type-3 fonts drop every `⊗` and `⊥` from Lemma 9 and garble Theorem 14's characterizations. These are statement-recovery tasks against the PDF before they are proof tasks, and a guessed statement is worse than none |
| 5 | — | **Theorem 12** — `continuous algebra satisfying axioms T` is undefined in the paper as printed; same recovery problem |

## The defect that must not recur a third time

`ScottHom`'s `sSup`, then `Smash`'s `smashSup`, each branched their `dite` on a
merely *sufficient* condition (directedness) rather than on the condition under
which the value is an element of the type. Both made a `BoundedComplete`
statement **false**, and r0027 cost an agent most of a run proving the second one
false before repairing it. `CoalescedSum`'s `sSup` is the third instance waiting
to happen. Agent1's instruction states the rule directly: branch on landing in
`NonBotSum`.

The general form, worth stating once in a module docstring: a total `SupSet` on a
subtype-with-adjoined-bottom must branch on **membership of the candidate value in
the subtype**, because that is exactly the proposition the constructor needs.

## Worktrees

Agents 4 and 5 have no worktree yet. For each of `agent4`, `agent5`:

1. `git worktree add ~/projects/ScottLean4-agentN -b agentN`
2. symlink `.lake/packages` at the main checkout's — measured safe, and 970 MiB
   for three worktrees against 22 GiB if each vendored Mathlib
3. copy `.claude/settings.local.json` in
4. add `~/projects/ScottLean4-agentN` to `permissions.additionalDirectories`
   **and restart the session** — that setting is read at session start, which is
   the failure that forced the r0027 restart

## Standing rules for every agent prompt

1. Work only in its own worktree; never touch `~/projects/ScottLean4` or a sibling.
2. Bare `lake build` — no `timeout` prefix (it is not allowlisted and prompts the
   user on every build); raise the Bash tool's own timeout instead.
3. Errors **and** warnings to zero; no `set_option` to silence a linter.
4. Edit/Write only — never `sed -i`, heredocs, or shell redirection into a file.
5. Helper lemmas in its own file; to change a shared module, stop and report —
   except where this plan names the exception explicitly (agent1 on
   `CoalescedSum.lean`, agent4 on `thm18`).
6. Never weaken or delete a statement to make it provable. If it is false as
   stated, prove it false and report — that is what turned r0027's `lem10_smash`
   from a stuck goal into a shared-module repair.
7. Commit with `scripts/gitcp.sh`; **do not push**, do not set an upstream. The
   orchestrator reviews the diff, merges, re-runs `lake build`, and pushes.
8. Report: statements proved, `#print axioms` for each (no `sorryAx`), exact
   remaining `sorry` count, the verbatim final build line, and the specific
   obstacle for anything unproved.

## Acceptance criteria for r0028

| # | Criterion | Measurement |
| -- | --------- | ----------- |
| 1 | Build | `Build completed successfully` with 0 errors, 0 warnings other than declared `sorry`s |
| 2 | Definitions | 11 of ≈13 after wave 1 (sum done); 13 of ≈13 after wave 2 |
| 3 | Numbered results | 9 → **13** after wave 1 (Lem 10, Lem 17 completed; Thm 11, Thm 16, Lem 20, Thm 22, Lem 23 landed, less any that report an obstacle) |
| 4 | `sorry` | 1 → 0 if agent4 lands Theorem 18; otherwise 1, with the obstacle recorded |
| 5 | Axioms | every new result depends only on `propext`, `Classical.choice`, `Quot.sound` |
