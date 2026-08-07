---
round: r0027
from: orchestrator
to: orchestrator
subject: session-restart
date: 2026-0806-18:05
status: pending
related:
  - plans/r0026-plan-from-orchestrator-to-orchestrator-parallel-skeleton.md
  - reports/r0025-report-from-orchestrator-to-user-smash-bifinite.md
---

# r0027 — Session restart: relaunch the three agents

State handoff so a fresh session resumes without re-deriving anything. The
restart exists for exactly one reason, recorded below so it is not repeated.

## Why the restart

Claude Code reads `permissions.additionalDirectories` **at session start**. It
was added mid-session, so it was never live: every Edit/Write the three agents
attempted inside `~/projects/ScottLean4-agent{1,2,3}` counted as a write outside
the project root and prompted the user. Three agents were launched on the
assumption the setting had taken effect; all three were stopped while still
reading files. Nothing was written, no branch was touched.

The settings are now correct **on disk** in both
`.claude/settings.json` (tracked) and `.claude/settings.local.json` (untracked,
machine-local), and `settings.local.json` has been copied into all three
worktrees. A fresh session picks them up at startup.

**Lesson for the new session:** verify a permission setting is live before
building work on top of it — launch one agent and let it write one file first.

## State at restart

Everything committed and pushed; all four working trees clean.

| # | Tree | Branch | Head | Build |
| -- | ---- | ------ | ---- | ----- |
| 1 | `~/projects/ScottLean4` | `main` | `e1e3deb` | 962 jobs, 0 errors |
| 2 | `~/projects/ScottLean4-agent1` | `agent1` | synced to main | 962 jobs |
| 3 | `~/projects/ScottLean4-agent2` | `agent2` | synced to main | 962 jobs |
| 4 | `~/projects/ScottLean4-agent3` | `agent3` | synced to main | 962 jobs |

Each worktree symlinks `.lake/packages` at the main checkout's — measured safe
(`find -newer` shows no writes into it during a build) and cheap: **970 MiB for
all three**, versus 22 GiB if each vendored its own Mathlib.

## Formalization progress

| # | Quantity | Count |
| -- | -------- | ----- |
| 1 | Numbered results proved | **7 of 29** — Thms 1, 3, 6, 7; Lems 4, 5, 8 |
| 2 | Unnumbered prose claims proved | 12 |
| 3 | Definitions | **11 of ≈13** (remaining: powerdomains, `D∞`) |
| 4 | Open `sorry`s | **10**, all in `ScottDomains/Skeleton/` |
| 5 | Modules / lines / theorems | 26 / ~3600 / 155 |

§2 and §3 are complete. §4 has Lemma 8 complete plus product, smash, lift,
coalesced sum, strict function space and currying.

## Resume steps

1. `cd ~/projects/ScottLean4 && git pull --rebase` — this repo is written from two
   machines.
2. `cd ScottDomains && lake build` — expect `Build completed successfully (962 jobs)`
   with 10 `sorry` warnings and nothing else.
3. **Verify the permission fix before relying on it.** Launch **one** agent
   (agent1) and confirm it can Edit a file in its worktree without prompting the
   user. Only then launch the other two. This is the check that was skipped.
4. Relaunch the three agents with the assignments below.

## Agent assignments

Each owns exactly one file; no two agents touch the same declaration, so their
branches merge without conflict.

| # | Agent | Worktree | File it owns | Statements |
| -- | ----- | -------- | ------------ | ---------- |
| 1 | agent1 | `~/projects/ScottLean4-agent1` | `ScottDomains/Skeleton/Lemma10.lean` | `lem10_prod`, `lem10_smash`, `lem10_lift`, `lem10_strict` — Lemma 10, bounded completeness closed under the operators |
| 2 | agent2 | `~/projects/ScottLean4-agent2` | `ScottDomains/Skeleton/Section6.lean` | `prop15`, `thm18`, `lem19` — §6 core |
| 3 | agent3 | `~/projects/ScottLean4-agent3` | `ScottDomains/Skeleton/Lemma17.lean` | `lem17_prod`, `lem17_lift`, `lem17_fun` — Lemma 17, bifiniteness closed under the operators |

Prompt requirements for each agent (all were in the stopped launches and should
be kept):

* work only in its own worktree; never touch `~/projects/ScottLean4` or a sibling;
* build with `lake build`, drive errors **and warnings** to zero, no `set_option`
  to silence linters;
* edit only with Edit/Write — never `sed -i`, heredocs or shell redirection;
* helper lemmas go in its own file; if a shared module genuinely needs changing,
  stop and report rather than change it;
* never weaken or delete a statement to make it provable — report the obstacle
  and leave the `sorry`;
* commit with `scripts/gitcp.sh` on its own branch;
* report which statements were proved, the exact remaining `sorry` count, the
  final build line, and the specific obstacle for anything unproved.

## Merging back

`main` takes each agent branch when its file builds clean. Because the skeleton
was split one file per agent, merges are independent and order does not matter.
Re-run `lake build` on `main` after each merge and update the `sorry` count in
`docs/PaperInventory.md` — it is the burn-down metric, currently 10.

## Open decisions

| # | Decision | Context |
| -- | -------- | ------- |
| 1 | Whether `D∞` waits on §6 | Reading §7 showed the paper builds recursive domains by *representability over a universal domain*, not by an inverse limit; Lemma 23 runs through `Fc(P N)`, and `Fc(D)` is Lemma 20 — inside agent2's §6 block. So `D∞` is downstream of §6, not a prerequisite for it |
| 2 | Seven results are not yet statable | Lem 9 (PDF drops every `⊗` and `⊥`), Thm 11 (needs the ideal completion as a construction), Thm 12 (`continuous algebra satisfying axioms T` undefined), Lem 13 (powerdomains), Thm 14 (characterizations garbled), Thm 16 and Lem 20 (`Fp(D)`/`Fc(D)` as posets). Each is recorded with its blocker; none should be guessed |
| 3 | The 6 commented-out theorems | `Domain.lean`, `ScottHom.lean`, `StepFunction.lean`, `Projection.lean` carry six unused theorems commented out in place at the user's request, each with a note on why it exists. Leave them |
