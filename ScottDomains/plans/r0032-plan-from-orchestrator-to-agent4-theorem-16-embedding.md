---
round: r0032
from: orchestrator
to: agent4
subject: theorem-16-embedding
date: 2026-0806-20:30
status: pending
related:
  - plans/r0032-plan-from-orchestrator-to-orchestrator-remaining-twelve.md
  - reports/r0028-report-from-agent3-to-orchestrator-fp-fc-posets.md
---

# r0032 agent4 — Theorem 16's embedding conjunct

## Goal

> **Theorem 16** (Gunter & Scott, §6.1) If `D` is bifinite then `Fp(D)` is an
> algebraic lattice, **and the inclusion `i : Fp(D) ↪ (D → D)` is an embedding**.

The first conjunct is **proved** — `ScottDomains.thm16` (r0028,
`Skeleton/Section6b.lean`) exhibits the `CompleteLattice` on `Fp α` with its order
pinned to the pointwise one and `IsCompactlyGenerated`. The second conjunct was
not stated, and this plan is that conjunct.

## Worktree and ownership

Work only in `/home/milnes/projects/ScottLean4-agent4`, branch `agent4`. Never
touch `/home/milnes/projects/ScottLean4` or a sibling worktree.

You own exactly one new file:
`ScottDomains/ScottDomains/FinitaryProjectionEmbedding.lean`. Everything else is
read-only — in particular `Skeleton/Section6b.lean` and
`FinitaryProjectionPoset.lean`, which carry `thm16`, `Fp`, `Fc` and their API. If
a shared module genuinely must change, stop and report rather than change it.

**Every declaration you write goes in `namespace ScottDomains.FpEmbedding`.** In
r0028 two agents each defined `isClosure_sSup` and
`IsClosure.apply_sSup_of_directed`; `lake build` passed at 971 jobs because no
module imported both, and the clash surfaced only when an axiom audit finally
imported the pair.

## What to read first

| # | File | Why |
| -- | ---- | --- |
| 1 | `ScottDomains/FinitaryProjectionPoset.lean` | `Fp α`, `Fc α`, the pointwise order (`Fp.le_def`, `Iff.rfl`), `Fp.completeLattice`, `Fp.isCompactlyGenerated`, `isNormalIn_sInter`, `IsPlotkinOrder.exists_isMinimalUpperBound` |
| 2 | `ScottDomains/Skeleton/Section6b.lean` | `thm16` as it stands, and its docstring, which records the obstacle below |
| 3 | `ScottDomains/Theorem6.lean` | Theorem 6 — normal substructures `≅` finitary projections; the handle on `Fp(D)` |
| 4 | `ScottDomains/NormalProjection.lean` | `p_N`, `normalHom`, `isProjection_normalHom` |
| 5 | `ScottDomains/MinimalUpperBounds.lean` | minimal upper bounds and `U^∞`, r0028; the vocabulary the obstacle is stated in |
| 6 | `papers/Gunter Scott 1990.pdf`, §6.1 | the statement and the paper's sketch |

## The obstacle — this is the whole task

r0028's agent3 documented precisely why the paper's sketch does not go through as
printed, and did not guess a repair:

> The paper's sketch takes `S_f = {x ∈ K(D) | x ⊑ f(x)}`, but `S_f` is **not
> normal**, so the least normal `N_f ⊇ S_f` is strictly larger. A minimal upper
> bound `m` of `a, b ∈ S_f` must lie in `N_f`, yet `f(m)` is only *an* upper bound
> of `{a, b}` and need not dominate the minimal one. So `m ⊑ f(m)` can fail, and
> with it the projection half `p_{N_f} ⊑ f`.

Three outcomes are acceptable, in this order of preference:

1. **Repair the sketch.** Find the construction that does work — perhaps
   `N_f` built by iterating `mubStep` and intersecting with `S_f`'s downward
   closure, perhaps a different `S_f` — and prove the embedding conjunct.
2. **Refute the sketch specifically.** Exhibit a bifinite `D` and `f` for which
   `p_{N_f} ⊑ f` fails, proving the paper's *route* wrong while leaving the
   theorem open. State clearly that this refutes the argument, not the theorem.
3. **Refute the conjunct.** If the embedding claim is itself false as the paper
   states it, prove that. A kernel-checked refutation is a first-class result —
   r0027's `lem10_smash` refutation is the precedent, and it turned a stuck goal
   into a shared-module repair.

Say which of the three you achieved. Do not report a partial repair as a proof.

## What "embedding" must mean

State it precisely before proving anything. In this development the candidate is
`ScottHom.IsEmbeddingProjectionPair` (r0012) — an embedding–projection pair — and
the paper's `i : Fp(D) ↪ (D → D)` should be read against it. If you formalize
"embedding" differently, say why in a docstring and give the definition you used.
An order-embedding and an embedding–projection pair are not the same claim.

## Rules

1. Build with `scripts/compile.sh` from the worktree root — it logs timing and
   peak memory. Never prefix a build with the `timeout` command; raise your Bash
   tool's own timeout parameter instead.
2. Drive errors **and** warnings to zero. No `set_option` to silence a linter.
3. Edit/Write only — never `sed -i`, heredocs, or shell redirection into a file.
4. Never weaken the statement to make it provable. Restating the conjunct with an
   extra hypothesis is weakening unless the paper states that hypothesis.
5. Commit with `scripts/gitcp.sh` on branch `agent4`. **Do not push and do not set
   an upstream**; its push step failing with "no tracking information" is
   expected. The orchestrator reviews, merges and pushes.

## Report

Write `reports/r0032-report-from-agent4-to-orchestrator-theorem-16-embedding.md`
containing: which of the three outcomes you reached; the definition of "embedding"
you used and why; the exact statements proved, kernel-accepted, with
`#print axioms` showing no `sorryAx`; if you refuted, the witness and what exactly
it refutes; the exact remaining `sorry` count; the verbatim final `lake build`
line; your commit SHAs; and the specific obstacle for anything unproved.
