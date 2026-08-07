---
round: r0034
from: orchestrator
to: agent6
subject: theorem-18-theorem-16
date: 2026-0806-22:35
status: pending
related:
  - plans/r0034-plan-from-orchestrator-to-orchestrator-six-way-remaining.md
  - plans/r0031-plan-from-orchestrator-to-agent3-theorem-18.md
  - reports/r0031-report-from-agent3-to-orchestrator-theorem-18.md
---

# r0034 agent6 — Theorem 18, and Theorem 16's positive form

Namespace: **`ScottDomains.Section62`**. Your worktree was created for this round
(`scripts/init-worktree.sh 6`); it is at `main` with the packages symlink in
place, so `lake build` reuses the built Mathlib rather than rebuilding ~7 GiB.

## Part 1 — Theorem 18

`D` and `D → D` domains ⟹ `D` bifinite. **The development's oldest `sorry`, open
since r0027 and failed in three rounds.** Read this section fully before writing
any Lean.

What is established:

| # | Fact | Source |
| -- | ---- | ------ |
| 1 | The paper gives **no proof**, citing Smyth [Smy83a] | §6.2 |
| 2 | `isBifinite_iff_mubClosure` reduces it to two obligations | r0028 |
| 3 | `ContinuousConstruction.lean` supplies a constructor needing neither bounded completeness nor algebraicity, reducing cases (a) and (b) to one finiteness statement | r0031 |
| 4 | That finiteness statement is **equivalent** to Theorem 18 — not a lemma below it | r0031 audit |
| 5 | The perturbation route fails on one monotonicity side condition; **three variants fail at the same point** | r0030–r0031 |

Row 4 is why this has not fallen: the reduction is not a weakening, so grinding on
it is circular. Row 5 is why repeating the perturbation argument is not worth
wall time.

**Your instruction is therefore different from every prior round: read [Smy83a]
directly.** The proof exists in the literature; the development has been trying to
re-derive it. Do not generate a fourth variant of the perturbation argument.

If the case analysis is not recoverable from the source, **a precise obstruction
is the deliverable**: name which side condition fails, at which step, why the
r0031 reduction is circular rather than progress, and what a proof would need that
the development does not have. Write it in the module docstring and the report.
That is a result — it tells the next round whether to spend on this at all.

## Part 2 — Theorem 16's positive form

Small, complementary, and currently **unstated**.

r0032 refuted Theorem 16's `Fp(D) ↪ (D → D)` embedding conjunct under the kernel
(`FinitaryProjectionEmbedding.lean`), with the paper's sketch error identified.
The other half — `D` bifinite ⟹ `Fp(D)` is an algebraic lattice — is proved as
`ScottDomains.thm16` (r0028).

The refuted conjunct **does hold** under a hypothesis: when every `S_f` has a
greatest normal subposet, a condition bounded complete domains satisfy. State it
and prove it as `thm16_positive`, and cross-reference the refutation so the pair
reads as one settled result rather than two loose ends.

Do not restate the refutation or re-derive it — it is kernel-checked already.

## Acceptance criteria

1. `thm16_positive` stated and proved, cross-referencing
   `FinitaryProjectionEmbedding.lean`.
2. **Either** `thm18` proved — taking the development to **0 `sorry`** — **or** a
   written obstruction in the module docstring and the report, with the failing
   step named. Do not add `sorry`s beyond the one already there.
3. `scripts/compile.sh -r r0034` reports 0 errors and 0 warnings beyond `sorry`.
4. Report which of [Smy83a]'s steps you could and could not recover, whichever
   way Part 1 goes.

## Process rules

1. **Namespace `ScottDomains.Section62`** for every new declaration. Six agents
   run this round; the collision limit binds at ~6 and the namespace rule is what
   has kept collisions at zero since r0029.
2. **Edit/Write only — never heredocs.**
3. **One command per Bash call. Never chain, never `cd`.**
4. Multi-step work becomes a script in `scripts/` — standing-authorized.
5. **Read the PDF, not the paraphrase** — and for Part 1, [Smy83a] above all.
6. **Commit to branch `agent6` with `scripts/gitcp.sh`; do not push.** Your branch
   has no upstream; "no tracking information" is the expected outcome.
7. Write `reports/r0034-report-from-agent6-to-orchestrator-theorem-18-theorem-16.md`
   with `started:`/`finished:` and the measured counts.
