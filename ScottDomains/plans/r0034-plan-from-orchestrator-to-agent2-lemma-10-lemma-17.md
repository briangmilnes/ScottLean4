---
round: r0034
from: orchestrator
to: agent2
subject: lemma-10-lemma-17
date: 2026-0806-22:35
status: pending
related:
  - plans/r0034-plan-from-orchestrator-to-orchestrator-six-way-remaining.md
  - docs/PaperInventory.md
---

# r0034 agent2 — complete Lemma 10 and Lemma 17

Namespace: **`ScottDomains.ClosureProperties`**.

Six conjuncts, every one against a statement that already exists. Your stream
moves two *partial* results to complete, taking the numbered count from 18 to 20
of 29.

## Lemma 10 — one conjunct left (6 of 7 today)

`D, E` bounded complete ⟹ `→, ◦→, ×, ⊗, ⊕, +, ()⊥` bounded complete.

Proved: `→` (r0007), `×`, `⊗`, `()⊥`, `◦→` (r0027, `Skeleton/Lemma10.lean`), `⊕`
(r0028, `Skeleton/Sum.lean` over `CoalescedSum`).

**Missing: `+`.** It is a *different operator* from `⊕`, which is why the row read
"complete" for two rounds while a conjunct was open. Expected route:
`D + E = D⊥ ⊕ E⊥`, reusing the `⊕` conjunct — cheap if that identity is stated
first as a definitional isomorphism.

## Lemma 17 — five conjuncts left (5 of 10 today)

`D, E` bifinite ⟹ `→, ◦→, ×, ⊗, ⊕, +, ()⊥, D♮, D♯, D♭` bifinite.

Proved: `×`, `()⊥`, `→` (r0027, `Skeleton/Lemma17.lean`), `⊗`, `⊕` (r0028,
`Skeleton/Sum.lean`).

**Missing: `◦→`, `+`, and the three powerdomains `D♮`, `D♯`, `D♭`.**

The three powerdomain conjuncts were dropped from the extraction **with their
glyphs** — `pdftotext` renders `♮`/`♯`/`♭` as `\`/`]`/`[` — not because the
objects were unavailable. All three have existed since r0029:
`Powerdomain/{Hoare,Smyth,Plotkin}.lean`, each `IdealCompletion (Pf K(D))` under
its pre-order, each with a `Domain` instance from Theorem 11 and its compacts
characterized as the principal ideals.

`ContinuousAlgebra.lean` (r0032, 1254 lines, 0 `sorry`) is the machinery to reach
for: Theorem 12 at all three powerdomains, existence and uniqueness, factoring
through `{|·|}` rather than principal ideals, plus the proof that each free
algebra models its own theory. `[IsAlgebraic D]` is its whole hypothesis —
countability of `K(D)` is never used and bounded completeness is never needed, so
do not add hypotheses the machinery does not require.

## Acceptance criteria

1. Lemma 10 at **7 of 7** conjuncts, Lemma 17 at **10 of 10**.
2. Both results move from partial to complete in `docs/PaperInventory.md` rows
   2 and 2b — report the counts, the orchestrator edits the file.
3. No new `sorry`. Measure with `scripts/counts.sh`.
4. `scripts/compile.sh -r r0034` reports 0 errors and 0 warnings beyond `sorry`.
5. If a conjunct turns out **false as stated** — the r0032 Theorem 16 outcome —
   refute it under the kernel and say so. A refutation is a result, not a failure.

## Process rules

1. **Namespace `ScottDomains.ClosureProperties`** for every new declaration.
2. **Edit/Write only — never heredocs.**
3. **One command per Bash call. Never chain, never `cd`.**
4. Multi-step work becomes a script in `scripts/` — standing-authorized.
5. **Read the PDF, not the paraphrase.** This stream exists because a paraphrase
   undercounted both lemmas.
6. **Commit to branch `agent2` with `scripts/gitcp.sh`; do not push.**
7. Write `reports/r0034-report-from-agent2-to-orchestrator-lemma-10-lemma-17.md`
   with `started:`/`finished:` and the measured conjunct counts.
