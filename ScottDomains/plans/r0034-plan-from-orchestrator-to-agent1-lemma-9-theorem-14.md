---
round: r0034
from: orchestrator
to: agent1
subject: lemma-9-theorem-14
date: 2026-0806-22:35
status: pending
related:
  - plans/r0034-plan-from-orchestrator-to-orchestrator-six-way-remaining.md
  - docs/StatementRecovery.md
---

# r0034 agent1 — Lemma 9 and Theorem 14

Namespace: **`ScottDomains.Isomorphism`**. Files: `ScottDomains/Skeleton/Recovered.lean`
(7 `sorry` today), plus new modules under your namespace for the proofs.

Your stream retires **7 of the development's 8 `sorry`s**. Both results were
recorded as "not statable" until r0032 decoded the paper's Type 3 fonts; the
statements are now in the file and the work is proof, not recovery.

## Lemma 9 — six isomorphism laws over `D, E, F`

| # | Conjunct | Status |
| -- | -------- | ------ |
| 1 | `D⊗E ≅ E⊗D` | certain, prove |
| 2 | `(D⊗E)⊗F ≅ D⊗(E⊗F)` | certain, prove |
| 3 | `(E⊕F) ◦→ D ≅ (E ◦→ D) × (F ◦→ D)` | **false as printed** — refute |
| 4 | `D ◦→ (E ◦→ F) ≅ (D⊗E) ◦→ F` | certain, prove |
| 5 | `D⊗(E⊕F) ≅ (D⊗E)⊕(D⊗F)` | **false as printed** — refute |
| 6 | `D⊥ ◦→ E ≅ D → E` | certain, prove |

Items 3 and 5 are **false**, and the refutation is already worked out as prose in
`docs/StatementRecovery.md`: the witness `D = E = Prop`, `F = Prop × Prop`
separates the two sides by cardinality. Put both under the kernel as explicit
negations rather than leaving them as prose — this is the `lem10_smash` precedent,
and it closes open decision 2 of the r0033 restart plan.

Two reading hazards, both measured in earlier rounds:

- `◦→` is the **strict** function space (`StrictHom.lean`, r0024), distinct from
  `→`. Both extract from the PDF as `!`, so the two are indistinguishable in
  `pdftotext` output. Check every occurrence against the decoded content stream.
- `⊕` and `+` are **different operators**. `⊕` is the coalesced sum
  (`CoalescedSum.lean`, r0028); `+` is not.

## Theorem 14 — equivalent characterizations of a domain

The obstacle is definitional, not mathematical. `Bifinite.lean` *defines*
`IsBifinite` as the paper's condition 2, which would make the theorem `P ↔ P`.
`IsBifiniteViaProjections` supplies condition 1 from the paper's own definition;
`thm14` is the equivalence between the two. This is the result that licenses §6's
use of the Plotkin-order condition as the definition, so state it that way in the
docstring.

## Acceptance criteria

1. `ScottDomains/Skeleton/Recovered.lean` reports **0 `sorry`**.
2. Development-wide `sorry` count goes **8 → 1** (only `thm18` remains).
   Measure with `scripts/counts.sh`, do not estimate.
3. Items 3 and 5 appear as kernel-checked negations with the witness named in the
   docstring.
4. `scripts/compile.sh -r r0034` reports 0 errors and 0 warnings beyond `sorry`.

## Process rules

1. **Namespace `ScottDomains.Isomorphism`** for every new declaration.
2. **Edit/Write only — never heredocs.** r0032's agent3 edited Lean with
   `python3 - <<'PY'`, prompting the user repeatedly against its own plan.
3. **One command per Bash call. Never chain, never `cd`.** Use `git -C <path>`
   and absolute paths.
4. Multi-step work becomes a script in `scripts/` — standing-authorized.
5. **Read the PDF, not the paraphrase.**
6. **Commit to branch `agent1` with `scripts/gitcp.sh`; do not push.** "No
   tracking information" is the expected outcome, not an error.
7. Write `reports/r0034-report-from-agent1-to-orchestrator-lemma-9-theorem-14.md`
   with `started:` and `finished:` timestamps and the measured counts.
