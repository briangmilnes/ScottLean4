---
round: r0050
from: agent2
to: orchestrator
subject: numbered-name-standard
date: 2026-0810-14:36
started: 2026-0810-14:30
finished: 2026-0810-14:36
related:
  - plans/r0050-plan-from-orchestrator-to-orchestrator-numbered-name-standard.md
---

# r0050 phase 1, agent2 — 29 declarations renamed, 29 plain aliases added

## Measurement

| # | Quantity | Count |
| -- | -------- | ----: |
| 1 | Declarations renamed | 29 |
| 2 | Plain `alias` lines added | 29 |
| 3 | Declarations skipped as unattributed | 0 |
| 4 | Reference sites edited | 0 |
| 5 | Modules touched | 12 of 17 owned |
| 6 | Build errors | 0 |
| 7 | Build warnings | 0 |
| 8 | `sorry` | 0 |

Build: `scripts/compile.sh -r r0050`, 1372 jobs, wall 0:27.19, peak 1835 MiB
single / 3144 MiB tree pss. Log
`ScottDomains/logs/compile-20260810-143541.agent2.log`. Wrapper summary:
`diagnostics 0 · lake errors 0 · sorry 0 · other warnings 0`.

## The renames

Every number here is in Gunter & Scott's 1–30, so rule 2 (author qualification)
does not apply to any of them; each was confirmed against the defining
declaration's own docstring, which names the printed result.

| # | Module | Was | Becomes | Printed result |
| -- | ----- | --- | ------- | -------------- |
| 1 | `FixedPoint.lean` | `theorem1` | `theorem_1` | Theorem 1 (Fixed-Point Theorem) |
| 2 | `UniformFixedPoint.lean` | `theorem3` | `theorem_3` | Theorem 3 |
| 3 | `Theorem6.lean` | `theorem6` | `theorem_6` | Theorem 6 |
| 4 | `Isomorphism/Counterexample.lean` | `lem9_3_printed_false` | `lemma_9_3_printed_false` | Lemma 9.3 |
| 5 | `Isomorphism/Counterexample.lean` | `lem9_5_printed_false` | `lemma_9_5_printed_false` | Lemma 9.5 |
| 6 | `IdealCompletion.lean` | `thm11` | `theorem_11` | Theorem 11 (§5.2), forward half |
| 7 | `IdealCompletion.lean` | `thm11_converse` | `theorem_11_converse` | Theorem 11, converse |
| 8 | `Dyadic.lean` | `thm11_at_U` | `theorem_11_at_U` | Theorem 11 at `U₀` |
| 9 | `ContinuousAlgebra.lean` | `thm12` | `theorem_12` | Theorem 12 |
| 10 | `ContinuousAlgebra.lean` | `thm12_hoare` | `theorem_12_hoare` | Theorem 12 at `D♭` |
| 11 | `ContinuousAlgebra.lean` | `thm12_smyth` | `theorem_12_smyth` | Theorem 12 at `D♯` |
| 12 | `ContinuousAlgebra.lean` | `thm12_plotkin` | `theorem_12_plotkin` | Theorem 12 at `D♮` |
| 13 | `Section62.lean` | `thm16_positive` | `theorem_16_positive` | Theorem 16, positive half |
| 14 | `Section62.lean` | `thm16_positive_isEmbeddingProjectionPair` | `theorem_16_positive_isEmbeddingProjectionPair` | Theorem 16, positive half |
| 15 | `Universality.lean` | `thm21_image` | `theorem_21_image` | Theorem 21, closure retained |
| 16 | `UniversalDomain.lean` | `thm22` | `theorem_22` | Theorem 22 |
| 17 | `UniversalDomain.lean` | `thm22_of_isCompactlyGenerated` | `theorem_22_of_isCompactlyGenerated` | Theorem 22 |
| 18 | `UniversalDomain.lean` | `lem23` | `lemma_23` | Lemma 23 |
| 19 | `Universality.lean` | `lem24` | `lemma_24` | Gunter & Scott, Lemma 24 |
| 20 | `Universality.lean` | `thm25` | `theorem_25` | Theorem 25 |
| 21 | `Universality.lean` | `thm25_powerset` | `theorem_25_powerset` | Theorem 25 at `U = P N` |
| 22 | `Universality.lean` | `thm25_isUniversal` | `theorem_25_isUniversal` | Theorem 25 |
| 23 | `Combinator.lean` | `thm26` | `theorem_26` | Theorem 26 |
| 24 | `Combinator.lean` | `thm26_subalgebra` | `theorem_26_subalgebra` | Theorem 26, subalgebra form |
| 25 | `Combinator.lean` | `thm26_retract` | `theorem_26_retract` | Theorem 26 at a retract |
| 26 | `Combinator.lean` | `exists_lambdaModel_of_thm25` | `exists_lambdaModel_of_theorem_25` | derivation from Theorem 25 |
| 27 | `Atomless.lean` | `thm27` | `theorem_27` | Theorem 27, no hypothesis |
| 28 | `Dyadic.lean` | `thm27_of_isNormallyRepresented` | `theorem_27_of_isNormallyRepresented` | Theorem 27, post-Boolean-algebra |
| 29 | `Dyadic.lean` | `thm27` | `theorem_27` | Theorem 27 as printed |

The longest new name is
`theorem_16_positive_isEmbeddingProjectionPair` at 45 characters, under rule 4's
60-character limit, so no `_and_<second>` component had to be dropped.

Row 29 and row 27 are two declarations both now named `theorem_27`, in the
distinct namespaces `ScottDomains.Dyadic` and `ScottDomains.Atomless`. That
duplication is pre-existing — they were both `thm27` before — and the two full
names remain distinct.

## `lem24` versus Gunter 1987's Lemma 24

`Universality.lean:394` is Gunter & Scott's Lemma 24, confirmed by its own
docstring ("**Lemma 24.** Let `U` be a non-trivial cpo. If the product and
function space operators are representable over `U`, then there are non-trivial
cpos `D` and `E` …"), so it takes the unqualified `lemma_24`. `A1Lemma24.lean`
(Gunter 1987's Lemma 24) is agent4's file and was not touched.

## Unattributed

None. Every one of the 29 numbers lies in 1–30 and every defining docstring
names the printed result, so rule 2's author-qualified dotted form was not
needed and nothing was left alone for want of attribution.

## Rule 4, one judgment call

Row 26, `exists_lambdaModel_of_thm25`, does not itself begin with a retired
abbreviation — the abbreviation sits in its derivation suffix. Rule 4 says
derivation suffixes take the new short form, so it was renamed to
`exists_lambdaModel_of_theorem_25` and aliased like the rest. Flagging it
because the phase-1 selection criterion was "name begins with the prefix," and
this one does not; revert the single edit if the orchestrator prefers the
narrow reading.

## Two residues outside phase 1, reported not fixed

1. **Section names.** `Atomless.lean:605`, `Dyadic.lean:448` and
   `Combinator.lean:522` open `section Thm27` / `section Thm26`. These are
   `section`s, not `namespace`s, so they contribute nothing to any declaration's
   full name and no reference resolves through them. They still spell the
   retired abbreviation. Phase 3 covers module filenames but not section names;
   these want a decision.
2. **Axiom-audit comment blocks.** The trailing `#print axioms` records in
   `ContinuousAlgebra.lean` and `Universality.lean` list the old names
   (`ScottDomains.ContinuousAlgebra.thm12`, …). They are comments recording a
   past run, and the hard rule forbids changing anything but a name, so they
   were left verbatim. They should be refreshed when phase 2 deletes the
   aliases and the audits are re-run.

## Method note

No reference site anywhere was edited; every existing call — including
`UniformFixedPoint.lean:166`'s use of `theorem1`, `Universality.lean:480`'s use
of `thm25` and `lem23`, and `Atomless.lean:649`'s use of
`Dyadic.thm27_of_isNormallyRepresented` — still resolves through a plain
`alias`. That is what the zero-error, zero-warning build measures: 29 new names
elaborate and ~700 old-name sites still resolve. Phase 2's alias deletion will
name each of those sites through the elaborator.
