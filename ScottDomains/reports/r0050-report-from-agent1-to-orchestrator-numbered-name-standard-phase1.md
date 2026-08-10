---
round: r0050
from: agent1
to: orchestrator
subject: numbered-name-standard-phase1
date: 2026-0810-14:37
started: 2026-0810-14:30
finished: 2026-0810-14:37
related:
  - plans/r0050-plan-from-orchestrator-to-orchestrator-numbered-name-standard.md
---

# r0050 phase 1, agent1 — 34 declarations renamed, 34 aliased, build at zero

## Measurement

| # | Quantity | Count |
| -- | ------- | ----: |
| 1 | Declarations renamed to the standard | 34 |
| 2 | Plain `alias` lines added | 34 |
| 3 | Declarations left alone as unattributed | 0 |
| 4 | Reference sites edited | 0 |
| 5 | Files touched | 13 |
| 6 | `lake` errors | 0 |
| 7 | Warnings (including `sorry`) | 0 |
| 8 | Jobs built | 1372 |

Build: `scripts/compile.sh -r r0050`, log
`ScottDomains/logs/compile-20260810-143555.agent1.log` — `exit 0 · wall 0:23.40 ·
mem 1837 MiB single · jobs 1372 · diagnostics 0 · lake errors 0 · sorry 0 ·
other warnings 0`.

The diff is 102 insertions and 34 deletions. That decomposes exactly: 34
deletions are the 34 old declaration lines, and the 102 insertions are the 34
replacement declaration lines plus 34 `alias` lines plus their 34 separating
blank lines. No statement, proof, binder, or docstring text changed — the arity
of the diff is itself the evidence.

## The renames

| # | Module | Old | New |
| -- | ----- | --- | --- |
| 1 | `Skeleton/Section6b.lean` | `thm16` | `theorem_16` |
| 2 | `Skeleton/Section6b.lean` | `lem20` | `lemma_20` |
| 3 | `Skeleton/Lemma10.lean` | `lem10_prod` | `lemma_10_prod` |
| 4 | `Skeleton/Lemma10.lean` | `lem10_smash` | `lemma_10_smash` |
| 5 | `Skeleton/Lemma10.lean` | `lem10_lift` | `lemma_10_lift` |
| 6 | `Skeleton/Lemma10.lean` | `lem10_strict` | `lemma_10_strict` |
| 7 | `Skeleton/Lemma17.lean` | `lem17_prod` | `lemma_17_prod` |
| 8 | `Skeleton/Lemma17.lean` | `lem17_lift` | `lemma_17_lift` |
| 9 | `Skeleton/Lemma17.lean` | `lem17_fun` | `lemma_17_fun` |
| 10 | `Skeleton/Section6.lean` | `prop15` | `proposition_15` |
| 11 | `Skeleton/Section6.lean` | `thm18` | `theorem_18` |
| 12 | `Skeleton/Section6.lean` | `lem19` | `lemma_19` |
| 13 | `Skeleton/Recovered.lean` | `lem9_1` | `lemma_9_1` |
| 14 | `Skeleton/Recovered.lean` | `lem9_2` | `lemma_9_2` |
| 15 | `Skeleton/Recovered.lean` | `lem9_3` | `lemma_9_3` |
| 16 | `Skeleton/Recovered.lean` | `lem9_4` | `lemma_9_4` |
| 17 | `Skeleton/Recovered.lean` | `lem9_5` | `lemma_9_5` |
| 18 | `Skeleton/Recovered.lean` | `lem9_6` | `lemma_9_6` |
| 19 | `Skeleton/Recovered.lean` | `thm14` | `theorem_14` |
| 20 | `Skeleton/Sum.lean` | `lem10_sum` | `lemma_10_sum` |
| 21 | `Skeleton/Sum.lean` | `lem17_sum` | `lemma_17_sum` |
| 22 | `Skeleton/Sum.lean` | `lem17_smash` | `lemma_17_smash` |
| 23 | `ClosureProperties.lean` | `lemma10` | `lemma_10` |
| 24 | `ClosureProperties.lean` | `lemma17` | `lemma_17` |
| 25 | `ClosureProperties/SeparatedSum.lean` | `lem10_separated` | `lemma_10_separated` |
| 26 | `ClosureProperties/SeparatedSum.lean` | `lem17_separated` | `lemma_17_separated` |
| 27 | `ClosureProperties/StrictFunction.lean` | `lem17_strictFun` | `lemma_17_strictFun` |
| 28 | `ClosureProperties/Powerdomain.lean` | `lem17_hoare` | `lemma_17_hoare` |
| 29 | `ClosureProperties/Powerdomain.lean` | `lem17_smyth` | `lemma_17_smyth` |
| 30 | `ClosureProperties/Powerdomain.lean` | `lem17_plotkin` | `lemma_17_plotkin` |
| 31 | `Powerdomain/Hoare.lean` | `thm11_hoare` | `theorem_11_hoare` |
| 32 | `Powerdomain/BoundedComplete.lean` | `lem13_hoare` | `lemma_13_hoare` |
| 33 | `Powerdomain/BoundedComplete.lean` | `lem13_smyth` | `lemma_13_smyth` |
| 34 | `Kleene/Uniform.lean` | `theorem3_existsUnique` | `theorem_3_existsUnique` |

Each carries a plain `alias <old> := <new>` immediately after the declaration
body, inside the same namespace and section, so every qualified old name still
resolves. No `@[deprecated]` attribute was used, per the plan's rule against
emitting a warning at each reference site.

## Rule 2 — attribution

Every number renamed lies in Gunter & Scott's 1–30: 3, 9, 10, 11, 13, 14, 15,
16, 17, 18, 19, 20. No declaration in my modules carries a number outside that
range, so the author-qualified dotted form was never required and **nothing was
left alone as unattributed**.

The one name whose attribution was not immediate is `theorem3_existsUnique` in
`Kleene/Uniform.lean`. Its module docstring quotes the source directly — "Gunter
& Scott, *Semantic Domains*, §2.3 (printed p. 7) … **Theorem 3** `fix` is *the*
unique *uniform fixed point operator*" — which fixes both the paper and the
printed number, so the plain `theorem_3_existsUnique` is correct and no author
qualifier applies.

`lem9_1` through `lem9_6` are the six parts of Lemma 9; the plan's own worked
example (`lem9_3_printed_false` → `lemma_9_3_printed_false`) fixes the reading of
the second integer as the printed part index, and the renames follow it.

## Rule 3 — `Prop`-valued claim `def`s

None. A grep for `def`/`abbrev` declarations whose name contains `Thm`, `Lem`,
`Prop` or `Cor` over all five module trees returns zero rows, so the
UpperCamelCase normalization has no instance in my partition.

## Scope

Thirteen files changed, all inside the assigned partition (`Skeleton/**`,
`ClosureProperties.lean`, `ClosureProperties/**`, `Powerdomain/**`,
`Kleene/**`). The remaining eight modules in the partition — `Kleene/Grammar`,
`Kleene/Extension`, `Kleene/Factorial`, `Kleene/FixContinuous`, `Kleene/Graph`,
`Powerdomain/Plotkin`, `Powerdomain/Smyth`, `Powerdomain/Universal` — define no
numbered result and were not touched.

Reference sites were not edited anywhere, including the ones inside my own
files: `lemma_10_smash`'s proof still calls `lem10_prod`, `ClosureProperties.lean`
still assembles its two conjunctions out of the fourteen old names, and
`ClosureProperties/SeparatedSum.lean` still composes `lem10_lift`/`lem10_sum`.
Those are exactly the sites phase 2's alias deletion will surface as `unknown
identifier`.
