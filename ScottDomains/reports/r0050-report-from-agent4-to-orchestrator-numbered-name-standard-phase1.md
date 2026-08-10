---
round: r0050
from: agent4
to: orchestrator
subject: numbered-name-standard-phase1
date: 2026-0810-14:42
started: 2026-0810-14:34
finished: 2026-0810-14:42
related:
  - plans/r0050-plan-from-orchestrator-to-orchestrator-numbered-name-standard.md
---

# r0050 agent4 — phase 1 on the `Effective/**`, `LemThirty`, `PRep*`, `A1`–`A7`, `Audit/**` partition

## Outcome

43 declarations renamed, 43 plain `alias` lines added, 1 declaration left alone
as unattributed, 0 reference sites edited, 0 files renamed. Build: **0 errors, 0
warnings, 0 `sorry`**, 1372 jobs (`ScottDomains/logs/compile-20260810-144115.agent4.log`).

## Fixing the scope before editing

The plan's rename set is the 126 declarations it tabulates under the five
retired prefixes. `scripts/a4-r50-scope.sh` recomputes that count over
`ScottDomains/ScottDomains/**/*.lean` and reproduces it exactly — 126, split
`thm` 50, `lem` 36, `lemma` 24, `theorem` 14, `prop` 2. The measurement
therefore fixes the predicate: **a declaration is in scope when its name begins
with `thm|lem|lemma|theorem|prop|cor` immediately followed by a digit.** Rule 3's
`Prop`-valued claim `def`s (`Thm…`, `Lem…`, UpperCamelCase) are a separate set,
not counted in the 126.

That predicate is what excludes the derived and negated results —
`not_forall_lemma28`, `five_conjuncts_of_thm29Normal`,
`rep_lift_V_of_thm29Normal`, `not_thm26_statement_of_zero_arity`, and 17 more in
this partition. Their leading token is a negation or a derivation, not a printed
number, so the standard's `theorem_<N>[_<semantic>]` form does not apply; the
retired abbreviation survives only inside a semantic tail, which the plan's
"tail kept verbatim" rule preserves. `scripts/a4-r50-decls.sh` enumerates every
declaration in the partition whose name carries a digit, which is how the
in-scope and out-of-scope sets were separated by inspection rather than by guess.

Package-wide the retired-prefix count fell from **126 to 87**, i.e. 39 of the
126 were in this partition and all 39 are renamed.

## Counts

| # | Category | Count |
| -- | -------- | ----: |
| 1 | snake_case renames of numbered results (of the 126) | 39 |
| 2 | rule-3 `Prop`-valued claim `def` renames | 4 |
| 3 | total renames | 43 |
| 4 | plain `alias` lines added | 43 |
| 5 | in-scope declarations skipped as unattributed | 1 |
| 6 | reference sites edited | 0 |
| 7 | build errors | 0 |
| 8 | build warnings | 0 |
| 9 | `sorry` | 0 |

The alias count is confirmed per file by `grep -c '^\s*alias '` and sums to 43
across the 23 modules touched.

## The two attribution hazards

**1. Gunter 1987's Lemma 24.** `A1Lemma24.lean`'s own module docstring
(lines 15–36) cites *Gunter, Universal Profinite Domains*, Information and
Computation **72** (1987) 1–30, p. 20, quoting Lemma 24 verbatim, and p. 23 for
the identification `A⁺ = M(A)`. The attribution is established by the defining
docstring, so rule 2 applies:

| # | Was | Becomes |
| -- | -- | ------- |
| 1 | `lemma24_MPair` | `gunter87_lemma_24_MPair` |
| 2 | `lemma24_Step` | `gunter87_lemma_24_Step` |

Gunter & Scott's own Lemma 24 (`lem24` in `Universality.lean`) is agent2's and
was not touched. The two results no longer share a stem.

**2. `lemma217_from_propertyM_pairs` — left alone, unattributed.**
`Audit/Bifinite.lean:63`. Its number, 217, is not in 1–30, so rule 2 requires
the paper and printed number from the defining docstring. That docstring
(`Audit/Bifinite.lean:3–44`) names the sibling declaration
`JungNets.lemma217_of_thm137` and describes the interderivability, but **states
no paper and no printed number**. Following the chain one module further,
`JungNets.lean:372–377` attributes it to `JungSFP.lemma217`, and `JungSFP.lean`
discusses Jung's construction — which makes "Jung's Lemma 2.17" plausible but
not established at the point of definition, and `JungSFP.lean` is agent3's
module, not mine. Per the plan's "an unattributed name is better than a
confidently wrong one", the declaration keeps its name. If agent3's pass
establishes the citation, this one declaration is a one-line follow-up.

No other number in this partition is outside 1–30. The numbers appearing are 2,
3, 7, 17, 24, 26, 28, 29, 30 and 217, and every one of those except 24 and 217
is Gunter & Scott's, confirmed against the defining module docstrings
(`A1Theorem2.lean:181` for Theorem 2 at printed folio 6; `A7Thm26Arity.lean:17–23`
quoting Theorem 26 verbatim from printed p. 39; `A3Thm29.lean:25` and
`A4Lemma17Fun.lean:16` for Theorem 29 and Lemma 17).

## Rule 3 — the `Prop`-valued claim `def`s

Four renamed, abbreviation only, UpperCamelCase preserved, no snake_case:

| # | Module | Was | Becomes |
| -- | ----- | --- | ------- |
| 1 | `LemThirty.lean:512` | `Thm29Normal` | `Theorem29Normal` |
| 2 | `LemThirty.lean:299` | `Thm29SecondAtDomains` | `Theorem29SecondAtDomains` |
| 3 | `A3Thm29.lean:194` | `Thm29NormalWithoutDomain` | `Theorem29NormalWithoutDomain` |
| 4 | `A7Thm26Arity.lean:145` | `Thm26Printed` | `Theorem26Printed` |

Six were already correct and were left untouched: `Lemma30`, `Lemma30AtV`,
`Lemma28`, `Lemma28AtU`, `Theorem7ArrowRecursive`, `Theorem7StrictRecursive`.

**Two named in my instructions are outside my module list and were not touched.**
`Lem30Arrow` and `Thm29Second` are both defined in `Colimit.lean`
(lines 1061 and 1051), which appears in **no** agent's partition in the plan's
table — not agent1's, agent2's, agent3's, or mine. Under "no file outside the
list" I left them. They still need `Lem30Arrow → Lemma30Arrow` and
`Thm29Second → Theorem29Second`, and `Colimit.lean` needs an owner before phase
2 deletes the aliases.

## The renames

Semantic tails are verbatim. Where the tail was glued to the number in
camelCase, the standard inserts `_` and lowercases the tail's initial, exactly as
`lemma28AtU → lemma_28_atU` and `lemma30AtV_iff → lemma_30_atV_iff` prescribe.
Where the tail was already `_`-separated it is copied unchanged (`_MPair`,
`_Step`, `_arrow`, `_fun`). No name exceeds 60 characters, so rule 4's
truncation never applied; the longest is
`theorem_7_strictRecursive_of_strictStepFunctionsDecidable` at 56.

| # | Module | Was | Becomes |
| -- | ----- | --- | ------- |
| 1 | `Effective/FunctionSpace.lean` | `theorem7_arrow` | `theorem_7_arrow` |
| 2 | `Effective/FunctionSpace.lean` | `theorem7_strict` | `theorem_7_strict` |
| 3 | `Effective/A1FlatRecursive.lean` | `theorem7ArrowRecursive_of_stepFunctionsDecidable` | `theorem_7_arrowRecursive_of_stepFunctionsDecidable` |
| 4 | `Effective/A2Compactness.lean` | `theorem7ArrowRecursive_of_scottHomC` | `theorem_7_arrowRecursive_of_scottHomC` |
| 5 | `Effective/A2Compactness.lean` | `theorem7StrictRecursive_of_strictHomC` | `theorem_7_strictRecursive_of_strictHomC` |
| 6 | `Effective/A3StepDecidable.lean` | `theorem7StrictRecursive_of_residue` | `theorem_7_strictRecursive_of_residue` |
| 7 | `Effective/A3StrictRecursive.lean` | `theorem7_strict_ofEnum` | `theorem_7_strict_ofEnum` |
| 8 | `Effective/A3StrictRecursive.lean` | `theorem7StrictRecursive_of_strictStepFunctionsDecidable` | `theorem_7_strictRecursive_of_strictStepFunctionsDecidable` |
| 9 | `Audit/Foundations.lean` | `theorem3_statement_eq_eq_kleeneOperator_op_statement` | `theorem_3_statement_eq_eq_kleeneOperator_op_statement` |
| 10 | `LemThirty.lean` | `lemma30_of` | `lemma_30_of` |
| 11 | `LemThirty.lean` | `lemma30_iff_lemma28_and_plotkin` | `lemma_30_iff_lemma28_and_plotkin` |
| 12 | `LemThirty.lean` | `thm29SecondAtDomains_of_thm29Second` | `theorem_29_secondAtDomains_of_thm29Second` |
| 13 | `LemThirty.lean` | `thm29SecondAtDomains_of_thm29Normal` | `theorem_29_secondAtDomains_of_thm29Normal` |
| 14 | `BifiniteUniversal.lean` | `thm29` | `theorem_29` |
| 15 | `PRep.lean` | `lemma28_of` | `lemma_28_of` |
| 16 | `PRepSum.lean` | `lemma28AtU_of` | `lemma_28_atU_of` |
| 17 | `PowerdomainMapRep.lean` | `lemma28AtU_of''` | `lemma_28_atU_of''` |
| 18 | `Lemma28AtU.lean` | `lemma28AtU_of'` | `lemma_28_atU_of'` |
| 19 | `A1Lemma24.lean` | `lemma24_MPair` | `gunter87_lemma_24_MPair` |
| 20 | `A1Lemma24.lean` | `lemma24_Step` | `gunter87_lemma_24_Step` |
| 21 | `A1Theorem2.lean` | `theorem2` | `theorem_2` |
| 22 | `A2Lemma28.lean` | `lemma28AtU_iff` | `lemma_28_atU_iff` |
| 23 | `A2Lemma28.lean` | `lemma28_of_universal` | `lemma_28_of_universal` |
| 24 | `A2Lemma28.lean` | `lemma28AtU_of_universal` | `lemma_28_atU_of_universal` |
| 25 | `A2Thm29Universal.lean` | `thm29Normal_of_hasFiniteExtensions` | `theorem_29_normal_of_hasFiniteExtensions` |
| 26 | `A2Thm29Universal.lean` | `thm29Normal_of_hasNormalRealizations` | `theorem_29_normal_of_hasNormalRealizations` |
| 27 | `A2Thm29Universal.lean` | `thm29SecondAtDomains_of_hasNormalRealizations` | `theorem_29_secondAtDomains_of_hasNormalRealizations` |
| 28 | `A3Lemma30Schemes.lean` | `lemma30AtV_of_thm29Normal_of_arrows` | `lemma_30_atV_of_thm29Normal_of_arrows` |
| 29 | `A3Thm29.lean` | `lemma30AtV_iff` | `lemma_30_atV_iff` |
| 30 | `A3Thm29.lean` | `lem30Arrow_iff` | `lemma_30_arrow_iff` |
| 31 | `A3Thm29.lean` | `lem30Arrow_of_lemma30AtV` | `lemma_30_arrow_of_lemma30AtV` |
| 32 | `A4Lemma17Fun.lean` | `lem17_fun` | `lemma_17_fun` |
| 33 | `A4Lemma17Fun.lean` | `lem17_strictFun` | `lemma_17_strictFun` |
| 34 | `A4Lemma17Fun.lean` | `lem17_fun_imp_old` | `lemma_17_fun_imp_old` |
| 35 | `A4Lemma17Fun.lean` | `lem17_strictFun_imp_old` | `lemma_17_strictFun_imp_old` |
| 36 | `A4PowerdomainRep.lean` | `lemma28AtU` | `lemma_28_atU` |
| 37 | `A5Thm29Finite.lean` | `thm29Normal_finiteBasis` | `theorem_29_normal_finiteBasis` |
| 38 | `A5Thm29Finite.lean` | `thm29Normal_finiteBasis_of_thm29Normal` | `theorem_29_normal_finiteBasis_of_thm29Normal` |
| 39 | `A6ProjectionBifinite.lean` | `lemma30AtV_of_thm29Normal` | `lemma_30_atV_of_thm29Normal` |
| 40 | `LemThirty.lean` | `Thm29SecondAtDomains` | `Theorem29SecondAtDomains` |
| 41 | `LemThirty.lean` | `Thm29Normal` | `Theorem29Normal` |
| 42 | `A3Thm29.lean` | `Thm29NormalWithoutDomain` | `Theorem29NormalWithoutDomain` |
| 43 | `A7Thm26Arity.lean` | `Thm26Printed` | `Theorem26Printed` |

`A5Unfinished.lean`, `A1R46.lean`, `A7SneqRows.lean`, `Audit/Powerdomains.lean`,
`Audit/Projections.lean`, `Audit/SectionSeven.lean`, `Audit/Skeleton.lean`,
`Effective/Powerset.lean`, `Effective/A3FreeCarrier.lean`,
`Effective/A3Operator.lean`, `Effective/A4Recursion.lean`, `PRepFun.lean` hold no
in-scope declaration and were not edited.

## Method notes for phase 2

`alias` is not `@[deprecated] alias` anywhere in this diff; the build emits zero
warnings, which is the measurement that confirms it. `alias` was not previously
used in the package, so its availability was checked by a single-module probe
build (`ScottDomains.Effective.FunctionSpace`, 1020 jobs, 0 diagnostics) before
the other 42 edits were made.

Two `alias` forms are present: one for theorems and one for the four
`Prop`-valued `def`s. The `def` case is the one worth flagging for phase 2:
`alias Thm29Normal := Theorem29Normal` elaborates to a `def` whose value is the
new constant, so a downstream `intro`/`obtain` on `h : Thm29Normal` unfolds two
steps rather than one. This is sound at default transparency and the build
confirms it, but a `simp only [Thm29Normal]` or `unfold Thm29Normal` at a
reference site would have stopped one step short. A pre-edit grep for those
tactic forms over the four names found **zero** occurrences, which is why the
`def` aliases are safe here and may not be in another partition.

No statement, binder, proof term or docstring claim was changed. Every edit
replaced a declaration's name and appended an `alias` line.
