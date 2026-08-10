---
round: r0052
from: agent1
to: orchestrator
subject: unproven-claims-as-sorry
date: 2026-0810-16:06
started: 2026-0810-15:39
finished: 2026-0810-16:06
related: plans/r0052-plan-from-orchestrator-to-agent1-unproven-claims-as-sorry.md
---

# r0052 — the census of 72, three sorried roots, and the detector that scored a `sorry` as a proof

Executed under the plan as amended in flight. Final state: **three** sorried
theorems, one per independent hole; `a6-query.lean` no longer counts a sorried
theorem as a discharge; `docs/Status.md` tables 4 and 5 report three unproven
statements and `sorry` 3.

## 1. Build and the three counts that must agree

| # | Measurement | Before r0052 | After |
| -- | ---------- | -----------: | ----: |
| 1 | lake errors | 0 | 0 |
| 2 | warnings other than `sorry` | 0 | 0 |
| 3 | `sorry` warnings, `scripts/compile.sh` | 0 | **3** |
| 4 | `sorry` lines, `scripts/counts.sh` | 0 | **3** |
| 5 | constants depending on `sorryAx`, transitive | 0 | **3** |
| 6 | `axiom` declarations in package modules | 0 | 0 |
| 7 | Prop-valued defs with no unconditional proof | 72 | **72** |
| 8 | modules / lines / theorems | 124 / 46,097 / 2,119 | 124 / 46,442 / 2,122 |

Log: `ScottDomains/logs/compile-20260810-160040.agent1.log`.

Rows 3, 4 and 5 are three independent instruments — the elaborator's warning, a
lexical scan of the sources, and a closure computed over the kernel environment —
and they agree at 3. They did not agree at first: `counts.sh` matches
`^\s*sorry\s*$` and reported 0 while the build reported 3, because the three
theorems were written `… := sorry` on the statement's own line. I put `sorry` on
its own line rather than loosen that grep, which would then match the word
`sorry` in the very docstrings that explain these theorems — string-matching Lean
source is the defect class the script's own header warns about.

## 2. The three sorried theorems

| # | Theorem | Site | Statement it asserts |
| -- | ------ | ---- | -------------------- |
| 1 | `R49.Agent3.scottHomCRecursive_unproven` | `Effective/A3StepDecidable.lean:200` | `ScottHomCRecursive d e` — the consistency-guarded enumeration of `K(D → E)` is recursive |
| 2 | `R49.Agent3.strictHomCRecursive_unproven` | `Effective/A3StepDecidable.lean:386` | `StrictHomCRecursive d e` — the same over `K(D ⊸ E)` |
| 3 | `LemThirty.theorem29Normal_unproven` | `LemThirty.lean:537` | `Theorem29Normal` — normal embedding of `K(E)` into `A∞` for every bifinite domain `E` |

Each sits immediately beside its `def`, which is unchanged, and carries a
docstring saying what must be proved to remove the `sorry`. Rows 1 and 2 take
the binders their `def` carries, so each universally closes at any use site.

`scripts/a1-r52-sorry-cone.lean` computes the reverse reachability closure of
`sorryAx` over all 4,393 package constants and reports `SORRYCONECOUNT 3` — those
three names and nothing else (`analyses/a1-r52-sorry-cone.txt`). This is the
strong form of the check: a consumer rewired to apply a sorried root would name
the root, not `sorryAx`, and `a6-query.lean`'s `SORRYUSER` record — a direct test
— would miss it. **No pre-existing declaration's axiom footprint changed.**

**Why these three and not the eight open claims.** They are the roots; the other
five open claims are already derivable from them by reductions proved in earlier
rounds, so sorrying those five would assert five more times what these three
assert once.

| # | Open claim | Root | Reduction, already proved |
| -- | --------- | ---- | ------------------------- |
| 1 | `Effective.StepFunctionsDecidable` | 1 | `R49.Agent3.stepFunctionsDecidable_of_scottHomC` |
| 2 | `Effective.Theorem7ArrowRecursive` | 1 | `R47.Agent2.theorem_7_arrowRecursive_of_scottHomC` |
| 3 | `R49.Agent3.StrictStepFunctionsDecidable` | 2 | `R49.Agent3.strictStepFunctionsDecidable_of_strictHomC` |
| 4 | `Effective.Theorem7StrictRecursive` | 2 | `R47.Agent2.theorem_7_strictRecursive_of_strictHomC` |
| 5 | `LemThirty.Theorem29SecondAtDomains` | 3 | `LemThirty.theorem_29_secondAtDomains_of_thm29Normal` |
| 6 | `LemThirty.Lemma30AtV` | 3 | `R49.Agent6.lemma_30_atV_of_thm29Normal` |
| 7 | `Colimit.Lemma30Arrow` | 3, via 6 | `R45.Agent3.lemma_30_arrow_of_lemma30AtV` |
| 8 | `LemThirty.Theorem29Normal` | itself | — |

Roots 1 and 2 are two roots and not one because no proved reduction connects
them: the only route to countability of `K(D ⊸ E)` in this development,
`PRepFun.strictHomDomain`, is an injection into `K(D → E)` that names no
enumeration, and `theorem_7_strictRecursive_of_residue` takes the strict residue
as its own hypothesis. Root 1 is `ScottHomCRecursive` and not
`StepFunctionsDecidable` because `stepFunctionsDecidable_of_scottHomC` derives
the latter from the former.

**No reduction was applied and no consumer discharged.**
`scripts/a1-r52-consumers.lean` counts the package declarations taking one of the
eight open claims (or its r0050 alias) as a hypothesis:

| # | Hypothesis assumed | Consumers |
| -- | ----------------- | --------: |
| 1 | `Thm29SecondAtDomains` | 24 |
| 2 | `Thm29Normal` | 14 |
| 3 | `Effective.StepFunctionsDecidable` | 3 |
| 4 | `R49.Agent3.StrictHomCRecursive` | 3 |
| 5 | `LemThirty.Lemma30AtV` | 2 |
| 6 | `R49.Agent3.ScottHomCRecursive` | 2 |
| 7 | `R49.Agent3.StrictStepFunctionsDecidable` | 1 |
| 8 | total, distinct declarations | **49** |

All 49 are now reachable from a sorried root, and **all 49 stay conditional**.
None assumes two of the claims, so the distinct count equals the pair count.

## 3. The census — all 72 adjudicated

`analyses/claim-census.20260810-155203.agent1.tsv`, one row and one reason each,
against the baseline scan `analyses/a6-env-r52.txt` (120 Prop-valued defs, 72
undischarged).

| # | Verdict | Count |
| -- | ------ | ----: |
| 1 | aliases excluded (r0050 scaffolding) | **9** |
| 2 | claims — open | **8** |
| 3 | claims — refuted | **5** |
| 4 | concepts | **50** |
| 5 | total | 72 |

The 9 aliases: `Colimit.Thm29Second`, `Colimit.Lem30Arrow`,
`LemThirty.Thm29SecondAtDomains`, `LemThirty.Thm29Normal`,
`R45.Agent3.Thm29NormalWithoutDomain`, `R49.Agent7.Thm26Printed`,
`JungNets.Thm137`, `JungNets.Thm137Chains`, `PropertyM.Thm137Omega`.

Excluding them is load-bearing, not hygiene. `JungNets.Theorem137`,
`Theorem137Chains` and `PropertyM.Theorem137Omega` — Jung's Theorem 1.37 and its
two weakenings — were **proved in r0045** (`R45.Agent5.jung_theorem_1_37` and
companions) and are correctly absent from the 72; their aliases are present with
`uncond` 0, because the proofs conclude the new name and an `alias` is a distinct
constant. r0044's claims file names the aliases, so running it against this
environment reports three resolved results as open.

Five more of r0044's claims are simply **proved**: `PRep.Lemma28AtU` and the four
powerdomain-map obligations `SmythImageIso`, `SmythFamilyLUB`, `HoareImageIso`,
`HoareFamilyLUB`, all by `R45.Agent4.*`.

Two departures from the plan's provisional list of eight.
`Effective.PreservesRecursivePresentation` is **not in the population** — it has
two unconditional proofs (`preservesRecursivePresentation_fstOp`, `_sndOp`), it is
a schema over operators whose universal closure is not §3.2's sentence, and its
one open instance is proved *equivalent* to `Theorem7ArrowRecursive` by
`R47.Agent3.preservesRecursivePresentation_arrowOp_iff`.
`R49.Agent3.StrictStepFunctionsDecidable` takes its place: Theorem 7's third
printed sentence, added after r0044.

### The five refuted claims — no `sorry` at any of them

| # | Claim | Refuted by |
| -- | ---- | ---------- |
| 1 | `Colimit.Theorem29Second` | `R45.Agent3.not_thm29Second` |
| 2 | `R45.Agent3.Theorem29NormalWithoutDomain` | `R45.Agent3.not_thm29NormalWithoutDomain` |
| 3 | `R49.Agent7.Theorem26Printed` | `not_thm26Printed_of_two_zero_arities` |
| 4 | `LemThirty.Lemma30` (carrier quantified) | `R46.Agent1.not_forall_lemma30` |
| 5 | `PRep.Lemma28` (carrier quantified) | `R45.Agent2.not_forall_lemma28`, `_bcd`, `not_lemma28_flatEmpty` |

Rows 4 and 5 are refuted only with the carrier quantified; at the paper's own
carriers, `Lemma30AtV` is open and `Lemma28AtU` is proved.

`R46.Agent2.HasNormalRealizations` is a **concept** — Gunter 1987 Theorem 25's
hypothesis on `V`, a property of a poset — so it is in neither table, but the
instance the development wanted is refuted by
`R47.Agent1.not_hasNormalRealizations_Ainf` at `A∞`.

## 4. The detector fix, and the corrected count

`scripts/a6-query.lean` computed the transitive `sorryAx` cone over package
constants and **excludes any theorem in it from `proofs`, `uncond`, `PROVEDBY`,
`refuted` and `REFUTEDBY`**. Reverse reachability to a fixpoint, package
constants only — Mathlib is elaborated first and cannot name a package constant,
so nothing outside `ScottDomains` enters the cone.

The test has to be transitive, not `SORRYUSER`'s direct one: a theorem applying a
sorried root names the root and not `sorryAx`. r0052 built no such theorem, but
the next round to prove something from a root would.

**Corrected undischarged count: 72** — unchanged from the baseline, which is the
right answer, because r0052 proved nothing.

The unfixed detector was measured at **70** in the two-root state earlier this
round: `Theorem29Normal` and `ScottHomCRecursive` had each left the list, each
discharged by its own `sorry`. Each root removes exactly its own claim and the
claims are distinct, so the three-root state would have read 69.

| # | `a6-summarize.py` section 3 | Unfixed, 2 roots (measured) | Fixed, 3 roots (measured) |
| -- | ------------------------- | --------------------------: | ------------------------: |
| 1 | Prop-valued defs, total | 120 | 120 |
| 2 | with no unconditional proof | 70 | **72** |
| 3 | package constants naming `sorryAx` | 2 | 3 |

`scripts/a1-r52-claims.txt` is the claims file rebuilt from this census —
13 names, the new spellings, no aliases — superseding `scripts/a6-claims.txt`.
Run against the fixed scan it reports `13 named, 2 refuted, 11 OPEN`, which
differs from the census's 8 open / 5 refuted for a reason worth recording rather
than smoothing: the `REFUTEDBY` record misses three of the five.

* `Colimit.Theorem29Second` and `R45.Agent3.Theorem29NormalWithoutDomain` — the
  refutations conclude `¬ Thm29Second` and `¬ Thm29NormalWithoutDomain`, the
  **r0050 aliases**, so the record attaches to the alias and not to the claim.
  This closes itself when r0050 phase 2 deletes the aliases and the elaborator
  points at each remaining reference.
* `R49.Agent7.Theorem26Printed` — the refutation is conditional on the signature
  having two 0-ary slots (which the paper's own `(2,0,0,0,0,0)` has), and
  `a6-query.lean`'s criterion is documented to admit only closed refutations,
  for the soundness reason its own docstring gives.

The census TSV is the authoritative split; the summarizer's is a lower bound on
refutations until the aliases go.

## 5. `docs/Status.md`

Table 4's second table now lists **three** unproven statements, each with the
Lean theorem that asserts it, replacing "All three reduce to two statements".
Table 5 reports Theorems **3** left with a `sorry` and the prose reads `sorry` 3,
`axiom` 0, since r0052 — with the rule stated: every unproved result is a
`theorem … := sorry`, so the unproven count *is* the `sorry` count. The header
line's "0 warnings" became "0 errors, 3 `sorry` warnings, 0 other warnings", and
the size figures were refreshed from `counts.sh` (46,442 lines, 2,122 theorems).
Existing form kept; no paragraphs added.

## 6. Artifacts

| # | Path | What |
| -- | --- | ---- |
| 1 | `analyses/claim-census.20260810-155203.agent1.tsv` | the 72, adjudicated, one reason each |
| 2 | `analyses/a6-env-r52.txt` | baseline env scan (120 / 72) |
| 3 | `analyses/a6-env-r52-after.txt` | final env scan, fixed detector (120 / 72, 3 `sorryAx` users) |
| 4 | `analyses/a1-r52-sorry-cone.txt` | transitive `sorryAx` cone — 3 constants |
| 5 | `analyses/a1-r52-consumers.txt` | the 49 conditional consumers, by hypothesis |
| 6 | `analyses/a1-r52-sigs.txt` | elaborated signatures of the claims and reductions |
| 7 | `scripts/a6-query.lean` | **changed**: a theorem in the `sorryAx` cone no longer discharges or refutes |
| 8 | `scripts/a1-r52-claims.txt` | claims file rebuilt from the census; supersedes `a6-claims.txt` |
| 9 | `scripts/a1-r52-sorry-cone.lean` | reverse reachability closure of `sorryAx` |
| 10 | `scripts/a1-r52-consumers.lean` | consumer count by claim assumed |
| 11 | `scripts/a1-r52-undischarged.py` | dumps the undischarged population `a6-summarize.py` only counts |
| 12 | `scripts/a1-r52-sigs.lean` | signature probe |
| 13 | `scripts/a6-context.py` | one-line fix: `PROPDEF` grew a tenth column in r0046 and the unpack still expected nine |
