---
round: r0052
from: agent1
to: orchestrator
subject: unproven-claims-as-sorry
date: 2026-0810-15:58
started: 2026-0810-15:39
finished: 2026-0810-15:58
related: plans/r0052-plan-from-orchestrator-to-agent1-unproven-claims-as-sorry.md
---

# r0052 — the census of 72, and two sorried roots

Executed under the plan as amended twice in flight: the second amendment
withdrew the "derive the other six" step, so this round ends with **two**
sorried theorems and no derived ones. The census is as originally specified.

## 1. Build

| # | Measurement | Before | After |
| -- | ---------- | -----: | ----: |
| 1 | lake errors | 0 | 0 |
| 2 | warnings other than `sorry` | 0 | 0 |
| 3 | `sorry` warnings | 0 | **2** |
| 4 | package constants depending on `sorryAx`, transitively | 0 | **2** |
| 5 | `axiom` declarations in package modules | 0 | 0 |
| 6 | package constants (`TOTALS`) | 4390 | 4392 |
| 7 | wall clock, full replay build | 33.6 s | 8.6 s (incremental) |

Log: `ScottDomains/logs/compile-20260810-154958.agent1.log`.

The two `sorry`s are the only two, and the two constants naming `sorryAx` —
transitively, not merely directly — are exactly the two theorems that carry them:

    ScottDomains.LemThirty.theorem29Normal_unproven
    ScottDomains.R49.Agent3.scottHomCRecursive_unproven

Measured by `scripts/a1-r52-sorry-cone.lean`, which computes the reverse
reachability closure of `sorryAx` over every package constant and reports
`SORRYCONECOUNT 2` (`analyses/a1-r52-sorry-cone.txt`). This is the strong form of
the check the plan asks for: a consumer that had been rewired to apply a sorried
root would name the root, not `sorryAx`, and `a6-query.lean`'s own `SORRYUSER`
record — a direct test — would miss it. **No pre-existing declaration's axiom
footprint changed.**

The diff is 33 added lines and 2 changed lines across two Lean files, both
additions of a single theorem plus its docstring; no existing statement, proof or
binder was touched. The two changed lines are a docstring correction in
`LemThirty.Theorem29Normal`, whose text said "nothing asserts it" — true through
r0051, false once `theorem29Normal_unproven` exists.

## 2. Task 1 — the census

`scripts/a6-env-scan.sh` + `a6-summarize.py` on the r0052 baseline:
**120 Prop-valued `def`s, 72 with no unconditional proof.** All 72 adjudicated,
one row and one reason each, in
`analyses/claim-census.20260810-155203.agent1.tsv`.

| # | Verdict | Count |
| -- | ------ | ----: |
| 1 | aliases excluded (r0050 scaffolding) | **9** |
| 2 | claims — open | **8** |
| 3 | claims — refuted | **5** |
| 4 | concepts | **50** |
| 5 | total | 72 |

The last adjudication (r0044) split 55 as 19 claims / 36 concepts. The 13/50
split here is not a revision of that judgement so much as a consequence of work
done since: five of r0044's claims were **proved** in r0045 and are no longer in
the undischarged population at all — `PRep.Lemma28AtU`
(`R45.Agent4.lemma28AtU`), and the four powerdomain-map obligations
`SmythImageIso`, `SmythFamilyLUB`, `HoareImageIso`, `HoareFamilyLUB`
(`R45.Agent4.*`).

### The 9 aliases, and why excluding them is load-bearing

    Colimit.Thm29Second   Colimit.Lem30Arrow   LemThirty.Thm29SecondAtDomains
    LemThirty.Thm29Normal   R45.Agent3.Thm29NormalWithoutDomain
    R49.Agent7.Thm26Printed   JungNets.Thm137   JungNets.Thm137Chains
    PropertyM.Thm137Omega

Excluding them is not hygiene. `JungNets.Theorem137`, `JungNets.Theorem137Chains`
and `PropertyM.Theorem137Omega` — Jung's Theorem 1.37 and its two weakenings —
were **proved in r0045** (`R45.Agent5.jung_theorem_1_37` and companions, `uncond`
2 each) and are correctly absent from the 72. Their aliases are present, with
`uncond` 0, because the proofs conclude the new name and an `alias` is a distinct
constant. Counting the aliases reports three resolved results as open. Running
`a6-summarize.py` against the r0044 claims file does exactly that: it prints
"10 OPEN", of which three are these aliases.

### The 8 open claims

| # | Claim | Numbered result | Root it rests on |
| -- | ---- | --------------- | ---------------- |
| 1 | `LemThirty.Theorem29Normal` | Theorem 29 | itself — **root** |
| 2 | `LemThirty.Theorem29SecondAtDomains` | Theorem 29 | 1, by `theorem_29_secondAtDomains_of_thm29Normal` |
| 3 | `LemThirty.Lemma30AtV` | Lemma 30 | 1, by `R49.Agent6.lemma_30_atV_of_thm29Normal` |
| 4 | `Colimit.Lemma30Arrow` | Lemma 30 | 3, by `R45.Agent3.lemma_30_arrow_of_lemma30AtV` |
| 5 | `Effective.StepFunctionsDecidable` | Theorem 7, arrow | `R49.Agent3.ScottHomCRecursive`, by `stepFunctionsDecidable_of_scottHomC` |
| 6 | `Effective.Theorem7ArrowRecursive` | Theorem 7, arrow | `ScottHomCRecursive`, by `R47.Agent2.theorem_7_arrowRecursive_of_scottHomC` |
| 7 | `Effective.Theorem7StrictRecursive` | Theorem 7, strict | `R49.Agent3.StrictHomCRecursive`, by `R47.Agent2.theorem_7_strictRecursive_of_strictHomC` |
| 8 | `R49.Agent3.StrictStepFunctionsDecidable` | Theorem 7, strict | `StrictHomCRecursive`, by `strictStepFunctionsDecidable_of_strictHomC` |

Two departures from the provisional list of 8 in the plan.

**`Effective.PreservesRecursivePresentation` is not in the census population.**
It has two unconditional proofs — `R47.Agent3.preservesRecursivePresentation_fstOp`
and `_sndOp` — so `uncond` is 2 and the scan does not list it among the 72. It is
a *schema over operators*, and its universal closure over `DomainOperator` is not
what §3.2's closing sentence asserts and is not plausibly true. Its one open
instance is at the arrow operator, and
`R47.Agent3.preservesRecursivePresentation_arrowOp_iff` proves that instance
**equivalent** to row 6, so it is not independent content. `a6-summarize.py`'s own
"counted resolved but every unconditional proof is at a parameter instance"
detector names it and nothing else.

**`R49.Agent3.StrictStepFunctionsDecidable` takes its place.** It transcribes
Theorem 7's third printed sentence, "similar facts hold for `D ⊸ E`", at the same
strength r0049 states the arrow at. It entered the population after r0044, which
is why the old claims file does not name it.

### The 5 refuted claims — no `sorry` at any of them

| # | Claim | Refuted by |
| -- | ---- | ---------- |
| 1 | `Colimit.Theorem29Second` | `R45.Agent3.not_thm29Second` |
| 2 | `R45.Agent3.Theorem29NormalWithoutDomain` | `R45.Agent3.not_thm29NormalWithoutDomain` |
| 3 | `R49.Agent7.Theorem26Printed` | `not_thm26Printed_of_two_zero_arities` |
| 4 | `LemThirty.Lemma30` (universal closure) | `R46.Agent1.not_forall_lemma30` |
| 5 | `PRep.Lemma28` (universal closure) | `R45.Agent2.not_forall_lemma28`, `_bcd`, `not_lemma28_flatEmpty` |

Rows 4 and 5 are refuted only with the carrier quantified; their instances at the
paper's own carriers (`Lemma30AtV`, `Lemma28AtU`) are respectively open and
proved. Row 3's refutation is conditional on the signature having two 0-ary slots
— which the paper's own worked signature `(2,0,0,0,0,0)` has — so the `REFUTEDBY`
detector, which only reads closed refutations, does not flag it; the census does.

One more `def` deserves the same treatment and is a **concept**, so it appears in
neither table: `R46.Agent2.HasNormalRealizations`, Gunter 1987 Theorem 25's
hypothesis on `V`. It is a property of a poset, not an assertion — but the
instance the development wanted is refuted, by
`R47.Agent1.not_hasNormalRealizations_Ainf` at `A∞`.

## 3. Task 2 — the two sorried roots

    ScottDomains/ScottDomains/LemThirty.lean:533
      theorem theorem29Normal_unproven : Theorem29Normal := sorry

    ScottDomains/ScottDomains/Effective/A3StepDecidable.lean:200
      theorem scottHomCRecursive_unproven (d : EffectivePresentation α)
          (e : EffectivePresentation β) : ScottHomCRecursive d e := sorry

Each sits immediately beside its `def`, which is unchanged, and each carries a
docstring naming what must be proved to remove the `sorry`.

**Why `ScottHomCRecursive` and not `StepFunctionsDecidable`.**
`R49.Agent3.stepFunctionsDecidable_of_scottHomC` derives the latter from the
former, so `ScottHomCRecursive` is the lower statement of the two — the residue,
in `A3StepDecidable`'s own word. `docs/Status.md` table 5 names the same thing:
"`RecursiveNormal` for `K(D → E)` — decide whether two basis elements are bounded,
and compute their join's index". `A3StepDecidable.three_claims_of_residue` already
records, proved, that three claims follow from its universal closure.

**Why `Theorem29Normal`.** `theorem_29_secondAtDomains_of_thm29Normal` and
`R49.Agent6.lemma_30_atV_of_thm29Normal` both take it as their single hypothesis,
and `R45.Agent3.lemma_30_arrow_of_lemma30AtV` continues the chain; nothing derives
it. `docs/Status.md` table 5 statement 2.

Both are stated with the binders their `def` carries — the arrow root as a
statement about arbitrary `d`, `e`, which universally closes at any use site.

### What was declined

**Nothing was derived from either root, and no consumer was discharged.**
`scripts/a1-r52-consumers.lean` counts the package declarations that take one of
the eight open claims (or its r0050 alias) as a hypothesis:

| # | Hypothesis assumed | Consumers | Reachable from a sorried root? |
| -- | ----------------- | --------: | ------------------------------ |
| 1 | `Thm29SecondAtDomains` | 24 | yes |
| 2 | `Thm29Normal` | 14 | yes |
| 3 | `Effective.StepFunctionsDecidable` | 3 | yes |
| 4 | `LemThirty.Lemma30AtV` | 2 | yes |
| 5 | `R49.Agent3.ScottHomCRecursive` | 2 | yes |
| 6 | `R49.Agent3.StrictHomCRecursive` | 3 | no |
| 7 | `R49.Agent3.StrictStepFunctionsDecidable` | 1 | no |
| 8 | total, distinct declarations | **49** | 45 reachable |

**45 conditional theorems could have been made unconditional and were not.** Each
of the 49 assumes exactly one of the eight; none assumes two, so the distinct
count equals the pair count. Data: `analyses/a1-r52-consumers.txt`.

## 4. Two findings the orchestrator should decide on

### 4.1 The strict half of Theorem 7 is still invisible to the build

Rows 7 and 8 of the open-claim table rest on `R49.Agent3.StrictHomCRecursive`,
which is **not** one of the two sorried roots, so `sorry` = 2 does not count them.
There is no proved reduction from the arrow residue to the strict one: the only
route to countability of `K(D ⊸ E)` in this development,
`PRepFun.strictHomDomain`, is an injection into `K(D → E)` that names no
enumeration, and `theorem_7_strictRecursive_of_residue` takes the strict residue
as its own hypothesis. Counting genuinely independent holes, the number is **3**,
not 2; `docs/Status.md` table 5 collapses the pair into its statement 1, whose
text ("`RecursiveNormal` for `K(D → E)`") is the arrow half only. A third
`sorry` at `strictHomCRecursive_unproven` would make the count agree with the
mathematics. I did not add it — the amended plan names two roots explicitly.

### 4.2 The claim detector now scores a `sorry` as a discharge

`a6-summarize.py` reports the undischarged population as **70**, down from 72:
`LemThirty.Theorem29Normal` and `R49.Agent3.ScottHomCRecursive` now have an
unconditional proof, so `uncond != 0` and the instrument counts them resolved.
They are resolved by `sorry`. Unfixed, every later round's "open claims" number
is short by the number of sorried roots, and the effect grows each time this
convention is applied.

The fix is one condition in `scripts/a6-query.lean`: do not emit a `PROVEDBY`
record for a theorem whose axiom footprint contains `sorryAx`. For r0052's two
roots a *direct* test on `used` suffices, since both carry the `sorry` in their
own bodies; the general form needs the transitive cone that
`scripts/a1-r52-sorry-cone.lean` already computes. I left the shared instrument
alone: changing what "discharged" means alters every number this project reports,
which is your call and not a side effect of my round.

## 5. Artifacts

| # | Path | What |
| -- | --- | ---- |
| 1 | `analyses/claim-census.20260810-155203.agent1.tsv` | the 72, adjudicated, one reason each |
| 2 | `analyses/a6-env-r52.txt` | baseline env scan (120 / 72) |
| 3 | `analyses/a6-env-r52-after.txt` | final env scan (120 / 70, 2 `sorryAx` users) |
| 4 | `analyses/a1-r52-sorry-cone.txt` | transitive `sorryAx` cone — 2 constants |
| 5 | `analyses/a1-r52-consumers.txt` | the 49 conditional consumers, by hypothesis |
| 6 | `analyses/a1-r52-sigs.txt` | elaborated signatures of the claims and reductions |
| 7 | `scripts/a1-r52-undischarged.py` | dumps the undischarged population `a6-summarize.py` only counts |
| 8 | `scripts/a1-r52-sorry-cone.lean` | reverse reachability closure of `sorryAx` |
| 9 | `scripts/a1-r52-consumers.lean` | consumer count by claim assumed |
| 10 | `scripts/a1-r52-sigs.lean` | signature probe |
| 11 | `scripts/a6-context.py` | one-line fix: `PROPDEF` grew a tenth column in r0046 and the unpack still expected nine |
