# r0045 — the 19 undischarged claims, after one round

Five agents, all writing `.lean`. Five new modules in five namespaces, **no
existing file modified** — a pure-addition merge. Build 1344 jobs, 0 errors, 0
warnings, `sorry` 0. Composition check passes: all five modules import into one
environment with no name clash, every headline result at
`[propext, Classical.choice, Quot.sound]`, no `sorryAx`.

## The measured number, and why it is not the honest one

Re-running agent6's detector over the built environment gives **10 undischarged
of 19**. That figure is reported first because it is the reproducible one, and
then corrected, because **the detector scores an added instance binder as a
discharge** — the same hole this orchestrator's acceptance criterion had, found
mid-round by agent5 and used by agent3 to sharpen two results.

| # | Outcome | Count | Claims |
| -- | ------ | ----: | ------ |
| 1 | **fully discharged** — conclusion is the claim, binders exactly the claim's own | **5** | the four `PowerdomainMap.Rep.*`, and `PRep.Lemma28AtU` |
| 2 | **refuted** — the claim is false as stated, kernel-checked | **2** | `Colimit.Thm29Second`, `PRep.Lemma28` |
| 3 | **discharged at `[Domain D]`** — real advance, general case still open | 3 | `JungNets.Thm137`, `Thm137Chains`, `PropertyM.Thm137Omega` |
| 4 | **vacuous, not a result** | 1 | `Effective.PreservesRecursivePresentation` |
| 5 | **reduced** | 2 | `Theorem7ArrowRecursive` (0 → 1 theorem, 1 hypothesis), `Lemma30AtV` (2 → 5 conjuncts) |
| 6 | **reclassified, row should be dropped** | 1 | `LemThirty.Lemma30` |
| 7 | **open** | 5 | `StepFunctionsDecidable`, `Theorem7StrictRecursive`, `Thm29Normal`, `Thm29SecondAtDomains`, `Lem30Arrow` |

**7 claims are resolved** (rows 1–2): five proved outright, two proved false.
Rows 3–5 are progress that must not be counted as resolution.

## The denominator was inflated: two schema/instance double-counts

`Lemma28` and `Lemma28AtU` are **one claim counted twice** (agent2): the sole
blocker at generic `U` is `UniversalForBCD U`, which is `PRepSum.pairAtU` at the
atomless `Dyadic.U`, and it is not obtainable as a typeclass.

`Lemma30` and `Lemma30AtV` are the same pattern (agent3, predicted independently
by agent2 from `LemThirty.lean:210`, which says it was written to mirror the
`PRep` cluster). `Lemma30` is a *parameterized family*, not a proposition, and
its universal closure is false; discharge would require binders exactly
`(W) [CompletePartialOrder W]`, and any proof must add one or fix `W := V`, at
which point it simply is `Lemma30AtV`.

So the real population was **17, not 19**.

## Two refutations, and neither convicts the paper

`Colimit.Thm29Second` is false at `E := Flat (Set ℕ)` — `not_thm29Second`. Gunter
& Scott write "`E` is any bifinite **domain**"; `Flat (Set ℕ)` is bifinite and is
not a domain. **Our Lean transcription dropped the word.** No tenth printed
defect; `StatementRecovery.md` stays at nine.

That is r0044's dominant defect mode running in reverse — not an *added* binder
narrowing a claim, but a *dropped* one widening it into falsity. It is the second
time in two rounds we came close to convicting the paper for our own
transcription error; Theorem 26 was the first.

`PRep.Lemma28` is false at `Flat Empty` — `not_forall_lemma28`, conjunct 7
failing on a cardinality count. agent2 then closed the escape hatch by proof:
`not_forall_lemma28_bcd` shows it stays false after adding `[Domain U]` **and**
`[BoundedComplete U]`, so **no "discharged at" route exists** — `Flat Empty`
satisfies every class in `Domain.lean`.

A third refutation was produced that is not one of the 19:
`not_thm29NormalWithoutDomain`. `LemThirty.lean:506` asserted that `Thm29Normal`
without `[Domain E]` "is refutable rather than open"; **nothing had proved it**,
and now something does. Both §7.4 claims are therefore **false at the binders the
paper does not assume, and open at the binders it does** — so
`Thm29SecondAtDomains` and `Thm29Normal` are not weakenings to be skipped past,
they are the only true readings, with the necessity of `[Domain E]` kernel-checked
at both.

## The construction that was the point of agent1's stream

**A genuine `RecursivePresentation` now exists** —
`R45.Agent1.natBotRecursivePresentation : RecursivePresentation (Flat ℕ)`, the
first instance ever built. Both conditions are `ComputablePred` witnesses from
`Primrec` combinators: condition 1 is `a = 0 ∨ a = b`, condition 2 is `0 ∈ u`
(in a flat cpo `↓x` is a chain, so normality collapses to "contains `⊥`"). Four
`example`s closed by `decide` check that the procedures actually run — which
`Classical.dec` cannot fake.

It does **not** make `powersetPresentation` recursive: `bitwise|lor|testBit` over
`Mathlib/Computability/` is still 0 hits, re-measured.

## A second vacuity mechanism, independent of `Classical.dec`

`Effective.PreservesRecursivePresentation` quantifies over a `γ` **unrelated to
`α` and `β`**, so `preservesRecursivePresentation_id` closes it in one line by
returning its own hypothesis. Its closure over `γ` is false by a counting
argument.

This matters beyond the row: the vacuity lives in the **quantifier structure, not
a field type**, so a reviewer checking only for `Classical.dec` — which is what
r0044 and this plan both told agents to check — would pass it. `docs/Structures
VsTypeClassesVsPropsInLean4.md` needs this second mechanism added.

## What blocks each open claim, named

| # | Claim | Missing input |
| -- | ---- | ------------- |
| 1 | `Thm29Normal` | a universal property of `M` among finite posets under normal embedding; nothing in `BifiniteUniversal.lean` concerns maps between two different bases. This is **[Gun87]'s content** — the paper requested from Gunter and never received |
| 2 | `StepFunctionsDecidable` | mis-stated: the paper says "using the effective presentations of `D` and `E`", the `def` quantifies over arbitrary `d`, `e`, and the universal closure is false. Refutation route named, **not kernel-checked, so not recorded as a result** |
| 3 | `Theorem7StrictRecursive` | everything the arrow needs, plus an enumeration of `K(D ⊸ E)` the development does not have |
| 4 | `Lemma28` at generic `U` | `UniversalForBCD U`, not obtainable as a class |

## Corrections to the orchestrator

1. **My acceptance criterion had a hole.** "Zero hypotheses beyond instance
   binders" admits an *added* instance binder, which is precisely r0044's
   dominant defect mode. Corrected mid-round to distinguish **discharged** from
   **discharged at `<binder>`**; agent3 immediately used it to find and close a
   real gap. The criterion must ship in this form.
2. **My "moved the obligation" framing of `lemma28AtU_of''` was wrong**, and two
   streams reversed it independently. The arity 2 → 4 restructure was correct:
   isolating the four is exactly what made them provable. agent2 rewrote its own
   draft after noticing it had repeated my reading.
3. **The plan's central lead for agent5 was wrong.** `Iwamura.HasWellOrderedInfima`
   has five occurrences, all consumers, **no producer** — Iwamura's lemma and
   Markowsky's theorem convert *between* completeness hypotheses and neither
   manufactures one. The cluster is "a complete reduction chain with an empty
   left end". What closed the three claims was `PropertyM.hasOmegaOpBoundsAbove_pair`
   — Spreen 2005's Lemma 5.8, one file away.
4. **The plan's lead for agent4 was unnecessary**: the general argument is
   shorter than the concrete `N⊥` one.

## Documentation defects found, continuing r0044's Class 4

1. `PowerdomainMapRep.lean:42` — "has to go through `IsProjection.isCompactElement_iff`"
   is false as a necessity claim; **found independently by agents 2 and 4**, neither
   of which edited the file because the other was citing it.
2. `LemThirty.lean:346` — "no algebraicity and no `Domain`" for Smash/CoalescedSum/
   SeparatedSum; `PRepFun.smashDomain` and `PRepSum.domain_coalescedSum` exist.
3. `LemThirty.lean:387` — says two of Lemma 28's nine schemes are proved; **seven** are.
4. `Effective/FunctionSpace.lean` — `RecursiveNormal`'s docstring says Mathlib has
   no `Primcodable (Finset ℕ)` so `ComputablePred` "cannot be asked of a predicate
   on `Finset ℕ` at all". False: `Primcodable.ofDenumerable` supplies it.

Items 1 and 4 are the same shape r0044 named as this development's least reliable
sentence type — a claim that some route or hypothesis is *required*. That count
is now seven across three rounds.

Items 2 and 3 were the stated reason for routing `⊗`, `+`, `⊕` through the
now-refuted hypothesis; six declarations lose it.

## Reclassification to fold in

`LemThirty.retracts_fun_of_boundedComplete` and `retracts_strictFun_of_boundedComplete`
are pre-existing **"reduced at `[BoundedComplete V]`"** — a hypothesis *and* an
added instance binder — and are now doubly vacuous: the hypothesis is refuted,
and `not_boundedComplete_V` shows the binder is incompatible with the weaker
hypothesis that would replace it.

## Package state

| # | Measure | Before r0045 | After |
| -- | ----- | ----: | ----: |
| 1 | jobs | 1339 | **1344** |
| 2 | `sorry` | 0 | **0** |
| 3 | `axiom` declarations | 0 | **0** |
| 4 | constants naming `sorryAx` | 0 | **0** |
| 5 | structures never instantiated | 0 of 22 | **0 of 22** |
| 6 | `@[simp]` tags | 194 | 196 |
| 7 | environment constants | 3,691 | 3,801 |
| 8 | environment theorems | 1,869 | 1,960 |

`scripts/a6-claims.txt` is now stale — the detector flags nine entries as "named
as claims but NOT undischarged". It should be rewritten to the r0045 statuses,
with `Lemma30` dropped and `Lemma28`/`Lemma28AtU` merged.
