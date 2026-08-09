---
round: r0044
from: agent6
to: orchestrator
subject: undischarged-defs
date: 2026-0808-17:45
started: 2026-0808-17:05
finished: 2026-0808-17:45
related:
  - plans/r0044-plan-from-orchestrator-to-orchestrator-specification-defects.md
---

# r0044 — Class 3: claims stated as definitions, and the axiom census

## Headline measurements

| # | Measurement | Value |
| -- | ----------- | ----: |
| 1 | `axiom` declarations in the 100 package modules | **0** |
| 2 | package constants naming `sorryAx` | **0** |
| 3 | `Prop`-valued `def`/`abbrev` declarations | 88 |
| 4 | of those, with no unconditional proof anywhere | 55 |
| 5 | of those 55, **claims** — a stated result nobody proved | **19** |
| 6 | of those 55, concepts — predicates defined in order to quantify over them | 36 |
| 7 | `Prop`-valued definitions no other constant mentions at all | 5 |
| 8 | `Prop`-valued definitions never concluded and never assumed | 16 |
| 9 | `structure`/`class` declarations never instantiated | **0 of 22** |
| 10 | `@[simp]`-tagged declarations | 194 (the plan says 197) |
| 11 | of those, no proof term in the package names them | 91 |
| 12 | of those 91, provably never fired | 13 |

The plan's Class 3 entry reads "undischarged `def` — stated, unproved, not a
`sorry` — ≥1". The measured figure is **19**, and `StepFunctionsDecidable` is one
of them. Nineteen results of Gunter & Scott and of Jung are written into this
package as propositions with nothing asserting them, and the `sorry` count of 0
sees none of them, because a `def` carries no proof obligation — a definition
always elaborates.

Build and size are unchanged: `scripts/counts.sh` gives 100 modules, 37300
lines, 1773 theorems, `sorry` 0; `scripts/compile.sh -r r0044` gives 1339 jobs,
0 errors, 0 warnings (`ScottDomains/logs/compile-20260808-173733.agent6.log`).
No `.lean` file under `ScottDomains/ScottDomains/` was edited.

## The instrument

`scripts/a6-query.lean` is a metaprogram run against the **built environment**,
not against source text. It lives outside `ScottDomains/ScottDomains/`, so it is
invisible to `lake build` and to `counts.sh`. `scripts/a6-env-scan.sh` generates
one `import` line per package module, concatenates the metaprogram, and runs
`lake env lean` on the result.

The reason it cannot be a grep: the question "is this definition a stated claim"
is "does its type, after stripping binders, end in `Prop`", which is a property
of the *elaborated* type; and the follow-on question is not lexical under any
reading at all:

> `D` is discharged **iff** some package theorem's type, after stripping every
> leading binder, is headed by the constant `D` **and** that theorem assumes no
> proof hypothesis of its own.

The second conjunct is what separates a proof from a reduction, and dropping it
would have hidden six of the nineteen. `PRep.Lemma28AtU` has three theorems
concluding it — `PowerdomainMap.Rep.lemma28AtU_of''` (4 hypotheses),
`PRepSum.lemma28AtU_of` (5), `Lemma28AtU.lemma28AtU_of'` (2). Counting those as
discharges would report Lemma 28 at `U` as proved. It is not; it is reduced.

### Two defects found in the instrument itself, and what they cost

Both were caught by probing a case whose answer was known independently
(`scripts/a6-probe.lean`), and both are recorded because either one alone would
have produced a confident wrong number.

1. **`ConstantInfo.value?` returns `none` for a theorem** unless
   `allowOpaque := true` is passed (`Lean/Declaration.lean:485`). Every reference
   occurring inside a *proof* was therefore invisible. Since a `Prop`-valued
   class instance is stored as a theorem, this made `ScottDomains.Domain` report
   **0 constructor references** while the sources declare nine
   `instance … : Domain …`. Uncorrected, row 9 of the table above would have read
   "12 of 22 structures never instantiated", every one of them false.

2. **`simp` does not name the simp lemma in the term it builds**; it names an
   `Eq`-form auxiliary Lean derives when the tag is registered. Measured on
   `Flat.pset_fcOfSet`, whose script is `simp only [mem_pset, fcOfSet]`: the
   proof term names `Flat.mem_pset._simp_1` and `Flat.fcOfSet._proof_1`, and
   neither `mem_pset` nor `fcOfSet`. Uncorrected, row 11 read 92 rather than 91,
   and `mem_pset` — which demonstrably fires two lines below its own declaration
   — was on the dead list.

## 1. Axiom census — zero, confirmed twice

Two independent instruments agree.

* Lexical: `scripts/a6-scan.sh`, a comment-aware lexer over all 100 modules
  (`scripts/a6-decls.py`, which reuses `lean-decls.py`'s `strip_comments`, so a
  declaration inside a `/- … -/` block is not counted). 2513 declarations, of
  which `axiom`: **0**.
* Environment: `a6-query.lean` walks every constant whose module is
  `ScottDomains` or below and reports each `ConstantInfo.axiomInfo`. 3691
  package constants, 2639 of them written by hand. `axiom` records emitted: **0**.

The same pass emits a `SORRYUSER` record for any package constant whose type or
value names `sorryAx`. **0** records, corroborating `counts.sh`'s lexical
`sorry` count of 0 from the kernel side rather than from a regex over source
lines.

This says nothing about which of Lean's own axioms the development consumes —
that is `docs/AxiomFootprint.md`'s question, and a separate one. It says that
the development assumes nothing of its own by fiat.

## 2. The nineteen undischarged claims

Every one has `uncond = 0`: no package theorem concludes it without itself
assuming a hypothesis. `refs` counts source-level package constants mentioning
it; `hyps` counts constants taking it as a hypothesis.

| # | file:line | declaration | binders | refs | proofs | hyps |
| -- | --------- | ----------- | ------: | ---: | -----: | ---: |
| 1 | `Effective/FunctionSpace.lean:374` | `Effective.StepFunctionsDecidable` | 9 | 1 | 0 | 1 |
| 2 | `Effective/FunctionSpace.lean:390` | `Effective.Theorem7ArrowRecursive` | 0 | 0 | 0 | 0 |
| 3 | `Effective/FunctionSpace.lean:405` | `Effective.Theorem7StrictRecursive` | 0 | 0 | 0 | 0 |
| 4 | `Effective/FunctionSpace.lean:420` | `Effective.PreservesRecursivePresentation` | 11 | 0 | 0 | 0 |
| 5 | `PRep.lean:252` | `PRep.Lemma28` | 2 | 3 | 1 | 0 |
| 6 | `PRep.lean:284` | `PRep.Lemma28AtU` | 0 | 3 | 3 | 0 |
| 7 | `Colimit.lean:1028` | `Colimit.Thm29Second` | 0 | 7 | 0 | 7 |
| 8 | `Colimit.lean:1038` | `Colimit.Lem30Arrow` | 0 | 0 | 0 | 0 |
| 9 | `LemThirty.lean:211` | `LemThirty.Lemma30` | 2 | 3 | 1 | 0 |
| 10 | `LemThirty.lean:260` | `LemThirty.Lemma30AtV` | 0 | 0 | 0 | 0 |
| 11 | `LemThirty.lean:277` | `LemThirty.Thm29SecondAtDomains` | 0 | 10 | 2 | 8 |
| 12 | `LemThirty.lean:464` | `LemThirty.Thm29Normal` | 0 | 4 | 0 | 4 |
| 13 | `PowerdomainMapRep.lean:102` | `PowerdomainMap.Rep.SmythImageIso` | 3 | 4 | 0 | 4 |
| 14 | `PowerdomainMapRep.lean:108` | `PowerdomainMap.Rep.SmythFamilyLUB` | 3 | 3 | 0 | 3 |
| 15 | `PowerdomainMapRep.lean:160` | `PowerdomainMap.Rep.HoareImageIso` | 3 | 4 | 0 | 4 |
| 16 | `PowerdomainMapRep.lean:165` | `PowerdomainMap.Rep.HoareFamilyLUB` | 3 | 3 | 0 | 3 |
| 17 | `JungNets.lean:308` | `JungNets.Thm137` | 2 | 11 | 1 | 9 |
| 18 | `JungNets.lean:319` | `JungNets.Thm137Chains` | 2 | 6 | 2 | 3 |
| 19 | `PropertyM.lean:750` | `PropertyM.Thm137Omega` | 2 | 4 | 2 | 2 |

Paths are relative to `ScottDomains/ScottDomains/`.

Six of the nineteen carry a nonzero `proofs` column, and every such theorem is a
reduction, not a discharge: rows 5 (`PRep.lemma28_of`, 9 hypotheses), 6 (three
theorems, 2 to 5 hypotheses each), 9 (`LemThirty.lemma30_of`, 10 hypotheses),
11 (`thm29SecondAtDomains_of_thm29Second`, `thm29SecondAtDomains_of_thm29Normal`,
1 hypothesis each), 17 (`Iwamura.thm137_of_thm137Chains`, 1), 18
(`PropertyM.Thm137Chains.toOmega` and `PropertyM.Thm137.toOmega`, 1 each). The
full list of 253 conclusion-to-theorem edges is in the `PROVEDBY` records of the
raw scan.

### Claim or concept: how the 55 were split

Of 88 `Prop`-valued definitions, 55 have no unconditional proof. Most of those
are **concepts** — `Flat.le`, `IsClosurePair`, `IsNonBotSum`, `IsOrdinalCodirected`,
`Plotkin.FinCompacts.le` — predicates the development defines so theorems can
quantify over them, for which "nobody proved it outright" is the correct state
and not a defect. Reporting 55 would have been the inflated number.

The split is a reading of each declaration's own docstring, which
`scripts/a6-context.py` extracts mechanically for all 55. It is recorded as data
in `scripts/a6-claims.txt`, one qualified name per line, so `a6-summarize.py`
reproduces the count of 19 and so a later round can dispute one entry rather than
the whole figure. Every entry's docstring states in the author's own words that
the statement is open — "**This is not proved.** No `sorry` stands in for it"
(`JungNets.Thm137`), "Unproved, and blocked twice over" (`Colimit.Lem30Arrow`),
"**Obligation 1 for `(·)♯`**" (`SmythImageIso`), "none is discharged"
(`PreservesRecursivePresentation`), and, most explicitly, `Thm29Normal`:
"Recorded as a `Prop` rather than a `sorry`, per this development's convention:
the statement is fixed and citable, and nothing asserts it."

That last sentence is the finding in one line. The convention is deliberate and
defensible — a `Prop` is citable and a `sorry` is not — but it means the
development's headline `sorry` count of 0 is not a measure of what is unproved,
and 19 is the number that measures it.

## 3. Structures never instantiated — zero of 22

All 22 `structure`/`class` declarations have at least one source-level package
constant naming their constructor. `ctorRefs` counts references from
hand-written constants only, with `_flat_ctor` and other auxiliaries normalized
onto the declaration they were generated for.

| # | file:line | declaration | ctorRefs | fields | Prop fields |
| -- | --------- | ----------- | -------: | -----: | ----------: |
| 1 | `ScottHom.lean:72` | `ScottHom` | 85 | 2 | 1 |
| 2 | `Domain.lean:128` | `Domain` | 18 | 2 | 2 |
| 3 | `UniversalDomain.lean:291` | `Cpo` | 16 | 2 | 0 |
| 4 | `Domain.lean:119` | `IsAlgebraic` | 15 | 2 | 2 |
| 5 | `BifiniteUniversal.lean:144` | `BifiniteUniversal.MPair` | 12 | 3 | 1 |
| 6 | `Powerdomain/Smyth.lean:150` | `Smyth.Basis` | 12 | 2 | 1 |
| 7 | `Domain.lean:168` | `BoundedComplete` | 11 | 1 | 1 |
| 8 | `ContinuousAlgebra.lean:633` | `ContinuousAlgebra.FinSets` | 3 | 11 | 7 |
| 9 | `JungSFP.lean:257` | `JungSFP.IsJungPatch` | 3 | 4 | 4 |
| 10 | `EffectivePresentation.lean:57` | `EffectivePresentation` | 3 | 5 | 2 |
| 11 | `ContinuousAlgebra.lean:184` | `ContinuousAlgebra.IsHom` | 3 | 2 | 2 |
| 12 | `UniformFixedPoint.lean:106` | `FixedPointOperator` | 2 | 2 | 1 |
| 13 | `Atomless.lean:233` | `Atomless.CountableBC` | 2 | 2 | 2 |
| 14 | `ContinuousAlgebra.lean:172` | `ContinuousAlgebra.IsLower` | 1 | 2 | 2 |
| 15 | `ContinuousAlgebra.lean:166` | `ContinuousAlgebra.IsUpper` | 1 | 2 | 2 |
| 16 | `ContinuousAlgebra.lean:157` | `ContinuousAlgebra.IsSemilattice` | 1 | 3 | 3 |
| 17 | `ContinuousAlgebra.lean:107` | `ContinuousAlgebra.Binop` | 1 | 2 | 1 |
| 18 | `FlatPowerdomain.lean:386` | `Flat.SmythCarrier` | 1 | 2 | 1 |
| 19 | `FlatPowerdomain.lean:876` | `Flat.PlotkinCarrier` | 1 | 2 | 1 |
| 20 | `FinitaryProjectionPoset.lean:410` | `IsMinimalUpperBound` | 1 | 4 | 4 |
| 21 | `Effective/FunctionSpace.lean:347` | `Effective.RecursivePresentation` | 1 | 3 | 2 |
| 22 | `Combinator.lean:193` | `Combinator.LambdaModel` | 1 | 8 | 3 |

**This is a negative result and it is a result.** The shape the plan asked
about — a structure field whose obligation is never discharged because nothing
ever builds the structure — does not occur in this package. The minimum is one
and the median is two.

What this measurement does **not** answer, and must not be read as answering: it
counts whether a structure is instantiated, not whether the instantiation is
*substantive*. `Effective.RecursivePresentation` has one constructor reference
and two `Prop`-valued fields; whether those fields are filled by real content or
by `Classical.dec` is Class 2's question, and agents 3, 4 and 5 own it. Rows 8,
9, 16 and 20 have the largest counts of `Prop` fields against the smallest
counts of instantiations and are the natural places for that stream to look.

## 4. Stated claims with no consumer

**Five** `Prop`-valued definitions are named by no other constant in the package
— not proved, not assumed, not mentioned in any statement or proof:

| # | file:line | declaration |
| -- | --------- | ----------- |
| 1 | `Colimit.lean:1038` | `Colimit.Lem30Arrow` |
| 2 | `Effective/FunctionSpace.lean:390` | `Effective.Theorem7ArrowRecursive` |
| 3 | `Effective/FunctionSpace.lean:405` | `Effective.Theorem7StrictRecursive` |
| 4 | `Effective/FunctionSpace.lean:420` | `Effective.PreservesRecursivePresentation` |
| 5 | `LemThirty.lean:260` | `LemThirty.Lemma30AtV` |

All five are on the list of nineteen. They are pure record: the statement is
fixed and citable and nothing in the package touches it. Row 4's docstring says
so directly — "Every operator of §§4–7 supplies another instance; none is
discharged." Row 5 is the one that surprises, since `LemThirty.Lemma30AtV` is
declared for the express purpose of pinning Lemma 30's carrier to `Colimit.V`
"so the instantiation cannot drift", and no declaration then uses it; its stated
model, `PRep.Lemma28AtU`, is referenced three times.

A weaker criterion — never a conclusion **and** never a hypothesis, though
possibly mentioned inside some other definition's body — holds of **16**:
the five above plus `Atomless.Legal`, `FpEmbedding.TwoMub.le`, `Flat.le`,
`Flat.omegaTest`, `Flat.SmythTrivial`, `JungSFP.HasTwoMubBelow`,
`JungSFP.HasAtMostOneMubBelow`, `Kleene.NatBot.le`, `Plotkin.FinCompacts.le`,
`Recursive.Solves` and `Recursive.IsCountablyBasedAlgebraicLattice`. Most of
that remainder is ordinary: an order relation reached through an `LE` instance
rather than by name is *used* without ever being a hypothesis. The two
`JungSFP` entries are worth agent 3's or 5's attention — both docstrings say
they exist to be the exact hypothesis shape `lemma213` and `lemma217` consume,
and neither is a hypothesis of anything.

## 5. Simp lemmas that never fire

There are **194** `@[simp]`-tagged declarations, not 197. Three instruments
agree on 194: `scripts/lean-decls.py --simp`, `scripts/a6-scan.sh`, and the
environment's own simp theorem set. The plan's 197 is wrong by three.

Of the 194, **91 are named by no proof term anywhere in the package**. A `simp`
call that rewrites with `L` puts `L` (or its `_simp_N` auxiliary) into the term
it builds, so a zero count means no proof in the package was built with that
lemma by any route — `simp`, `rw` or `exact`.

That inference has one exception, and it is large: a `rfl`-theorem may be applied
on `simp`'s definitional (`dsimp`) path, which rewrites without constructing a
proof at all and so leaves no trace. Splitting on `Meta.isRflTheorem`:

* **13 are not `rfl`-theorems and are named by no proof term. These never
  fired.** This is conclusive.
* 78 are `rfl`-theorems. Zero references is not evidence about them, and this
  report claims nothing about those 78.

The thirteen:

| # | file:line | declaration |
| -- | --------- | ----------- |
| 1 | `ContinuousAlgebra.lean:734` | `ContinuousAlgebra.mem_op` |
| 2 | `ContinuousAlgebra.lean:839` | `ContinuousAlgebra.mem_unit` |
| 3 | `FlatPowerdomain.lean:110` | `Flat.cpt_le_cpt` |
| 4 | `IdealCompletion.lean:125` | `IdealCompletion.mem_toIdeal` |
| 5 | `IdealCompletion.lean:127` | `IdealCompletion.mem_ofIdeal` |
| 6 | `JungBicomplete.lean:162` | `JungBicomplete.mem_wayBelowSet` |
| 7 | `JungBicomplete.lean:595` | `JungBicomplete.mem_wayBelowLower` |
| 8 | `LemThirty.lean:551` | `LemThirty.mem_embIdeal` |
| 9 | `LemThirty.lean:591` | `LemThirty.mem_projIdeal` |
| 10 | `Powerdomain/Plotkin.lean:105` | `Plotkin.FinCompacts.mem_carrier` |
| 11 | `PowerdomainCompacts.lean:161` | `PowerdomainMap.Compacts.mem_p` |
| 12 | `Skeleton/Section6.lean:96` | `mem_lubClosure` |
| 13 | `StepFunction.lean:100` | `ScottHom.step_self` |

Twelve of the thirteen are membership-unfolding lemmas of the same shape. One is
named at a live use site and still did not fire, which is the interesting case:
`ClosureProperties/Powerdomain.lean:299` writes
`simp only [← Plotkin.FinCompacts.mem_carrier, show w.carrier = v.carrier from h]`,
and the second element closes the goal on its own. `step_self` is also mentioned
once outside its declaration, at `StepFunction.lean:131`, but that line sits
inside a `/- … -/` block (closed at line 132) and is not code — the mention was
found by grep and then checked, which is why the count of live use sites is one
and not two. These thirteen are the candidates to delete, and deleting them is a
cheap independent check of this measurement: the build must stay at 1339 jobs, 0
errors.

Method note. The plan's suggestion of `set_option trace.simp` over a full build
was not used: the trace volume for 37300 lines is impractical and it would have
needed the package rebuilt under a modified option, which this round forbids.
`#lint`'s `simpNF` was not run either; it answers a different question — whether
a statement is malformed — and the reference-count method answers the question
asked, "which tags never fire", for 116 of the 194 conclusively (103 that fire,
13 that do not).

## Corrections to the plan and to other streams

| # | Where | Says | Measured |
| -- | ----- | ---- | -------- |
| 1 | plan, Class 3 row | undischarged `def` "≥1" | 19 |
| 2 | plan, Class 3 stream | "every `@[simp]`-tagged lemma … There are 197" | 194 |
| 3 | plan, Class 3 stream | axiom census "expected: zero" | zero, confirmed by two instruments |

One number that is **not** a correction but should not surprise a later reader:
the environment reports 1869 theorems where `counts.sh` reports 1773. The
difference is 96, and the package declares 103 `instance`s. A `Prop`-valued
class instance is stored as a theorem in the environment and is not a
`theorem`/`lemma` opener in the source, so the lexer cannot see it. Both numbers
are right about what they measure; `counts.sh`'s 1773 remains the project's
size metric.

## Reproduction

Four commands, in order. The first needs a built package.

```
scripts/compile.sh -r r0044
scripts/a6-scan.sh <outdir>                      # lexical census, 2513 decls
scripts/a6-env-scan.sh <outdir>/env.txt          # the environment scan
python3 scripts/a6-summarize.py <outdir>/env.txt --claims scripts/a6-claims.txt
```

Every count in this report is a line of `a6-summarize.py`'s output. To re-read
the evidence behind the claim/concept split:

```
python3 scripts/a6-context.py <outdir>/env.txt ScottDomains --only-undischarged
```

| # | Script | What it is |
| -- | ------ | ---------- |
| 1 | `scripts/a6-query.lean` | the metaprogram; not a package module |
| 2 | `scripts/a6-env-scan.sh` | generates the imports and runs it under `lake env lean` |
| 3 | `scripts/a6-decls.py` | comment-aware lexer for every declaration kind |
| 4 | `scripts/a6-scan.sh` | the lexical census |
| 5 | `scripts/a6-context.py` | docstring and signature for each undischarged definition |
| 6 | `scripts/a6-claims.txt` | the 19 claims, as data |
| 7 | `scripts/a6-summarize.py` | the tallies |
| 8 | `scripts/a6-probe.lean` | the one-question debug companion that caught both instrument defects |
