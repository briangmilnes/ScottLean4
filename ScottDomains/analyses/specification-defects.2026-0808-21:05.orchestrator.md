# r0044 — the three unmeasured defect classes, measured

Eight agents, read-only, no `.lean` file edited. Every class this round attacked
was previously a **discovery count** — a tally of things found while looking for
something else — reported as though it were a measurement. All four now have an
instrument and a number.

## The headline: every prior figure was wrong, in both directions

| # | Class | Was | Now | Direction |
| -- | ---- | --: | --: | --------- |
| 1 | under- or incorrectly specified (`S≠`) | 18 | **13** | 5 were correct work, not defects |
| 2 | vacuously specified | ≥2 | **6** | 4 new, all from one stream |
| 3 | undischarged `def`s | ≥1 | **19** | 19× under-reported |
| 4 | artifacts asserting false things | 7 sites | **218 name sites + 7 claims** | 31× under-reported |

Classes 3 and 4 were under-reported because nobody had swept. Class 1 was
**over**-reported because a merged label was read as a defect count. Both errors
are the same error: a number produced as a by-product of other work, quoted as
though produced on purpose.

## Class 1 — the 18 `S≠` rows split (agents 1, 2)

| # | Kind | agent1 (§2–§4) | agent2 (§5–§7) | Total |
| -- | ---- | --: | --: | --: |
| 1 | under-specified | 3 | 9 | **12** |
| 2 | incorrectly specified | 0 | 1 | **1** |
| 3 | deliberately divergent — correct work | 2 | 3 | **5** |
| | rows | 5 | 13 | **18** |

**Defects attributable to us: 13 of 18.** The plan assigned 9 and 9; both agents
independently re-derived the real split as 5 and 13, agreeing exactly.

**The structural finding: 9 of the 12 under-specified rows are the added-binder
shape**, not the missing-conjunct shape. r0040 and r0043 were both hunting
missing conjuncts. The dominant defect mode in this development is **stating the
paper's conclusion under stronger hypotheses than the paper assumes** — which
reads as faithful transcription until you compare binders. Only agent4's p16 is a
missing conjunct.

## Class 2 — vacuity (agents 3, 4, 5)

| # | Stream | Area | Vacuous | Over-hypothesized |
| -- | ----- | ---- | ------: | ----------------: |
| 1 | agent3 | `Effective/`, `Kleene/`, `Isomorphism/`, `Skeleton/` | 2 (both already known) | 8 |
| 2 | agent4 | `Flat*`, `Powerdomain*`, `ContinuousAlgebra` | 0 | 12 |
| 3 | agent5 | `IdealCompletion`, `Universality`, `PropertyM`, `Thm18`, … | **4 (all new)** | 6 |
| | **total** | | **6** | **26** |

The 26 over-hypothesized declarations are reported separately and **must not be
added to the vacuity count**: they prove *more* than they claim, which is the
opposite sign of the defect. All three streams held that line independently.

### Why the obvious instrument fails twice

1. **`#lint only unusedArguments in ScottDomains` reports "0 errors in 0
   declarations"** — a false pass. `ScottDomains.lean`, the package root,
   imports five Mathlib modules and **none of the 100 submodules**, so
   `import ScottDomains` loads none of our declarations. **Three agents hit this
   wall independently** (3, 4, 7) and a fourth (5) logged it. This is a live
   defect in its own right: anyone importing our package gets Mathlib and
   nothing else.
2. **`unusedArguments` exempts binders whose name starts with `_`** — and both
   known-vacuous instances are named `_d` and `_e`. **Used alone, the linter
   finds zero vacuous theorems in this package.**

Note the exact inversion between two streams, both correct: agent2 established
that an underscore name is **not** evidence a binder is unused; agent3
established that the linter's underscore **exemption hides** genuinely unused
ones. Any instrument here must read occurrence, never names.

### Three instruments, three different defects

| # | Instrument | Finds | Blind to |
| -- | --------- | ----- | -------- |
| 1 | `#lint unusedArguments` | hypothesis never mentioned in the proof term | `_`-prefixed binders; anything used |
| 2 | agent5's `a5-freehyp` | hypothesis **used but free** — derivable from the others | hypotheses that are genuinely needed by *this* proof |
| 3 | deletion + reproof (`a4-delete`, `a1-probe45`) | hypothesis **used and not free, but unnecessary** — another proof does without it | nothing, but costs a reproof per candidate |

Instrument 2 is what found all four new vacuous theorems, and instrument 1
structurally cannot: there the hypothesis *is* used and merely free.
agent3's tool excludes `Prop`-valued classes, and `Domain` is one, so it would
have missed agent4's headline entirely. **The three are complementary, not
redundant** — a stream running only one reports a clean-looking zero.

### The four new vacuous theorems (agent5)

`EffectivePresentation.countable_compacts` — agent3's handoff lead, confirmed;
its own docstring concedes it, and it re-proves from `[Domain α]` with **no
axioms**. Then `ClosureProperties.lemma17`, `lem17_strictFun` and
`exists_finite_projection_fixing`, whose `IsBifinite β` is free because the added
`[BoundedComplete β]` together with `[Domain β]` supplies it via `prop15`.

### Class 2b-ii remains unmeasured

Used-but-unnecessary: **4 decided by reproof** (agent4), **38 candidates
undecided**, and agent5 reports **no number** for its area rather than a
misleading one. This class is strictly larger than the other two and only
reproof reaches it.

### Theorem 18 survives scrutiny

`thm18 : ∀ {α} [CompletePartialOrder α] [Domain α] [Domain (ScottHom α α)],
IsBifinite α`, axioms `[propext, Classical.choice, Quot.sound]`, no `sorryAx`.
`PropertyM`'s 1008 lines show zero unused-hypothesis hits and zero free `Prop`
hypotheses beyond `thm18_of_cor136`'s `hcor`, which the library discharges at
`Skeleton/Section6.lean:219`. `hAlgF` and `hCount` are load-bearing under both
instruments, backed by a **negative control**: `IsAlgebraic` has eleven
hypothesis-free providers and `hAlgF` was tested against all eleven and rejected.

The plan's `IdealCompletion` `dite` lead is a **negative result** — the guard is
satisfiable and satisfied wherever used; the `⊥` branch is totality, not vacuity.

### Zeros that are measurements

agent4's 0-of-427 is backed by four controls: 3-of-3 recovery of r0038's known
cases, exact agreement with agent3's independently written instrument on 7 dead
binders, 0 underscore-prefixed binders in the area, and a negative control
(`thm11_hoare` without `[Domain D]` correctly fails). agent5's structure census
found **zero** `Classical.dec`-inhabitable structures in its area — the
mechanism lives only in agent3's `EffectivePresentation`.

## Class 3 — undischarged `def`s (agent 6)

**19, not ≥1.** All are `Prop`-valued `def`/`abbrev`s stating a result of Gunter
& Scott or of Jung with no theorem discharging them. `StepFunctionsDecidable` is
one of nineteen.

**It is a documented convention, not an accident.** `LemThirty.Thm29Normal`'s
docstring states it: *"Recorded as a `Prop` rather than a `sorry` … the statement
is fixed and citable, and nothing asserts it."* So the `sorry` 0 headline has a
systematic 19-claim blind spot **by design**, and the design was never recorded
anywhere a count would find it.

Six of the 19 carry a nonzero "proved by" count; every such theorem is a
**reduction, not a proof** — `PRep.Lemma28AtU` has three theorems concluding it,
assuming 2, 4 and 5 hypotheses respectively.

agent6 declined the inflated number available to it: 88 `Prop`-valued defs, 55
with no unconditional proof, split **19 claims / 36 concepts**.

| # | Census | Result |
| -- | ----- | ------ |
| 1 | `axiom` declarations | **0**, two independent instruments; zero `sorryAx` |
| 2 | structures never instantiated | **0 of 22** (min constructor refs 1, median 2) |
| 3 | `Prop`-defs with no consumer at all | 5 |
| 4 | `@[simp]` tags | **194**, not the 197 this orchestrator quoted |
| 5 | `@[simp]` lemmas that provably never fire | **13** |

On row 5: agent6 split on `Meta.isRflTheorem` and **claims nothing** about the 78
`rfl`-theorems, because `dsimp` leaves no proof term and the method is
inconclusive there.

## Class 4 — artifacts asserting false things (agents 7, 8)

### Mechanical half: 218 defect sites, 126 distinct names, 258 files

| # | Kind | Sites | Precision (audited) |
| -- | ---- | ----: | ------------------: |
| 1 | wrong-module-qualifier — exists, cited under module path not namespace | 113 | **41/41 = 100%** |
| 2 | nonexistent — no such declaration, ours or Mathlib | 93 | 15/27 = 56% |
| 3 | wrong-qualifier — matches neither | 12 | 1/5 = 20% |
| — | absence-claim — cited *to say it is absent* | 85 | **not counted** |

**40 sites are in live `.lean` docstrings**, precision **91.7%** measured by
hand-checking all 48 `.lean` sites exhaustively. New finds: `Dyadic.lean:45–47`
is a docstring table naming **three instances, none of which exists**;
`Colimit.lean:59` cites `etaChain_not_wellDefined` and **no `etaChain` anything
exists in the environment**; `PRepFun.lean:662` points at "`SmashObstruction`
below", which has no referent.

**Root cause worth keeping: a module path is not a namespace.**
`ScottDomains/ClosureProperties/*.lean` declares into `ScottDomains`, not
`ScottDomains.ClosureProperties`. Anyone citing from a file path gets it wrong.
The orchestrator's r0043 checker matched on a name's **last component** and so
passed every one of these — its "no cited name fails to exist" was weaker than
stated. agent7 replaced the mechanism rather than patching it, taking the name
universe from the **elaborated environment** (770,249 constants, 3,691 ours) and
matching fully-qualified names on component boundaries, which kills three of
r0043's four false-positive sources by construction.

### Reading half: 7 false claims, 4 in live `.lean` docstrings

1. `Powerdomain/BoundedComplete.lean:321` — claims both of `lem13_smyth`'s
   hypotheses are consumed; `[Domain α]` is not. **The file contradicts itself
   eight lines later at `:329`**, which is the correct sentence.
2. `PRepFun.lean:658` — claims `Domain (D ⊗ E)` does not exist and names
   `SmashObstruction`. False twice: `smashDomain` is proved **334 lines below in
   the same file**, and `SmashObstruction` exists nowhere.
3. `FlatPowerdomain.lean:549` — docstring claims a directed-supremum conjunct the
   statement lacks.
4. `PowerdomainMap.lean:18` — a "nine variants returned zero hits" survey,
   falsified by `PowerdomainMap.map` at `:167` **of the same file**.

**11 claims were checked and found true**, including "Mathlib has no
`OrderIso.prodCongr`" (`#check` → unknown constant). Selection precision **7 of
19 verified = 36.8%**, stated rather than implied.

**Four of the seven are claims about whether a hypothesis is necessary** — the
same shape as Class 1's dominant defect, found by three independent streams.
`Kleene/Uniform.lean:39` calls a hypothesis "indispensable" and the deletion
probe **failing** confirms it, so the probe decides this prose in both
directions. It should be the standard instrument for the shape.

## `PaperInventory.md` row 3: the wrong number is 91

146 and 60 are both right. **91 is the numbered-results count** — "91 of 93
numbered conjuncts are stated" — transcribed into the prose row. Two independent
proofs: the parenthetical justifying it sums to 146, not 91; and prose-proved is
**70** while prose-stated-in-any-form is 86, so 91 exceeds the maximum possible
by 5.

**A worse defect sits underneath:** the categories are non-complementary.
`S+H`, `S≠` and `P` account for 16 prose rows between "proves" and "unstated", so
`146 − proved = unstated` is **unsound for any numbers**. The arithmetic was
never going to close.

## Corrections to the orchestrator and the plan

1. The plan's 9-and-9 Class 1 split was wrong; the real split is 5 and 13.
2. The orchestrator's r0043 citation checker under-reported by matching last
   components only.
3. The orchestrator quoted **197** `@[simp]` tags; the measured figure is **194**.
4. The powerdomain-map claim is at `PaperInventory.md:586`, **not row 554** —
   554 is the Lemma 13 row. Every "row 554" citation in the r0040 and r0043
   reports points at the wrong row.
5. The plan's lines 143–144 are wrong on both halves.
6. The plan's Class-2 definition merges two defects needing different tools.
7. r0043's agent1 moved row 45 to `S+P`; the added hypothesis keeps it `S≠`.
8. `PaperInventory.md` row 2c and `Combinator.lean:60` assert Theorem 26 is false
   at arity 0. **Not established** — the argument refutes the paper's *proof* at
   arity 0, not the theorem, since two one-point algebras are isomorphic to the
   same one-point subalgebra. That row is a defect of ours, not a repair.
9. `PaperInventory.md` row 569 qualifies Lemma 17 as over-hypothesized on two
   conjuncts; it should name **five**.

## Three counts that must never be reconciled

| # | Figure | Counts |
| -- | ----- | ------ |
| 1 | 1,773 | source `theorem`/`lemma` openers (`counts.sh`) — the size metric |
| 2 | 1,869 | environment theorems — adds `Prop`-valued class instances |
| 3 | 3,691 | all package constants — adds defs, structures, projections, equation lemmas |

A document claiming any of these equals another is itself a false claim.

## Instrument defects found, for whoever writes the next one

1. `ConstantInfo.value?` returns `none` for theorems unless `allowOpaque := true`;
   without it every reference inside a proof is invisible, and `Domain` reports 0
   constructor references against nine declared instances.
2. `simp` names `L._simp_N` in proof terms, never the lemma.
3. `forallTelescopeReducing` unfolds `Prop`-valued `def`s, which made agent5's
   first cut blind to the entire `Thm18` family.
4. Restricting free-hypothesis providers to zero explicit binders makes the
   detector blind to `nonempty_effectivePresentation` itself.
5. Testing `trivial` in the full telescope yields 267/427 pure noise, because
   `trivial` ends in `assumption`; test in the preceding context only.

## Measurement discipline

Counts identical at start and end: **100 modules, 37,300 lines, 1,773 theorems,
`sorry` 0 in 0 files**, build 1,339 jobs, 0 errors, 0 warnings. Eight-way octopus
merge, zero conflicts. Every agent verified the build before reporting.
