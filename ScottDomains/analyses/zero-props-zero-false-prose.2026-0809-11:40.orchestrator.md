# r0046 — the two standing goals, measured

Five agents. Build **1356 jobs, 0 errors, 0 warnings, `sorry` 0**, no `sorryAx`,
composition check clean across five namespaces.

## Both metrics were defective, and both are fixed

Two streams independently found that the naive metrics **go up when the work goes
well.** Neither agent touched the instrument; both returned the question.

| # | Goal | Defect | Fix |
| -- | --- | ------ | --- |
| A | zero `Prop`s naming a theorem | a **refutation** produces `¬ Foo`, not `Foo`, so a claim *proved false* still scored as undischarged; and reducing an open problem to a named input **adds** `Prop`s | `a6-summarize.py` now reports `refuted` as a third status with its refuting theorems, and flags resolutions that hold only at a **parameter instance** |
| B | zero prose claiming to be proof | the no-deleting-history rule makes a correction **quote** the sentence it fixes, so the raw sweep went **230 before** four corrections and **231 after** | measure against `analyses/a5-r46-adjudicated.tsv`, never against candidate counts |

Recording this because it is the round's most reusable lesson: **a metric that
counts occurrences of a defect pattern will count the description of the fix.**

## Goal A: 10 → 7

Re-derived on the merged tree, not on any branch and not by subtraction.

| # | Status | Count | Claims |
| -- | ---- | ----: | ------ |
| 1 | **refuted — resolved** | **3** | `Colimit.Thm29Second`, `PRep.Lemma28`, `LemThirty.Lemma30` |
| 2 | open | 7 | `Lem30Arrow`, `StepFunctionsDecidable`, `Theorem7ArrowRecursive`, `Theorem7StrictRecursive`, `Lemma30AtV`, `Thm29SecondAtDomains`, `Thm29Normal` |

**Strictly, 8.** `Effective.PreservesRecursivePresentation` is scored resolved but
every unconditional proof is at a **parameter instance** (`γ := α`,
`γ := Flat ℕ`) — the second vacuity mechanism, in the quantifier structure rather
than a field type. agent1 left the headline at 7 for comparability with the
baseline and flagged the difference rather than burying it. Fixing that row needs
a `def` change no stream was authorized to make.

**The plan's "10 → 6" was not attainable and agent1 said so.** Rows 1–3 are
bookkeeping and give 10 → 7; row 6 was a statement fix, and **a fixed statement is
still an open statement**.

### Row 3 was not bookkeeping after all

`Lemma30`'s universal closure had been argued in prose across two rounds and
never proved false. `R46.Agent1.not_forall_lemma30` proves it.

### `StepFunctionsDecidable`: restated, not discharged

Restated to the sentence printed on p. 12 — `IsRecursive d → IsRecursive e →
IsRecursive (scottHom d e)`. The old statement is kept verbatim as
`StepFunctionsDecidableUnconditional`, and **`stepFunctionsDecidable_of_unconditional
: old → new` is the kernel's check that the change did not lower the bar.** That
is the right way to make a specification change: the direction of the weakening
is itself a theorem.

## The two open problems collapsed to one lemma each

**`Thm29Normal` was never blocked on [Gun87].** The mathematics is published in
`papers/Gunter 1987 Universal Profinite Domains.pdf` §5, pp. 16–23 — Prop. 21,
Thm. 22, Lemmas 23–24, Thm. 25, Cor. 26, with proofs — and the p. 23 remark
identifies Gunter's `A⁺` with Scott's `M(A)`. **`BifiniteUniversal.lean:47`
already cites that exact page**, for the construction; the same section carries
the universality proof. A second copy is Gunter's CMU dissertation, whose file is
misnamed `Gunter 1985`.

agent2 stated the missing input as `HasNormalRealizations` and proved
`thm29Normal_of_hasNormalRealizations` — **`Thm29Normal` used exactly as stated,
no added instance binder** — plus `isRoot_singleton_bot` discharging Theorem 25's
other hypothesis outright, and `not_hasNormalRealizations_unit` checking the
property is not satisfied by everything. Residue: **one statement**, Gunter's
Lemma 24 at `M(A)`, with a published proof in hand.

**`StepFunctionsDecidable` is blocked on domain theory, not recursion theory.**
agent3 reported two recursion-theoretic obstructions; agent1 measured both
against the installed Mathlib and found **both real and neither blocking**.
`Nat.bitwise`/`lor`/`testBit` co-occur with `Primrec`/`Computable` in 0 files —
but that blocks *constructing* a recursive presentation of `P N`, which the rows
assume rather than build. `REPred` has 7 declarations and no closure lemma — but
the rows are `ComputablePred` throughout and name `REPred` nowhere.

What actually blocks it is **one fact**: deciding `IsCompactElement (ofPairs Q)`,
whether a finite set of step functions named by index pairs is bounded above. The
arrow, the strict arrow and Theorem 7's proof sentence are **one lemma away**.

## `K(D ⊸ E)` now exists, and the blocker was four lines

`R46.Agent3.strictHomEnum`, the paper's own enumeration by joins of strict step
functions, with `exists_strictHomEnum_eq` proving it exhausts the compacts — not
a re-indexing through `nonempty_effectivePresentation`. The recorded blocker was
overstated: `PRepFun.isStrict_of_le` composed with
`ScottHom.exists_finite_isLUB_of_isCompactElement`, **both already present**,
because that theorem returns step functions *below* the compact and anything
below a strict function is strict.

Also: only **one** of the three missing `PRep` schemes was actually missing —
r0045's agent4 discharged Smyth and Hoare in the same round, so the plan was
stale before it was written. agent3 verified by kernel rather than by reading,
built `rep_plotkin`, and **zero schemes remain**. `Lemma30AtV` goes from
`lemma30_of`'s arity 10 to arity 3.

## Goal B: the instruments now exist

### Prose asserting something is proved (agent4)

**8 false claims, all in live `.lean` docstrings**, precision **71.4%** hand-
checked over every verdict row. 6 corrected; 2 deferred to merge and applied by
the orchestrator.

**Seven of the eight were true when written.** Only `PRepFun.lean:385` was wrong
at commit time — and wrong by 66 lines *within its own commit*. Two were
falsified by a later commit **in the same round**.

**Goal B is a staleness problem, not a carelessness problem.** Nothing signals
it: no `sorry`, no build failure, no warning. It needs a recurring check, not a
one-time sweep.

The orchestrator's mid-round steer was measured and found wrong: the package-wide
tier returns **0 rows**, and the case cited to justify it would have been missed
at any radius, because its subject is a noun phrase naming no constant. Blindness
quantified rather than caveated: **52 absence claims with an unbackticked
subject**, 13 asserting the package lacks something.

### Necessity and impossibility claims (agent5)

**228 sites, 90.8% precision, 24 adjudicated: 5 false, 18 true, 1 refused.** Base
rate of falsity **20.8%**.

**The plan's premise was half wrong.** This sentence type is unswept but *not*
unreliable — prior rounds found seven false ones because they stumbled onto false
ones; the true ones were never counted. The 18 confirmations are the larger half
of the value.

**An instrument defect that would have faked the whole result**:
`ConstantInfo.value?` returns `none` for imported *theorems*, so the first
dependency probe answered `NOT-USED` for everything including the control; dep
counts went 508 → 2777 after `.thmInfo v => some v.value`. **A naive dependency
probe silently refutes every necessity claim with plausible numbers.** This is
the same family as r0044's `allowOpaque` defect — twice now, reading proof bodies
from the environment has produced confident zeros.

**Grade upgrade**: r0044 confirmed necessity at grade C — "my reproof failed",
a statement about the prover. Three are now grade A: the hypothesis-free
statement is *refuted by counterexample*, kernel-checked.

**Class U — 103 of 230 — is mostly undecidable by instrument.** "The only place
`X` is spent" is file- or proof-scoped, so a global reverse-dependency count is
the wrong denominator; agent5 **refused to convict** `JungBicomplete.lean:506`
despite measuring 11 users against a claim of one. Deciding class U needs a
**writing convention** — sentences naming their scope — not a better instrument.
That is a standards change and it is the orchestrator's.

Also corrected: Mathlib claims do **not** age worst — 10 of 11 adjudicated true,
the one failure being incomplete search rather than drift.

## Prose fixes applied at merge

Three were deferred because the refuting constant lived on another branch —
agent4 declined to cite what was not in its own environment, which is exactly the
defect that stream removes.

1. `Effective/FunctionSpace.lean` — "This development has no strict-step-function
   basis"; replaced with the r0046 construction and the four-line reason.
2. `PRepFun.lean:664` — "`SmashObstruction` below names this as a `Prop`". **No
   such declaration has ever existed.** Found by r0044 twice and r0046 once
   before removal here.

## Package state

| # | Measure | r0045 | r0046 |
| -- | ----- | ----: | ----: |
| 1 | jobs | 1344 | **1356** |
| 2 | `sorry` / `axiom` / `sorryAx` | 0 / 0 / 0 | **0 / 0 / 0** |
| 3 | Goal A open | 10 | **7** (8 strict) |
| 4 | environment constants | 3,801 | 3,908 |
| 5 | environment theorems | 1,960 | 2,009 |
| 6 | `Prop`-valued defs | 90 | 95 |
| 7 | structures never instantiated | 0 of 22 | **0 of 23** |

## Residue, and which of it is a genuine open problem

| # | Item | Kind |
| -- | ---- | ---- |
| 1 | Gunter's Lemma 24 at `M(A)` | **published proof in hand** — transcription work, not research |
| 2 | deciding `IsCompactElement (ofPairs Q)` | one domain-theoretic lemma; closes 3 rows |
| 3 | `PreservesRecursivePresentation`'s `γ` | mis-stated; needs a `def` change |
| 4 | `Lemma30AtV` conjuncts 1–2 | blocked on removing `[BoundedComplete β]` from `lem17_fun` — `ClosureProperties.lean:54` calls this "a real open item" |
| 5 | 183 unadjudicated necessity sites, 52 unbackticked absence claims | instrument residue |
| 6 | class U, 103 sites | needs a writing convention first |

**Nothing in Goal A is now a genuine open problem in the research sense.** Item 1
is transcription from a paper we own; item 2 is a single lemma; items 3–4 are
known and named. The only true unknown left is item 4's `[BoundedComplete β]`,
which the development itself flagged as open before this round.
