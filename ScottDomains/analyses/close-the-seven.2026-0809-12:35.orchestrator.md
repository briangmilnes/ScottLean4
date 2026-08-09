# r0047 — the seven did not move, and that is the honest headline

Five agents. Build **1364 jobs, 0 errors, 0 warnings, `sorry` 0**, no `sorryAx`,
no `axiom`. Goal A re-derived on the merged tree: **7 open, 3 refuted, 8 strict.
Unchanged from r0046.**

**The number is unchanged and the round was not wasted.** Three of the seven now
mean something different, one binder came out of six declarations, and two of the
plan's four "this is transcription, not research" premises were wrong. This
document records what moved underneath a static count, because a coverage number
that cannot see this round is a number worth distrusting.

## What the plan got wrong

I wrote that **two lemmas close six of the eight** and that neither was research.
Both halves failed, in opposite directions.

### `Thm29Normal` — the target was empty

**Lemma 24 at `M(A)` is proved** — `R47.Agent1.lemma24_MPair`, kernel-checked,
for an arbitrary poset, with `lemma24_Step` and `isNormalIn_eta_image_univ`.

**But it was not transcription.** agent1 read `Gunter 1987` pp. 20–23. Lemma 24's
printed proof (p. 21) iterates Lemma 23 over an enumeration of normal types and
produces *some* `A⁺`; it is **not about `M(A)`**. The `Ã_tp` form (p. 23) is
asserted without proof. **The `M(A)` form is a remark carrying no theorem, no
proof and no property claim** — the printed sentence says only that it helps in
*picturing* the universal domain. `lemma24_MPair` is therefore the first proof of
it. That is a finding about what the paper carries, **not a printed defect**, and
agent1 correctly logged no tenth entry in `StatementRecovery.md`.

**And `HasNormalRealizations Ainf` is refuted** — `not_hasNormalRealizations_Ainf`
via `not_hasNormalRealizations_of_maximal`: the property forbids normal maximal
points other than `⊥` outright. `Colimit.lean`'s connecting map is `M(stgEmb n)`,
not `eta`; `M(f)` carries an empty cover along unchanged, so `(x,∅)`'s maximality
persists forever, where under `eta` it is destroyed at the next stage. §7.4's own
`b = (⊥,∅)` has a maximal image `β` in `A∞` with `{⊥,β} = im(incl 1) ◁ A∞`.
`not_stagewise_realizations` refutes `LemThirty.lean:426`'s sentence too, so
**r0046's "whole of what remains" is false at this tower.**

**Zero dependent claims fell and none is refuted.** `thm29Normal_of_hasNormalRealizations`
remains a sound implication with an unsatisfiable hypothesis. r0046's reduction
was correct; the target it reduced to is empty.

**The §7.4 dilemma, now measured on both sides:** the `M(f)` tower gives
`V ≅ V⁺`, which every Lemma 30 conjunct consumes, but refutes Theorem 25's
hypothesis; the `η` tower satisfies Lemma 24 but is not a fixed point of `M`.

### `StepFunctionsDecidable` — the lemma was proved and the question was wrong

**The domain theory is done.** `bddAbove_stepsOf_iff`: a finite set of step
functions named by compact pairs is bounded above in `D → E` **iff `P` is
consistent** — for every `S ⊆ P`, sources bounded in `D` implies values bounded
in `E`. And `bddAbove_iff_exists_normal` reduces boundedness of a finite set of
compacts to an existential over finite normal subposets, so §3.2's two conditions
decide it, terminating because `isNormalIn_joinClosure` puts every finite set of
compacts inside a finite normal one. **That is the proof of the paper's
"condition 2 of `e` is exactly what it is for"** — asserted in the file, never
established.

**But `IsCompactElement (ofPairs Q)` is not the boundedness test**, and that is
kernel-checked: `not_forall_isCompactElement_ofPairs_imp_bddAbove`, closed, no
binders. `sSup` on `ScottHom` is total and unconstrained off the bounded sets, so
on an inconsistent `Q` the guard reads a junk value that can be compact. The
witness is at `α = β = N⊥` with `natBotPresentation`, which **is** `IsRecursive`,
so it sits inside the hypotheses the claim grants.

**This is a defect in our transcription of the enumeration, not in Gunter &
Scott** — the third time this round-family that a suspected paper error was ours.

The claim's subject `scottHom d e` branches on a guard its hypotheses do not
determine. The fix is to restate over the consistency-guarded enumeration;
`consistentEnum`/`scottHomC` and `strictConsistentEnum`/`strictHomC` are built
and still exhaust the basis. agent2 did not restate, correctly, since only agent3
held `def`-change authorization.

Rows 1, 2 and 4 of the five-row blocking table are now supplied
(`ofPairs_le_iff`, `ofPairs_apply`, `isNormalIn_compacts_iff`). **Row 2's
recorded reason — "item 3 in disguise" — was wrong, and row 4's — "needs
mub-closure" — was too.**

## What did advance

### The one genuinely open item closed: outcome 1

**`[BoundedComplete β]` is removed from `lem17_fun`**, kernel-checked. Its only
consumer was `ScottHom.exists_finite_isLUB_of_isCompactElement`, whose only
consumer was `directedOn_finiteJoinsBelow` — one lemma, one use. agent4 replaced
the step-function route with **Gunter & Scott's own §6.2 argument**: the directed
family of finitary projections `(q,p)(f) = q ∘ f ∘ p` indexed by finite normal
subposets, `IsLUB (approx f) f` spending only algebraicity. No `stepFun`,
`IsStepPair` or `stepsBelow` appears.

Six declarations lost the binder and gained nothing:

| # | Declaration | Now |
| -- | ---------- | --- |
| 1 | `lem17_fun` | `[Domain α] [Domain β]` |
| 2 | `lem17_strictFun` | `[Domain α] [Domain β]` |
| 3 | `exists_finite_projection_fixing` | `[Domain α] [Domain β]` |
| 4 | `IsAlgebraic (ScottHom α β)` | `[Domain α] [Domain β]` |
| 5 | **`Domain (ScottHom α β)`** | `[Domain α] [Domain β]` |
| 6 | `strictHomDomain` | `[Domain α] [Domain β]` |

Rows 4–5 reach far past Lemma 30: **the function-space domain instance no longer
requires bounded completeness.** Four `*_imp_old` theorems record that each
binder-free statement implies the old one, so the bar is provably not lowered.

**The plan's reduction was incomplete.** Conjunct 1 carries **two** independent
bounded-completeness obligations and Lemma 17 was only one; `PRepFun.rep_arrow`'s
`[BoundedComplete U]` is on `U` itself, spent in `domain_range_compHom`. Routing
that through row 5 leaves exactly one proposition: **`FpImagesBifinite V`** —
every finitary-projection image of `V` is bifinite. Not a formality: transporting
a normal subposet along `p` fails because `p a ≤ x` does not give `a ≤ x`, and
the finite-image-deflation argument needs an idempotence `q ∘ p_i ∘ q` lacks.

**Conjuncts 1–2 are reachable from `Thm29SecondAtDomains` + `FpImagesBifinite V`.**

### `PreservesRecursivePresentation` restated — and the direction runs the other way

The `def` now quantifies over an **operator**, which is what p. 12's sentence
quantifies over. `R47.Agent3.DomainOperator` carries a `Defined` field, which is
what makes `· → ·` expressible at all, since the arrow is a domain only when `E`
is bounded complete.

All four r0046 conditions discharged, and one is instructive:
**`freeCarrier_of_preservesRecursivePresentation` runs *opposite* to r0046's
pattern.** r0046's restatement was a weakening as a proposition; this one is a
**strengthening** — the old is provable at `γ := α`, the new at the arrow is
open. The direction being a theorem is what makes that visible.

`preservesRecursivePresentation_arrowOp_iff` proves the new claim at `arrowOp`
**equivalent to `Theorem7ArrowRecursive`**. The pre-r0047 docstring asserted that
relationship; with a free carrier it could not even be stated.

Discharged at `fstOp`, `sndOp` and any constant operator; open at the arrow, and
no more open than `StepFunctionsDecidable`.

### The quantifier-vacuity sweep: zero further instances, best-controlled zero yet

`scripts/a3-r47-qvac-body.lean`. Criterion: build the parameter graph — parameters
adjacent when they co-occur in a parameter's type, a hypothesis, or the conclusion
— and flag a conclusion parameter whose connected component contains no
hypothesis parameter.

**1 hit in 2,111 declarations, and it is the known one.** 0 among the paper's 19
claims, 0 among 2,015 theorems, 0 instance-only rows.

Precision measured both ways in one pass: the loose criterion ("conclusion-only
parameter") gives **15 hits, 1 true positive, 6.7%**; connectivity gives **1 of
1, 100%, with recall cost 0** — all 15 adjudicated by reading, the 14 false
positives being transport-along-a-map, relations whose arguments sit across an
implication, and predicates about a function.

**Five controls print on every run**, including an underscored synthetic checking
the instrument does not share `#lint unusedArguments`'s `_`-blindness. Plus a
**cross-instrument control**: r0045's `a5-freehyp` reports 50 free `Prop` and 173
free data rows and **says nothing about this mechanism** — confirming *by
measurement* that the question-1 sweeps would have passed it.

### The `S+H` count was 16 and is 12

Four stale, each checked against the kernel: Theorem 18 (`S+P` since r0042/43),
Lemma 28's `(·)♯` and `(·)♭` (`S+P` since r0045), and `StepFunctionsDecidable`,
which **is not an `S+H` row at all** — a `Prop`-valued `def` nobody attempted,
excluded by the label's own definition. The tally was never decremented.

agent5 closed **zero, which is correct**: ten of the twelve are already reduced to
`Thm29Normal`, the other two are agent4's. It identified two conjuncts as "four
lines away" — and **r0046's agent3 had already written those four lines.**

New instrument: `scripts/a5-r47-conditional.sh` is **the first mechanical
detector for `S+H`**. With `sorry` at 0, an open proof appears as a theorem
conditional on an undischarged claim; the package's entire conditional surface is
five files. No `S+H` row has appeared in §§2–6 since r0040.

**Rows 24/25 are contradictory, not open.** `retracts_fun_of_boundedComplete` and
`retracts_strictFun_of_boundedComplete` take the refuted `Thm29Second` *and*
`[BoundedComplete V]`; `not_thm29SecondAtDomains_and_boundedComplete_V` proves
that set contradictory, so repairing them the r0045 way was impossible. agent4's
`retracts_fun_V`/`retracts_strictFun_V` replace them and carry **no
bounded-completeness binder at all**. Both originals are now superseded.

## Corrections to the record

1. **`PaperInventory.md` row 2i's "nobody has swept for it" is false** as of this
   round — written this morning, obsolete by afternoon.
2. r0045's refutation blocker is **overstated**: `IdealCompletion.instDomain
   [Countable A]` exists at line 443 with `thm11`. The refutation is a 300–500
   line counting argument, not a missing construction — and flat domains can
   never be the witness, since any infinite countable carrier admits a
   `PrimrecPred` presentation.
3. `Colimit.lean:59` cites `etaChain_not_wellDefined`, **which exists nowhere** —
   third sighting, after r0044's agent7. The real witness is `stgEmb_ne_mk_eta`.
4. Closing `StepFunctionsDecidable` now closes §3.2's closing sentence at the
   arrow as well: **three claims become four.**
5. agent5's `Ainf` stage-3 minimal-upper-bound witness is **no longer on the
   critical path** for Lemma 30 — agent4's work removed the dependency. It
   remains valuable for an unconditional `¬ BoundedComplete V`.

## Package state

| # | Measure | r0046 | r0047 |
| -- | ----- | ----: | ----: |
| 1 | jobs | 1356 | **1364** |
| 2 | `sorry` / `axiom` / `sorryAx` | 0 / 0 / 0 | **0 / 0 / 0** |
| 3 | Goal A open | 7 (8 strict) | **7 (8 strict)** |
| 4 | `S+H` unfinished proofs | 16 recorded | **12 measured** |
| 5 | environment constants | 3,908 | 4,089 |
| 6 | environment theorems | 2,009 | 2,114 |
| 7 | structures never instantiated | 0 of 23 | **0 of 25** |

## Residue

| # | Item | Kind |
| -- | ---- | ---- |
| 1 | restate `StepFunctionsDecidable` over `consistentEnum` | **mechanical** — machinery built, closes 4 claims |
| 2 | `FpImagesBifinite V` | one named proposition, not a formality |
| 3 | `Thm29Normal` at the `M(f)` tower | the §7.4 dilemma; three routes named, one is refuting it outright |
| 4 | `Primrec` facts for `Finset (ℕ × ℕ)`, `Nat.rfind` totality | recursion theory only; neither `Nat.bitwise` nor `REPred` appears |
| 5 | `Ainf` stage-3 witness | off the critical path; still wanted |

Item 1 is the next round's first move and it is not research.
