---
round: r0045
from: agent1
to: orchestrator
subject: discharge-effective
date: 2026-0808-21:50
started: 2026-0808-21:15
finished: 2026-0808-21:50
related:
  - plans/r0045-plan-from-orchestrator-to-orchestrator-discharge-nineteen.md
  - docs/StructuresVsTypeClassesVsPropsInLean4.md
  - ScottDomains/Effective/A1FlatRecursive.lean
---

# r0045 — agent1: the §3.2 effective-presentation cluster

## Headline

| # | Measurement | Value |
| -- | ----------- | ----: |
| 1 | claims assigned | 4 |
| 2 | **fully discharged** (conclusion is the claim, binders exactly the claim's) | **0** |
| 3 | discharged at a parameter instance | 1 claim, 2 instances |
| 4 | reduced (fewer hypotheses than the best prior theorem) | 1 |
| 5 | open | 2 |
| 6 | claims found mis-stated (statement does not say what the paper says) | 2 |
| 7 | **`RecursivePresentation` now inhabited** | **yes** — `natBotRecursivePresentation : RecursivePresentation (Flat ℕ)` |
| 8 | new declarations, all in `ScottDomains.R45.Agent1` | 21 |
| 9 | build | 1340 jobs, 0 errors, 0 warnings, 0 `sorry` |
| 10 | `sorryAx` in any new footprint | 0 |

One file was written: `ScottDomains/Effective/A1FlatRecursive.lean`. Nothing outside
my namespace was edited; no `def` of any claim was changed.

## The acceptance labels I am using

Per the orchestrator's correction, **discharged** requires the theorem's binders to
be exactly the claim's. I need one more label the correction does not name, because
three of my four claims are *parameterized* `def`s rather than closed `Prop`s:

* **Discharged at the parameter instance `x := c`** — the conclusion is the claim
  with one of its own parameters instantiated at a specific value. No binder is
  added, but the universal closure over that parameter is not proved. This is
  weaker than discharge in exactly the way "discharged at `[Domain D]`" is, and I
  report it as such.

## Claim-by-claim

### 1. `Effective.StepFunctionsDecidable` — **open, and mis-stated**

    def StepFunctionsDecidable {α β} [CompletePartialOrder α] [Domain α]
        [CompletePartialOrder β] [Domain β] [BoundedComplete β]
        (d : EffectivePresentation α) (e : EffectivePresentation β) : Prop :=
      IsRecursive (scottHom d e)

Nothing was proved about it, and I claim its universal closure `∀ α β d e,
StepFunctionsDecidable d e` is **false**. The reason is a missing hypothesis, not a
missing proof: Theorem 7's proof sentence says the step-function poset is decidable
"**using the effective presentations of `D` and `E`**", and the `def` quantifies
over *arbitrary* `d` and `e`, including presentations whose own ordering is not
computable.

The refutation, as a proof sketch with its obligations named — **not kernel-checked,
do not record it as a result**:

| # | Step | What it needs |
| -- | ---- | ------------- |
| 1 | a presentation `d` of `Flat ℕ` with `¬ RecursiveLE d`: `enum (2n) = up n`, `enum (2n+1) = if n ∈ A then ⊥ else up n` for `A` non-computable. Then `enum (2n+1) ≤ enum (2m)` with `m ≠ n` decides `A` | `ComputablePred.halting_problem` (Mathlib) supplies `A` |
| 2 | `RecursiveLE (scottHom d e) → RecursiveLE d`, by reading the order back off single step functions: `(a ↦ b) ≤ (a' ↦ b) ↔ a' ≤ a` whenever `b ≠ ⊥` | the order lemma for `ScottHom.ofPairs` at a singleton, plus compactness of that singleton so `scottHomEnum` takes its `then` branch |
| 3 | the index map `(i, j) ↦ Encodable.encode ({(i, j)} : Finset (ℕ × ℕ))` is `Primrec`, so step 2 is a computable reduction | the singleton case of the `Denumerable (Finset (ℕ × ℕ))` coding; the analogous fact for `Finset ℕ` is now proved in this round's file, so the route is known-feasible rather than blocked |

Estimated cost: one round. **The specification decision is yours**: the honest
statement is `IsRecursive d → IsRecursive e → StepFunctionsDecidable d e`, which is
what `theorem7ArrowRecursive_of_stepFunctionsDecidable` below takes as its
hypothesis. I did not change the `def`.

### 2. `Effective.Theorem7ArrowRecursive` — **reduced: 0 theorems → 1 theorem, 1 hypothesis**

    theorem ScottDomains.R45.Agent1.theorem7ArrowRecursive_of_stepFunctionsDecidable.{u, v}
        (h : ∀ {α : Type u} {β : Type v} [CompletePartialOrder α] [Domain α]
          [CompletePartialOrder β] [Domain β] [BoundedComplete β]
          (d : EffectivePresentation α) (e : EffectivePresentation β),
          IsRecursive d → IsRecursive e → StepFunctionsDecidable d e) :
        Theorem7ArrowRecursive.{u, v}

Footprint `[propext, Classical.choice, Quot.sound]`.

Before this round the claim had **no theorem concluding it**.
`Effective.exists_isRecursive_of_stepFunctionsDecidable` concludes `∃ f, IsRecursive
f` at fixed `d`, `e` — a different proposition. The remaining hypothesis is the
uniform, hypothesis-strengthened step-function claim; one hypothesis, and it is the
paper's own proof structure.

Two notes the next stream needs:

* The explicit universe binders `.{u, v}` are load-bearing. `Theorem7ArrowRecursive`
  is universe-polymorphic (`Theorem7ArrowRecursive.{u_1, u_2}`), and a hypothesis
  cannot quantify over universes, so without pinning the theorem's universes to the
  claim's the statement does not typecheck. The first attempt failed exactly there.
* This is a reduction, not progress on the mathematics. What is genuinely missing
  for the claim is (a) a decision procedure for `ofPairs P ≤ ofPairs Q` from the
  component presentations, (b) the boundedness test that decides whether the join of
  a finite set of step functions exists — condition 2 of `e` — and (c) `Primrec`
  facts for the `Finset (ℕ × ℕ)` coding. Item (c) was on record as blocked; it is
  not (see "corrections" below).

### 3. `Effective.Theorem7StrictRecursive` — **open, untouched**

Not attempted, and I would not have got it: it needs everything the arrow case needs
and one thing more. The paper's argument is that "the strict step functions form a
basis"; this development has no strict-step-function basis. `PRepFun.strictHomDomain`
makes `K(D ⊸ E)` countable by injecting it into `K(D → E)`, and an injection names
no enumeration, still less a computable one.

What would supply it, cheapest first:

1. A **decidable-image transfer lemma**: if `K(δ)` embeds in `K(γ)` by an
   order-embedding whose image is a computable set of indices, then a recursive
   presentation of `γ` induces one of `δ`. General, reusable, and it would also give
   the powerdomain operators. Estimated 60–100 lines on top of a compactness-transfer
   lemma for order-embeddings, which the development does not appear to have.
2. The paper's route: enumerate the strict step functions directly.

### 4. `Effective.PreservesRecursivePresentation` — **discharged at two parameter instances; mis-stated; universal closure false**

    def PreservesRecursivePresentation {α β} [CompletePartialOrder α] [Domain α]
        [CompletePartialOrder β] [Domain β] (γ : Type*) [CompletePartialOrder γ]
        [Domain γ] (d : EffectivePresentation α) (e : EffectivePresentation β) : Prop :=
      IsRecursive d → IsRecursive e → ∃ f : EffectivePresentation γ, IsRecursive f

`γ` is a parameter **unrelated to `α` and `β`**, and the conclusion does not mention
`d` or `e`. So the statement cannot express §3.2's sentence, which is about
*operators* `(D, E) ↦ F D E`. Three consequences, all measured:

| # | Theorem | Binders vs. the claim's | Label |
| -- | ------- | ----------------------- | ----- |
| 1 | `preservesRecursivePresentation_id : PreservesRecursivePresentation α d e` | identical except `γ := α` | discharged at the parameter instance `γ := α`; proof is `fun hd _ => ⟨d, hd⟩` |
| 2 | `preservesRecursivePresentation_natBot : PreservesRecursivePresentation (Flat ℕ) d e` | identical except `γ := Flat ℕ` | discharged at the parameter instance `γ := Flat ℕ` |
| 3 | `preservesRecursivePresentation_of_isRecursive` | adds `{f : EffectivePresentation γ}` and `hf : IsRecursive f` | a reduction, and a **trivial** one — the hypothesis is the conclusion minus the `∃`. Recorded because it makes rows 1 and 2 one line each, not as progress |

Row 1 is the finding. The identity operator satisfies the schema by returning its
own hypothesis; no `Classical.dec` is involved, so this is a **second vacuity,
independent of the one `docs/StructuresVsTypeClassesVsPropsInLean4.md` describes**.
That one lives in a field type (`Decidable` is classically free); this one lives in
the quantifier structure of the statement.

I flag these rather than suppress them because agent6's detector will now score this
row as having theorems concluding it. **It is not discharged.** Its universal
closure over `γ`,

    ∀ γ [CompletePartialOrder γ] [Domain γ], PreservesRecursivePresentation γ d e

is **false** whenever some `d`, `e` are recursive — which, as of this round, some
are. The argument (not kernel-checked): a recursive presentation is determined by a
computable order relation on ℕ, and there are countably many of those
(`Nat.Partrec.Code` is denumerable), whereas there are `2^ℵ₀` pairwise
non-isomorphic countable bounded-complete bases, hence that many pairwise
non-isomorphic domains. To make it kernel-checked one needs an ideal-completion
construction over an arbitrary countable poset — the development has none — plus the
countability of `{p // ComputablePred p}`. I do not recommend it: fixing the `def`
is cheaper and is the actual defect.

**Recommended restatement (your call, not mine):** one `def` per operator, shaped
like `Theorem7ArrowRecursive` — the `γ = D → E` instance is already written that way
and is the model.

## The round's substantive result: `RecursivePresentation` is inhabited

`Effective/FunctionSpace.lean` records `RecursivePresentation` as "deliberately
uninstantiated … an honest empty set". It is no longer empty:

    noncomputable def ScottDomains.R45.Agent1.natBotRecursivePresentation :
        RecursivePresentation (Flat ℕ)

built from `natBotPresentation` and `isRecursive_natBot`, footprint `[propext,
Classical.choice, Quot.sound]`, no `sorryAx`.

Why `N⊥` is where this is cheap, and why it is not vacuous:

| # | Condition | At `N⊥` | Witness |
| -- | --------- | ------- | ------- |
| 1 | `dₐ ⊑ d_b` | `a = 0 ∨ a = b`, because the flat order is `x ⊑ y ↔ x = ⊥ ∨ x = y` and the enumeration `0 ↦ ⊥`, `k+1 ↦ up k` is injective | `Primrec.eq` twice, `PrimrecPred.or` |
| 2 | `{dₙ ∣ n ∈ u} ◁ K(N⊥)` | `0 ∈ u`. In a flat cpo `↓x` is a chain, so directedness is automatic and normality reduces to `⊥ ∈ N` (`isNormalIn_compacts_flat_iff`) | `Primrec.list_head?` after the decoding bridge below |

`ComputablePred` is not obtainable from `Classical.choice` — Mathlib's own
`ComputablePred.halting_problem` is the proof — so neither field can be filled the
way `EffectivePresentation`'s `Decidable` fields can. Two independent checks that
this instance is not the vacuous kind:

* Four `example`s in the file are closed by `decide`, which a `Classical.dec`
  instance cannot do: the kernel runs both decision procedures.
* The presentation is marked `noncomputable`, and that is **not** a weakening. It
  records that `Flat.instCompletePartialOrder`'s `sSup` branches classically — a
  fact about the carrier's cpo structure, not about the two decision procedures. The
  axiom footprint cannot distinguish those; the `decide` examples can, which is why
  they are there.

This does not make `Effective.powersetPresentation` recursive. That one enumerates
`K(P N)` by binary expansion and its condition 1 reduces to `Computable fun p : ℕ ×
ℕ => p.1 ||| p.2`; re-measured this round, `bitwise|lor|testBit` over
`Mathlib/Computability/` is still **0 hits**. That obstruction is specific to that
enumeration.

## Two corrections to `Effective/FunctionSpace.lean`

Both are docstring claims about Mathlib, both measured against the built library,
per r0044's rule that a docstring is not a specification.

**1. False.** `RecursiveNormal`'s docstring: "Mathlib v4.32.2 has no `Primcodable
(Finset ℕ)` instance, so `ComputablePred` cannot be asked of a predicate on `Finset
ℕ` at all."

`Primcodable.ofDenumerable` (`Mathlib/Computability/Primrec/Basic.lean:139`,
priority 10) turns any `Denumerable α` into `Primcodable α`, and `Denumerable
(Finset α)` is `Mathlib/Logic/Equiv/Finset.lean:109`. The file now contains
`example : Primcodable (Finset ℕ) := inferInstance` and, for the second half of the
sentence, `primrecPred_zero_mem_finset : PrimrecPred fun u : Finset ℕ => 0 ∈ u`.

The consequence is larger than one docstring: `RecursiveNormal` quantifies over
`Denumerable.ofNat (Finset ℕ) n`, and that decoding is primitive recursive by
`Primrec.ofNat`. Deciding membership in it needed one bridge Mathlib does not state,
now proved here:

    zero_mem_ofNat_finset_iff (n : ℕ) :
      0 ∈ Denumerable.ofNat (Finset ℕ) n ↔ (Denumerable.ofNat (List ℕ) n).head? = some 0

`Denumerable.finset` decodes `n` to a list and applies `Denumerable.raise' · 0`,
whose entries increase from the head, so `0` occurs exactly at the head.
`le_of_mem_raise'` is the supporting induction. **Any future `RecursiveNormal` proof
goes through this route**, so it is the reusable half of the file.

**2. Superseded.** "No `RecursivePresentation` exists yet, and that is the honest
state." True when written; false now, for `Flat ℕ`. It remains true that no
`RecursivePresentation (Set ℕ)` exists, for the bitwise reason above.

## Declarations added, with footprints

All in `ScottDomains.R45.Agent1`, all in `ScottDomains/Effective/A1FlatRecursive.lean`.

| # | Declaration | Footprint |
| -- | ----------- | --------- |
| 1 | `ofNat_finset_eq` | `[propext, Classical.choice, Quot.sound]` |
| 2 | `mem_ofNat_finset_iff` | `[propext, Classical.choice, Quot.sound]` |
| 3 | `le_of_mem_raise'` | `[propext, Quot.sound]` |
| 4 | `zero_mem_raise'_zero_iff` | `[propext, Quot.sound]` |
| 5 | `zero_mem_ofNat_finset_iff` | `[propext, Classical.choice, Quot.sound]` |
| 6 | `primrecPred_zero_mem_ofNat_finset` | `[propext, Classical.choice, Quot.sound]` |
| 7 | `primrecPred_zero_mem_finset` | `[propext, Classical.choice, Quot.sound]` |
| 8 | `isNormalIn_compacts_flat_iff` | `[propext, Classical.choice, Quot.sound]` |
| 9 | `natBotEnum`, `natBotEnum_{zero,succ,eq_bot_iff,injective,surjective}` | — (definition and `rfl`-level lemmas) |
| 10 | `natBotEnum_le_iff` | `[propext]` |
| 11 | `isNormalIn_natBotEnum_image_iff` | `[propext, Classical.choice, Quot.sound]` |
| 12 | `decidableNatBotLE`, `decidableNatBotNormal` | — (instances) |
| 13 | `natBotPresentation` | `[propext, Classical.choice, Quot.sound]` |
| 14 | `recursiveLE_natBot` | `[propext, Classical.choice, Quot.sound]` |
| 15 | `recursiveNormal_natBot` | `[propext, Classical.choice, Quot.sound]` |
| 16 | `isRecursive_natBot` | `[propext, Classical.choice, Quot.sound]` |
| 17 | `natBotRecursivePresentation` | `[propext, Classical.choice, Quot.sound]` |
| 18 | `preservesRecursivePresentation_of_isRecursive` | `[propext, Classical.choice, Quot.sound]` |
| 19 | `preservesRecursivePresentation_natBot` | `[propext, Classical.choice, Quot.sound]` |
| 20 | `preservesRecursivePresentation_id` | `[propext, Classical.choice, Quot.sound]` |
| 21 | `theorem7ArrowRecursive_of_stepFunctionsDecidable` | `[propext, Classical.choice, Quot.sound]` |

`Classical.choice` enters through the ambient domain theory (`Flat`'s `sSup`,
`IsNormalIn`, `funext`/`propext` transport in `of_eq`), never through the two
`ComputablePred` witnesses — which is unprovable from a footprint and is why row 10
and the `decide` examples are reported separately.

## Corrections to the plan

* The plan's warning — "do not discharge these four by routing through
  `nonempty_effectivePresentation`" — was right and I did not. But the vacuity it
  names is not the only one in this cluster: `PreservesRecursivePresentation` is
  trivially satisfiable by its own quantifier structure, with no `Classical.dec`
  anywhere. A reviewer checking only for `Classical.dec` would pass it.
* The plan says `RecursivePresentation` is "deliberately uninstantiated" and treats
  constructing one as the hard half. At `N⊥` it is about 120 lines, and the blocking
  fact it cites (`Primcodable (Finset ℕ)`) does not block anything. The genuinely
  hard half is the *operator* cases, which are recursion theory about codings of
  `Finset (ℕ × ℕ)` and about `ScottHom.ofPairs`.

## What I would do next, in cost order

1. The decidable-image transfer lemma (claim 3, item 1 above). It is the single
   lemma that makes recursive presentations propagate at all, and every operator
   case needs it.
2. The `Finset (ℕ × ℕ)` singleton-coding `Primrec` fact. It unlocks both the
   `StepFunctionsDecidable` refutation and the arrow construction.
3. A specification decision on `StepFunctionsDecidable` (add the two `IsRecursive`
   hypotheses) and on `PreservesRecursivePresentation` (one `def` per operator).
   Both are orchestrator calls; neither is a proving task.
