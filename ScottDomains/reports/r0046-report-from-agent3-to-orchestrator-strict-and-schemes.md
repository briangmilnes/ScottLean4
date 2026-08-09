---
round: r0046
from: agent3
to: orchestrator
subject: strict-and-schemes
date: 2026-0808-23:35
started: 2026-0808-23:05
finished: 2026-0808-23:35
related:
  - plans/r0046-plan-from-orchestrator-to-orchestrator-zero-props-zero-false-prose.md
  - reports/r0045-report-from-agent3-to-orchestrator-discharge-thm29.md
  - ScottDomains/Effective/A3StrictRecursive.lean
  - ScottDomains/A3Lemma30Schemes.lean
---

# r0046 agent3 — the enumeration of `K(D ⊸ E)`, and Lemma 30's missing schemes

Two new files, 24 declarations, all in namespace `ScottDomains.R46.Agent3`. Full
package build: **1346 jobs, 0 errors, 0 warnings, `sorry` 0**. Every declaration's
axiom footprint is `[propext, Classical.choice, Quot.sound]`; no `sorryAx`.

Both answers first, because both are short.

**(A) Does an enumeration of `K(D ⊸ E)` now exist? Yes.**
`R46.Agent3.strictHomEnum` is it, and `exists_strictHomEnum_eq` proves it exhausts
`K(D ⊸ E)`. It is the paper's own enumeration — joins of *strict step functions*
named by finite sets of index pairs — not a re-indexing through
`nonempty_effectivePresentation`.

**(B) How many of the three `PRep` schemes were built? One, and the other two
were already there.** The figure "three" was correct when r0045's agent3 wrote it
and stale when r0046 opened: r0045's agent4 discharged the Smyth and Hoare
obligations in the same round, so `R45.Agent4.rep_smyth` and `rep_hoare` were on
this branch at `c4de8f6`. The genuinely missing one was `(·)♮`, which had **zero**
representation-side declarations anywhere in the tree. It is built here as
`rep_plotkin`.

**Nothing in this round is a discharge, and nothing is a discharge at an added
instance binder.** Both headline theorems are reductions with explicit
hypotheses and no binder added to the claim's own `def` line; §4 is the audit.

---

## 1. Piece A — `Theorem7StrictRecursive` and the strict function space

### 1.1 The obstruction as stated, and what it actually cost

`Effective/FunctionSpace.lean:396–400`, the docstring of
`Effective.Theorem7StrictRecursive`:

> Open, and for a further reason than the arrow's: the paper's argument is that
> "the strict step functions form a basis", and this development has no
> strict-step-function basis to enumerate — `PRepFun.strictHomDomain` gets
> `K(D ⊸ E)` countable by injection into `K(D → E)`, which names no enumeration.

That was an accurate measurement of the tree. It is no longer true, and the cost
of making it false is **one lemma that was already present**:
`PRepFun.isStrict_of_le` (anything below a strict function is strict, `PRepFun.lean:405`).

The basis theorem is `exists_strictSteps_isLUB`:

    theorem exists_strictSteps_isLUB {g : StrictHom α β} (hg : IsCompactElement g) :
        ∃ S : Set (ScottHom α β), S.Finite ∧ S ⊆ ScottHom.stepsBelow g.val ∧
          (∀ h ∈ S, IsStrict h) ∧ IsLUB S (g.val : ScottHom α β)

Its proof is four lines. `ClosureProperties.isCompactElement_val_of_isCompactElement`
carries compactness from `D ⊸ E` to `D → E`;
`ScottHom.exists_finite_isLUB_of_isCompactElement` writes `g.val` as the least
upper bound of a finite set of step functions **below it** — `ScottHom.stepsBelow`
carries that inequality already — and `isStrict_of_le` makes each of them strict
because `g.val` is. **No strictification step is needed and no separate
strict-step theory is needed**, which is why the sentence quoted above overstated
the obstruction: it named a missing basis where the tree had every ingredient.

### 1.2 The naming condition

`isStrict_iff_of_isStepPair` is the characterisation the enumeration runs on:

    ScottHom.IsStepPair g p → (IsStrict g ↔ (p.1 = ⊥ → p.2 = ⊥))

Both directions are one evaluation of `stepFun p.1 p.2` at `⊥`, using
`p.1 ≤ ⊥ ↔ p.1 = ⊥`. This turns "strict step function" into a condition on the
*pair of compacts*, which is what an enumeration indexed by pairs of indices
needs, and `isStrict_ofPairs` lifts it to the join through
`ScottDomains.isStrict_sSup` — for every set, with no boundedness hypothesis,
because `isStrict_sSup` covers both branches of `ScottHom`'s total `sSup`.

### 1.3 The enumeration

| # | Declaration | What it is |
| -- | ----------- | ---------- |
| 1 | `strictPairsOf d e Q` | the index pairs of `Q` naming a strict step function |
| 2 | `strictStepJoin d e Q` | their join, landing in `D ⊸ E` with no side condition on `Q` |
| 3 | `strictHomEnum d e n` | `strictStepJoin` at the `n`-th `Finset (ℕ × ℕ)`, guarded by a compactness test |
| 4 | `strictHomEnum_isCompactElement` | every value is compact |
| 5 | `exists_strictHomEnum_eq` | the enumeration exhausts `K(D ⊸ E)` |
| 6 | `strictHom d e` | the `EffectivePresentation (StrictHom α β)` |

The compactness test and the `⊥` fallback are the same ones
`Effective.scottHomEnum` needs, for the same reason: a finite set of step
functions need not be bounded above, `sSup` on `ScottHom` is total, so the join is
a junk value there. The test is classical, so the definition is `noncomputable` —
again exactly as in the arrow case.

`theorem7_strict_ofEnum` is `Effective.theorem7_strict` with its hypotheses used:
same statement, but the witness is `strictHom d e` rather than
`nonempty_effectivePresentation _`, so `d` and `e` are consumed rather than
ignored. `Effective/FunctionSpace.lean:262` records the unused arguments as "a
hypothesis-strength gap"; that gap is closed.

### 1.4 What `Theorem7StrictRecursive` needs now — **reduced, still open**

    theorem theorem7StrictRecursive_of_strictStepFunctionsDecidable.{u, v}
        (h : ∀ {α : Type u} {β : Type v} [CompletePartialOrder α] [Domain α]
          [CompletePartialOrder β] [Domain β] [BoundedComplete β] [Domain (StrictHom α β)]
          (d : EffectivePresentation α) (e : EffectivePresentation β),
          IsRecursive d → IsRecursive e → IsRecursive (strictHom d e)) :
        Effective.Theorem7StrictRecursive.{u, v}

This is the strict counterpart of `R45.Agent1.theorem7ArrowRecursive_of_stepFunctionsDecidable`,
with the same hypothesis shape and the same one-line proof. The measurement:

| # | | before r0046 | after |
| -- | --- | --- | --- |
| 1 | `Theorem7ArrowRecursive` needs | recursion theory | unchanged |
| 2 | `Theorem7StrictRecursive` needs | an enumeration of `K(D ⊸ E)` **and** recursion theory | the same recursion theory, nothing more |

So `⊸` is no longer harder than `→`. The residue is the two obstructions
`Effective/FunctionSpace.lean`'s module docstring already names — Mathlib v4.32.2
states no `Primrec`/`Computable` fact about `Nat.lor`/`Nat.bitwise`/`Nat.testBit`,
and `REPred`'s API is closed under neither `∧` nor `∃` — and they are agent1's
row 6, not mine. **`Theorem7StrictRecursive` is reduced, not discharged.**

---

## 2. Piece B — Lemma 30's representation schemes

### 2.1 The count was three and is one — measured, not assumed

r0045's agent3 table (`reports/r0045-…-discharge-thm29.md`, §1) lists conjuncts 8,
9 and 10 as "scheme missing". Re-measured on this branch at `c4de8f6`:

| # | Conjunct | Retraction pair over `V` | `PRep` scheme | Status at round open |
| -- | -------- | ------------------------ | ------------- | -------------------- |
| 8 | `(·)♯` | `LemThirty.retracts_smyth` | `R45.Agent4.rep_smyth` | **present** |
| 9 | `(·)♭` | `LemThirty.retracts_hoare` | `R45.Agent4.rep_hoare` | **present** |
| 10 | `(·)♮` | `LemThirty.retracts_plotkin` | none | **absent** |

Rows 8 and 9 are r0045's agent4 discharging `SmythImageIso`, `SmythFamilyLUB`,
`HoareImageIso` and `HoareFamilyLUB`, which turned
`PowerdomainMap.Rep.rep_smyth_of` and `rep_hoare_of` from arity 4 into arity 2 —
retraction pair only. The two r0045 streams ran concurrently and did not read each
other; `repSmythAtV` and `repHoareAtV` in `A3Lemma30Schemes.lean` are the
composition check, and the kernel accepted both.

### 2.2 `(·)♮`: 8 new declarations, and why it was cheap

Grep for `plotkinFamily`, `PlotkinImageIso`, `PlotkinFamilyLUB`, `rep_plotkin`
over the tree returned **zero hits** before this round. What did exist is the
whole functor half — `PowerdomainMap.plotkin`, `plotkin_id`, `plotkin_comp`,
`scottContinuous_plotkin`, `isProjection_plotkin`, `foldMono_plotkin` — at exact
parity (9/9/9) with the Smyth and Hoare declarations of `PowerdomainMap.lean`.

The representation half transcribes because r0045's agent4 wrote its two engines
generically and said so:

* `R45.Agent4.nonempty_orderIso_range_of_section` is pure order theory — a
  monotone section-retraction pair, no powerdomain in the statement. So
  `plotkinImageIso` is `smythImageIso` with `plotkin_*` for `smyth_*`.
* `R45.Agent4.isLUB_mapFamily` is generic in the pre-order `A` presenting
  `Pf(K(U))`, with the ordering entering only through `hmono`.
  `Plotkin.FinCompacts U` meets its three binders (`Preorder`,
  `Powerdomain/Plotkin.lean:146`; `OrderBot`, `:223`;
  `ContinuousAlgebra.instFinSetsPlotkin`), and `foldMono_plotkin` is the `hmono`.
  So `plotkinFamilyLUB` is **one line**.

Measured: **no Egli–Milner-specific reasoning appears in the new file.** It was all
spent inside `foldMono_plotkin`, which is r0041's. That is the strongest evidence
that agent4's genericity claim was real rather than asserted.

Result:

    theorem rep_plotkin {fn : ScottHom U (Plotkin.Powerdomain U)}
        {gr : ScottHom (Plotkin.Powerdomain U) U}
        (hfg : ∀ y, fn (gr y) = y) (hgf : ∀ x, gr (fn x) ≤ x) :
        IsPRepresentable U plotkinOp

Arity 2, matching `R45.Agent4.rep_smyth` and `rep_hoare`. Both obligations are
theorems rather than hypotheses, so **no new `Prop` is added to the project's
claim list** — relevant to Goal A, which counts `def … : Prop` naming a result.

There is deliberately **no `repPlotkinAtU`**. §7.4's opening sentence, quoted at
`LemThirty.lean:166`, says `(·)♮` cannot be representable over `U` because it does
not preserve bounded completeness; `Flat.not_boundedComplete_plotkin_TT` is this
development's kernel-checked witness, and `Powerdomain/BoundedComplete.lean`
correspondingly proves Lemma 13 for `♯` and `♭` and not for `♮`. Over `V` the pair
is `LemThirty.retracts_plotkin`, which takes `Thm29SecondAtDomains`.

### 2.3 Five conjuncts became eight

    theorem eight_conjuncts_of_thm29Normal (h : Thm29Normal) :
      IsPRepresentable₂ V prodOp ∧ … ∧ IsPRepresentable V liftOp ∧
      IsPRepresentable V smythOp ∧ IsPRepresentable V hoareOp ∧ IsPRepresentable V plotkinOp

`R45.Agent3.five_conjuncts_of_thm29Normal` had `×`, `⊗`, `+`, `⊕`, `(·)⊥`. The
three powerdomain conjuncts join them. The hypothesis is `Thm29Normal` itself,
with no instance binder added: the pairs come through
`LemThirty.thm29SecondAtDomains_of_thm29Normal`, which is proved.

### 2.4 `Lemma30AtV` reduced to arity 3

    theorem lemma30AtV_of_thm29Normal_of_arrows (h : Thm29Normal)
        (h_arrow : IsPRepresentable₂ V PRep.funOp)
        (h_strictArrow : IsPRepresentable₂ V PRep.strictFunOp) :
        LemThirty.Lemma30AtV

Against `LemThirty.lemma30_of`'s arity 10. **Lemma 30 over `V` is now open at
exactly two named obstructions, and neither is a missing representation scheme:**

1. `LemThirty.Thm29Normal` — [Gun87]'s theorem, agent2's stream.
2. Conjuncts 1 and 2, `→` and `⇸`. `R45.Agent3.not_boundedComplete_V` proves
   `Thm29SecondAtDomains → ¬ BoundedComplete V`, while `PRepFun.rep_arrow` and
   `PRepFun.rep_strictArrow` are this development's only routes to those
   conjuncts and both carry `[BoundedComplete U]`.

Obstruction 2 is worth naming precisely, because it is **not** Lemma 30's defect
and not a scheme gap. It is `Domain (D → E)` for bifinite `D`, `E` **without**
bounded completeness — the development's route to that instance runs through
Theorem 7's step-function decomposition, which needs bounded completeness of the
codomain. `ClosureProperties.lean:54–58` already calls the `[BoundedComplete β]`
in `lem17_fun` "a real open item, not a formality"; this round measures its price
at two of Lemma 30's ten conjuncts, unconditionally. Removing it is Plotkin's SFP
closure under `→`, which the development states nowhere.

---

## 3. Declarations added

`ScottDomains/Effective/A3StrictRecursive.lean` — 13 declarations.

| # | Declaration | Kind | Axioms |
| -- | ----------- | ---- | ------ |
| 1 | `isStrict_iff_of_isStepPair` | theorem | `[propext, Classical.choice, Quot.sound]` |
| 2 | `isStrict_ofPairs` | theorem | same |
| 3 | `exists_strictSteps_isLUB` | theorem | same |
| 4 | `strictPairsOf` | def | — |
| 5 | `strictStepJoin` | def | — |
| 6 | `strictHomEnum` | def | — |
| 7 | `strictHomEnum_isCompactElement` | theorem | same |
| 8 | `exists_strictHomEnum_eq` | theorem | same |
| 9 | `strictHom` | def | — |
| 10 | `theorem7_strict_ofEnum` | theorem | same |
| 11 | `exists_isRecursive_of_strictStepFunctionsDecidable` | theorem | same |
| 12 | `theorem7StrictRecursive_of_strictStepFunctionsDecidable` | theorem | same |
| 13 | `example : Domain (StrictHom α β)` | example | — |

`ScottDomains/A3Lemma30Schemes.lean` — 11 declarations.

| # | Declaration | Kind | Axioms |
| -- | ----------- | ---- | ------ |
| 1 | `plotkinFamily` | def | — |
| 2 | `plotkinFamily_apply` | theorem | `[propext, Classical.choice, Quot.sound]` |
| 3 | `isProjection_plotkinFamily` | theorem | same |
| 4 | `plotkinFamily_mono` | theorem | same |
| 5 | `plotkinImageIso` | theorem | same |
| 6 | `plotkinFamilyLUB` | theorem | same |
| 7 | `domain_range_plotkinFamily` | theorem | same |
| 8 | `rep_plotkin` | theorem | same |
| 9 | `repSmythAtV`, `repHoareAtV`, `repPlotkinAtV` | theorems | same |
| 10 | `eight_conjuncts_of_thm29Normal` | theorem | same |
| 11 | `lemma30AtV_of_thm29Normal_of_arrows` | theorem | same |

---

## 4. Binder audit — no discharge, and no discharge at an added binder

The orchestrator's dominant defect mode, checked declaration by declaration
against the claim each addresses.

| # | Declaration | Binders in signature | Claim's own binders | Verdict |
| -- | ----------- | -------------------- | ------------------- | ------- |
| 1 | `theorem7StrictRecursive_of_strictStepFunctionsDecidable` | none; universe params `{u, v}` and one hypothesis | `Theorem7StrictRecursive` is a closed `Prop` | **reduction**; the `[Domain (StrictHom α β)]` inside the hypothesis is the claim's own binder, copied, not added |
| 2 | `lemma30AtV_of_thm29Normal_of_arrows` | none; three hypotheses | `Lemma30AtV` is a closed `Prop` (`abbrev` for `Lemma30 Colimit.V`) | **reduction** |
| 3 | `eight_conjuncts_of_thm29Normal` | none; hypothesis `Thm29Normal` | — | reduction, not a claim |
| 4 | `repSmythAtV`, `repHoareAtV`, `repPlotkinAtV` | none; hypothesis `Thm29SecondAtDomains` | — | reductions |
| 5 | `rep_plotkin` | `[CompletePartialOrder U] [Domain U]`, both used | — | general scheme, matching `R45.Agent4.rep_smyth` exactly |
| 6 | `strictHom`, and everything downstream | `[Domain (StrictHom α β)]` | `Theorem7StrictRecursive` carries it | the claim's binder, not an addition; discharged by `PRepFun.strictHomDomain` in the module's closing `example` |

Row 6 is the one to check twice, and the check is the `example` at the end of
`A3StrictRecursive.lean`: `Domain (StrictHom α β)` follows from
`[Domain α] [Domain β] [BoundedComplete β]` alone, so the binder restricts
nothing. It has to be a binder because the *statement* mentions
`EffectivePresentation (StrictHom α β)`, whose elaboration needs the instance
before any tactic runs — the same reason `Effective.theorem7_strict` carries it.

**Nothing here concludes a claim.** Both headline results are implications with
named, precisely stated hypotheses.

---

## 5. Per-claim status, in r0045's vocabulary

| # | Claim | Status | Evidence |
| -- | ----- | ------ | -------- |
| 1 | `Effective.Theorem7StrictRecursive` | **reduced** — was open needing an enumeration *and* recursion theory; now needs the recursion theory only | `theorem7StrictRecursive_of_strictStepFunctionsDecidable`; the enumeration is `strictHomEnum` + `exists_strictHomEnum_eq` |
| 2 | `LemThirty.Lemma30AtV` | **reduced**, 5 conjuncts → 8 from `Thm29Normal`; arity 3 overall | `eight_conjuncts_of_thm29Normal`, `lemma30AtV_of_thm29Normal_of_arrows` |
| 3 | `Effective.Theorem7ArrowRecursive` | untouched — agent1's row 6 | — |
| 4 | `LemThirty.Thm29Normal` | untouched — agent2's stream | — |

Movement: **two claims reduced, one representation scheme built, one enumeration
built, zero discharged, zero refuted.**

---

## 6. For the orchestrator

1. **A false sentence in `Effective/FunctionSpace.lean:396–400`**, and I did not
   edit it because this round authorizes prose edits for agents 4 and 5 only. It
   says the development "has no strict-step-function basis to enumerate". It has
   one now (`exists_strictSteps_isLUB`), and the sentence overstated the
   obstruction when written: `PRepFun.isStrict_of_le` and
   `ScottHom.exists_finite_isLUB_of_isCompactElement` were both already present,
   and the basis is their composition. Suggested replacement text is in
   `A3StrictRecursive.lean`'s module docstring. **This is a live instance for
   agent4's Goal B sweep**: it is an "X does not exist" claim falsified by
   material two files away.

2. **A stale count in my own r0045 report**, §1 row 8/9: "missing — agent4's
   stream". Agent4 supplied them in the same round. The report was right when
   written; the merged tree makes it wrong. Recording the correction here rather
   than editing the r0045 report, per the round's rule about not deleting the
   historical record.

3. **`scripts/a6-claims.txt` and `PaperInventory.md`.** Row 7
   (`Theorem7StrictRecursive`) should read "reduced to the arrow's hypothesis",
   not "needs an enumeration of `K(D ⊸ E)`" — the plan's row-7 entry is now
   discharged as a *blocker description*, though the claim itself is still open.
   Row 5 (`Lemma30AtV`) should read "3 missing schemes" → **0 missing schemes**;
   its two remaining obstructions are `Thm29Normal` and bounded completeness.

4. **Coordination with agent2 held.** I touched no `Thm29Normal` declaration and
   proved nothing about it; `eight_conjuncts_of_thm29Normal` consumes it through
   the pre-existing `thm29SecondAtDomains_of_thm29Normal`. If agent2 reduces or
   proves `Thm29Normal`, `lemma30AtV_of_thm29Normal_of_arrows` composes with that
   result unchanged and `Lemma30AtV` drops to arity 2.

5. **Composition check for merge.** `A3Lemma30Schemes.lean` imports both
   `ScottDomains.A3Thm29` (r0045 agent3) and `ScottDomains.A4PowerdomainRep`
   (r0045 agent4) into one environment; the r0045 merge never did, since
   `lake build` does not import two unrelated modules together. It elaborates with
   zero errors and zero warnings, so those two namespaces do not clash.

6. **A defect I did not fix and am not authorized to.** `LemThirty.lean:389–393`
   says `PRep.rep_lift` and `PRep.rep_prod` "are the only two of Lemma 28's nine
   schemes already proved". My r0045 report already recorded this as false at
   seven; with `rep_plotkin` the corresponding figure for **Lemma 30** is that
   eight of its ten schemes are available. The sentence should be rewritten
   against the built environment, not against r0044's tree.
