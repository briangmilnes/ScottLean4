---
round: r0047
from: agent2
to: orchestrator
subject: compactness-decision
date: 2026-0809-12:40
started: 2026-0809-12:05
finished: 2026-0809-12:40
related:
  - ScottDomains/plans/r0047-plan-from-orchestrator-to-orchestrator-close-the-seven.md
  - ScottDomains/reports/r0046-report-from-agent1-to-orchestrator-bookkeeping-restatement.md
  - ScottDomains/ScottDomains/Effective/A2Compactness.lean
---

# r0047 — agent2: the boundedness of a finite set of step functions

## Headline

| # | Measurement | Value |
| -- | ----------- | ----: |
| 1 | the domain-theoretic fact the plan named — proved? | **yes**, `bddAbove_stepsOf_iff` |
| 2 | claims discharged | **0** |
| 3 | claims reduced further (and how far) | **2** — `Theorem7ArrowRecursive`, `Theorem7StrictRecursive`, now to recursion theory alone |
| 4 | claims with a **new, kernel-checked obstruction** | **1** — `StepFunctionsDecidable` |
| 5 | items of `Effective/FunctionSpace.lean`'s five-row blocking table now supplied | **3 of 5** (rows 1, 2, 4); row 3 split in two; row 5 untouched |
| 6 | new declarations, all in `ScottDomains.R47.Agent2` | 58 (48 theorems, 10 defs), 940 lines, one new file |
| 7 | build | 1357 jobs, 0 errors, 0 warnings, 0 `sorry` |
| 8 | `sorryAx` in any new footprint | 0 |
| 9 | added instance binders on any theorem concluding a claim | 0 |

**The plan predicted "one domain-theoretic fact closes claims 5, 6 and 7." The
fact is proved and it does not close them.** It removes the domain theory from
all three; what is left for claims 6 and 7 is recursion theory, and what is left
for claim 5 is recursion theory *plus a defect in the claim's own subject*.

## 1. The fact

    theorem ScottDomains.R47.Agent2.bddAbove_stepsOf_iff
        {P : Set (α × β)} (hP : P.Finite) (hcptP : P ⊆ compacts α ×ˢ compacts β) :
        BddAbove (ScottHom.stepsOf P) ↔ Consistent P

with

    def Consistent (P : Set (α × β)) : Prop :=
      ∀ S ⊆ P, BddAbove (Prod.fst '' S) → BddAbove (Prod.snd '' S)

A finite set of step functions named by compact pairs is bounded above in
`D → E` exactly when, for every subset whose *sources* are bounded in `D`, the
*values* are bounded in `E`. The condition mentions `P`, `D` and `E` only — no
function space, no `sSup`.

Forward is `ScottHom.step_le_iff` and monotonicity of the bound. Backward
constructs the bound: `pairSup P x = ⨆{b | (a,b) ∈ P, a ⊑ x}`, whose Scott
continuity (`scottContinuous_pairSup`) is where compactness of the sources and
finiteness of `P` are spent — every source below `⨆d` is below one member of `d`,
and finitely many of them are below a single member.

Footprint of every theorem in this section: `[propext, Classical.choice,
Quot.sound]`. `isNormalIn_compacts_iff` depends on **no axioms at all**.

## 2. The blocking table, re-measured

`Effective/FunctionSpace.lean` listed five items. Three are now supplied and one
was two questions written as one.

| # | Item, as recorded | Now |
| -- | ----------------- | --- |
| 1 | `ofPairs P ≤ g` as a finite condition — "half available" | **`ofPairs_le_iff`**: `ofPairs P ≤ g ↔ ∀ p ∈ P, p.2 ≤ g p.1`, under `Consistent P` |
| 2 | `ofPairs Q` evaluated pointwise — "missing, and it is item 3 in disguise" | **`ofPairs_apply`**: `(ofPairs P) x = ⨆(Prod.snd '' belowSet P x)`. It was not item 3 in disguise; consistency replaces directedness, and `pairSupHom` *is* the least upper bound. `ofPairs_le_ofPairs_iff` composes items 1 and 2 into the order test on two index sets |
| 3 | a decision procedure for `IsCompactElement (ofPairs Q)` | **split** — see §3 |
| 4 | `IsNormalIn` for a finite set of compact functions — "missing" | **`isNormalIn_compacts_iff`**, and over *any* bounded complete cpo, not only the function space: `N ◁ K(D) ↔ ⊥ ∈ N ∧ N` closed under the binary joins that exist. `R45.Agent1.isNormalIn_compacts_flat_iff` is its flat case, where the closure clause is vacuous |
| 5 | `Primrec` facts for the `Finset (ℕ × ℕ)` coding — "missing but known feasible" | untouched; still the recursion-theoretic residue |

Row 4's correction matters beyond this claim: the recorded reason was that it
"needs mub-closure in `K(D → E)`". In a bounded complete domain a minimal upper
bound of a bounded set *is* its least upper bound, so mub-closure is join-closure
and the characterization is two lines of condition on `N`, at any domain.

## 3. Row 3 was two questions, and they have different answers

**Question A — is the join there?** Decidable from `d` and `e`. Three results
chain:

* `bddAbove_iff_exists_mem_upperBounds`: inside a normal subposet `u`, a finite
  `v ⊆ u` is bounded above **iff some member of `u` bounds it**. The join of `v`
  is compact (`isCompactElement_of_isLUB_finite`), so normality applies at it.
* `isNormalIn_joinClosure` + `finite_joinClosure`: every finite set of compacts
  lies in a *finite* normal subposet — its join closure, which has at most one
  element per subset.
* `bddAbove_iff_exists_normal`: therefore `BddAbove v ↔ ∃ u, u.Finite ∧ v ⊆ u ∧
  u ◁ K(D) ∧ ∃ b ∈ u, b ∈ upperBounds v`.

The right-hand side is exactly what §3.2's two conditions run: condition 2
recognizes `u`, condition 1 tests the bound, and the search over `u` terminates
because the join closure is a witness. **Boundedness is not an extra assumption
on an effective presentation; it is a consequence of the two the paper states.**
This is the answer to "condition 2 of `e` is exactly what it is for", which
`Effective/FunctionSpace.lean` asserted without proof.

**Question B — does `IsCompactElement (ofPairs Q)` hold?** This is the test
`Effective.scottHomEnum` actually runs, and it is **not** question A.

    theorem R47.Agent2.not_forall_isCompactElement_ofPairs_imp_bddAbove :
        ¬ ∀ {α β : Type} [CompletePartialOrder α] [Domain α] [CompletePartialOrder β]
            [Domain β] [BoundedComplete β] (P : Set (α × β)), P.Finite →
            P ⊆ compacts α ×ˢ compacts β → IsCompactElement (ScottHom.ofPairs P) →
            BddAbove (ScottHom.stepsOf P)

A closed refutation — no binders, conclusion `¬ e` — so it meets r0046's
`REFUTEDBY` criterion.

The mechanism: `sSup` on `ScottHom` is total; `CompletePartialOrder` pins it down
on directed sets and `BoundedComplete` on bounded sets, and an inconsistent
`stepsOf Q` is neither. `ofPairs Q` is then whatever the codomain's `SupSet`
instance returns off its constrained range, and that value can be compact.

The witness is inside the hypotheses the claim grants. At `α = β = N⊥`, with
`P = {(up 0, up 0), (up 0, up 1)}`:

* `not_consistent_badPairs` — the sources are the single element `up 0`, so
  bounded; the values `up 0` and `up 1` have no common upper bound.
* `not_bddAbove_stepsOf_badPairs` — hence the two step functions have no upper
  bound in `N⊥ → N⊥` at all.
* `ofPairs_badPairs` — yet `ofPairs P = step (up 0) (⨆{up 0, up 1})`, because
  `Flat.flatSup` answers the unbounded pair with one of its two members; and
  `isCompactElement_ofPairs_badPairs` — that is a step function with compact
  value, hence **compact**.
* `natBot_guard_true_but_unbounded` — the same statement at
  `Effective.pairsOf natBotPresentation natBotPresentation {(1,1),(1,2)}`, and
  `R45.Agent1.natBotPresentation` is `IsRecursive` (`isRecursive_natBot`). So the
  index set is one `Effective.scottHomEnum` must classify under exactly the
  hypotheses `StepFunctionsDecidable` supplies.

**Consequence.** No theorem of the form "`IsCompactElement (ofPairs Q)` iff
*condition on `Q`, `d`, `e`*" is available, because the left side reads the
ambient `SupSet` instance outside the range any axiom constrains. Which of `up 0`
and `up 1` `flatSup` returns is fixed by `Classical.choice` and is not derivable
either way, so the *value* of `Effective.scottHomEnum` at that index — and hence
the truth of instances of `RecursiveLE (scottHom d e)` — is not decidable from
`d` and `e`.

This is a defect in **this development's transcription of the enumeration**, not
in Gunter & Scott. The paper's enumeration runs over the finite joins that
*exist*; `scottHomEnum` runs over all finite index sets and guards with a
compactness test that is only accidentally related.

## 4. What the defect does and does not block

`Effective.Theorem7ArrowRecursive` and `Effective.Theorem7StrictRecursive` ask
for **some** `f : EffectivePresentation (…)` with `IsRecursive f`. Neither names
`Effective.scottHom d e`. Only `Effective.StepFunctionsDecidable` does. So the
defect is confined to one claim of the three, and the other two can be routed
around it.

`consistentEnum` is `Effective.scottHomEnum` with the guard replaced by
`Consistent (pairsOf d e Q)` — question A instead of question B. It still
exhausts `K(D → E)`: `exists_ofPairs_consistent` upgrades
`ScottHom.exists_ofPairs_of_isCompactElement` by observing that the step
functions it returns are bounded by the compact function itself, which
`bddAbove_stepsOf_iff` converts to consistency. `scottHomC d e` is the resulting
`EffectivePresentation`; `consistentEnum_eq_scottHomEnum` records that the two
agree wherever the old guard was reading a genuine join.

    theorem R47.Agent2.theorem7ArrowRecursive_of_scottHomC.{u, v}
        (h : ∀ {α : Type u} {β : Type v} [CompletePartialOrder α] [Domain α]
          [CompletePartialOrder β] [Domain β] [BoundedComplete β]
          (d : EffectivePresentation α) (e : EffectivePresentation β),
          IsRecursive d → IsRecursive e → IsRecursive (scottHomC d e)) :
        Effective.Theorem7ArrowRecursive.{u, v}

and the same for `⊸`, over `R46.Agent3.strictPairsOf` with the identical
replacement:

    theorem R47.Agent2.theorem7StrictRecursive_of_strictHomC.{u, v} … :
        Effective.Theorem7StrictRecursive.{u, v}

Neither adds a binder: each carries exactly its claim's own binder list,
`[Domain (StrictHom α β)]` included for the strict one, which is the `def`'s own.

## 5. Per-claim status

| # | Claim | Status | Evidence |
| -- | ---- | ------ | -------- |
| 1 | `Effective.StepFunctionsDecidable` | **open, with a new obstruction located in its own subject** | `not_forall_isCompactElement_ofPairs_imp_bddAbove`, `natBot_guard_true_but_unbounded`. The domain theory it needs is done; what remains is recursion theory **and** a guard its hypotheses do not determine |
| 2 | `Effective.Theorem7ArrowRecursive` | **reduced**, strictly further than r0045 left it | `theorem7ArrowRecursive_of_scottHomC` — hypothesis is `IsRecursive (scottHomC d e)`, over a guard §3 question A decides |
| 3 | `Effective.Theorem7StrictRecursive` | **reduced**, likewise | `theorem7StrictRecursive_of_strictHomC` |

Claims 2 and 3 were previously reduced *through* claim 1
(`R45.Agent1.theorem7ArrowRecursive_of_stepFunctionsDecidable`,
`R46.Agent3.theorem7StrictRecursive_of_strictStepFunctionsDecidable`). Those
reductions stand; the new ones are independent of claim 1 and of the defect, and
are the ones a future round should attack.

## 6. Recommendation for `StepFunctionsDecidable`

The claim should be **restated over the consistency-guarded enumeration** —
`IsRecursive d → IsRecursive e → IsRecursive (scottHomC d e)` — under r0046's own
conditions: quote the printed sentence, keep the current statement verbatim as a
citable declaration, and record the direction of the change with a kernel-checked
implication. I did not do it: only agent3 is authorized to change a claim's `def`
this round, and only `PreservesRecursivePresentation`.

The case for the restatement is the same shape as r0046's: the current statement
transcribes the paper's enumeration incorrectly, and the counterexample is the
evidence, not a proof strategy that failed. The paper's own object is the poset
of step functions that *have* joins.

## 7. Corrections to the plan and to the record

* **"One domain-theoretic fact closes claims 5, 6 and 7" is false.** The fact is
  proved and closes none of them. It removes the domain theory from all three and
  exposes a second, different obstruction in claim 5.
* **`Effective/FunctionSpace.lean`'s item 2 is not "item 3 in disguise."** It is
  an independent statement, and consistency — not directedness, and not
  compactness of `ofPairs Q` — is what makes it true.
* **Item 4's recorded reason is wrong.** It does not need "mub-closure in
  `K(D → E)`" as a separate theory: over a bounded complete domain a minimal
  upper bound of a bounded set is its join, so the characterization is general
  and cheap.
* **The two obstructions r0046 measured as "real but not blocking" were checked
  again and not spent on.** Neither `Nat.bitwise` nor `REPred` appears anywhere in
  this module, and neither is on the residue.
* **The plan's `step_le_iff` "half-available" framing understated what was
  missing.** The order characterization needs the pointwise evaluation, which
  needs the boundedness fact; all three are now present, and the chain is
  `ofPairs_le_ofPairs_iff`.

## 8. Declarations added, with footprints

All in `ScottDomains.R47.Agent2`, all in
`ScottDomains/ScottDomains/Effective/A2Compactness.lean` (new file, 940 lines,
58 declarations). Every theorem's footprint is `[propext, Classical.choice,
Quot.sound]` except the two noted.

| # | Declaration | Kind | Footprint |
| -- | ----------- | ---- | --------- |
| 1 | `exists_mem_ub_of_finite` | theorem | `[propext, Classical.choice, Quot.sound]` |
| 2 | `isCompactElement_of_isLUB_finite` | theorem | `[propext, Classical.choice, Quot.sound]` |
| 3 | `isNormalIn_compacts_iff` | theorem | **none** |
| 4 | `sSup_singleton_cpo` | theorem | `[propext]` |
| 5 | `joinClosure`, `subset_joinClosure`, `bot_mem_joinClosure`, `finite_joinClosure`, `joinClosure_subset_compacts`, `isNormalIn_joinClosure` | def + 5 theorems | `[propext, Classical.choice, Quot.sound]` |
| 6 | `bddAbove_iff_exists_mem_upperBounds`, `bddAbove_iff_exists_normal` | theorems | `[propext, Classical.choice, Quot.sound]` |
| 7 | `belowSet`, `mem_belowSet`, `belowSet_subset`, `Consistent` | 2 defs + 2 theorems | — |
| 8 | `finite_stepsOf`, `pairSup`, `bddAbove_snd_belowSet`, `isLUB_pairSup`, `monotone_pairSup`, `scottContinuous_pairSup`, `pairSupHom`, `pairSupHom_apply`, `isLUB_stepsOf_pairSupHom` | 2 defs + 7 theorems | `[propext, Classical.choice, Quot.sound]` |
| 9 | **`bddAbove_stepsOf_iff`** | theorem | `[propext, Classical.choice, Quot.sound]` |
| 10 | `isLUB_stepsOf_ofPairs`, `ofPairs_apply`, `ofPairs_le_iff`, `ofPairs_le_ofPairs_iff`, `isCompactElement_ofPairs_of_consistent` | theorems | `[propext, Classical.choice, Quot.sound]` |
| 11 | `badPairs`, `finite_badPairs`, `badPairs_subset_compacts`, `not_consistent_badPairs`, `not_bddAbove_stepsOf_badPairs`, `stepsOf_badPairs`, `ofPairs_badPairs`, `isCompactElement_ofPairs_badPairs` | def + 7 theorems | `[propext, Classical.choice, Quot.sound]` |
| 12 | **`not_forall_isCompactElement_ofPairs_imp_bddAbove`**, `pairsOf_natBot_badPairs`, `natBot_guard_true_but_unbounded` | theorems | `[propext, Classical.choice, Quot.sound]` |
| 13 | `finite_pairsOf`, `pairsOf_subset_compacts`, `exists_ofPairs_consistent`, `consistentEnum`, `consistentEnum_isCompactElement`, `exists_consistentEnum_eq`, `consistentEnum_eq_scottHomEnum`, `scottHomC` | 2 defs + 6 theorems | `[propext, Classical.choice, Quot.sound]` |
| 14 | **`theorem7ArrowRecursive_of_scottHomC`** | theorem | `[propext, Classical.choice, Quot.sound]` |
| 15 | `finite_strictPairsOf`, `strictPairsOf_subset_compacts`, `strictConsistentEnum`, `strictConsistentEnum_isCompactElement`, `exists_strictConsistentEnum_eq`, `strictHomC` | 2 defs + 4 theorems | `[propext, Classical.choice, Quot.sound]` |
| 16 | **`theorem7StrictRecursive_of_strictHomC`** | theorem | `[propext, Classical.choice, Quot.sound]` |

Docstring-only edit outside the new file: `Effective/FunctionSpace.lean`'s module
docstring gains one section recording rows 1, 2 and 4 as supplied and row 3 as
split, with the refutation named. **No `def` and no statement outside my
namespace was changed.**

## 9. What I would do next, in cost order

1. **The `Primrec` facts for `Denumerable (Finset (ℕ × ℕ))`** — row 5, the only
   remaining item for claims 2 and 3. Membership in and bounded quantification
   over the decoded finset; r0045's `zero_mem_ofNat_finset_iff` is the pattern and
   the `Finset ℕ` analogue is done.
2. **The μ-search for `bddAbove_iff_exists_normal`**, as a `Computable` witness.
   The search is over `Finset ℕ` codes with a decidable test and a proof that a
   witness exists, so it is `Nat.rfind` with a totality proof — the one place the
   development will need `Partrec`-to-`Computable` transfer.
3. **Restate `StepFunctionsDecidable`** over `scottHomC`, per §6. It is the same
   class of defect r0046 corrected in the same claim, one level down: r0046 fixed
   a dropped antecedent, and this is a mis-transcribed subject.
