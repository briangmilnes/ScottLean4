---
round: r0049
from: agent3
to: orchestrator
subject: step-functions-restated
date: 2026-0809-16:56
started: 2026-0809-16:40
finished: 2026-0809-16:56
related:
  - plans/r0049-plan-from-orchestrator-to-orchestrator-six-at-the-unproven.md
  - ScottDomains/Effective/A3StepDecidable.lean
---

# r0049 agent3 — `StepFunctionsDecidable` restated, and the guard convicted a second time

## Outcome in one table

| # | Item | Classification | Evidence |
| -- | ---- | -------------- | -------- |
| 1 | `Effective.StepFunctionsDecidable` | **reduced** — restated, still open | `stepFunctionsDecidable_of_scottHomC`; residue is `ScottHomCRecursive` |
| 2 | direction of the change | **discharged** | `stepFunctionsDecidable_of_compactGuard : old → new`, a **weakening** |
| 3 | `Theorem7ArrowRecursive` | **reduced** (unchanged in strength) | `three_claims_of_residue`, conjunct 2 |
| 4 | `PreservesRecursivePresentation` at `arrowOp` | **reduced** | `three_claims_of_residue`, conjunct 3 |
| 5 | `Theorem7StrictRecursive` | **reduced** | `theorem7StrictRecursive_of_residue` |
| 6 | the order test on the enumeration | **discharged** | `consistentEnum_le_iff` — no reference to the function space survives |
| 7 | **the guard is vacuous on the paper's index set** | **discharged, axiom-free** | `consistent_stepPairs` — the new result of the round |
| 8 | `ScottHomCRecursive`, `StrictHomCRecursive` | **open** — handed to agent4 | recursion theory only |

Build: **1366 jobs, 0 errors, 0 warnings, `sorry` 0**
(`ScottDomains/logs/compile-20260809-165611.agent3.log`). Baseline before the
round was 1365 jobs at the same three zeros.

## 1. What changed, and in which direction

`Effective.StepFunctionsDecidable` read, through r0048:

    IsRecursive d → IsRecursive e → IsRecursive (scottHom d e)

and now reads

    IsRecursive d → IsRecursive e →
      ∃ f : EffectivePresentation (ScottHom α β), IsStepEnumeration d e f ∧ IsRecursive f

with `Effective.IsStepEnumeration d e f := ∀ n, ∃ Q : Finset (ℕ × ℕ),
f.enum n = ScottHom.ofPairs (pairsOf d e Q)` added beside it.

The printed sentence, folio 12, verbatim from `papers/Gunter Scott 1990.pdf`:

> The proof that the poset of step functions has decidable ordering and finite
> normal subposets is tedious, but not difficult, using the effective
> presentations of `D` and `E`.

**Direction: old → new, a weakening** — `stepFunctionsDecidable_of_compactGuard`.
Same direction as r0046's `stepFunctionsDecidable_of_unconditional`; the
*opposite* of r0047's `freeCarrier_of_preservesRecursivePresentation`, which runs
new → old. The old subject `scottHom d e` is one of the enumerations the new
existential ranges over (`isStepEnumeration_scottHom`), which is exactly why the
implication exists. The pre-r0049 statement is kept verbatim as
`R49.Agent3.StepFunctionsDecidableCompactGuard`.

The claim's own universal closure is not weakened as a *transcription*: no bar was
lowered, because `Theorem7ArrowRecursive` is untouched and is still reached from
the new `def` by `Effective.exists_isRecursive_of_stepFunctionsDecidable` and
`R45.Agent1.theorem7ArrowRecursive_of_stepFunctionsDecidable`, both of which still
compile.

### Why not literally `IsRecursive (scottHomC d e)`

The plan asked for the `def` to be stated over `R47.Agent2.scottHomC`. It is
stated over it as a **named claim** — `R49.Agent3.ScottHomCRecursive` — and not
as the `def`, for two reasons, one contingent and one substantive.

1. **Import order forbids it.** `scottHomC` is in `Effective/A2Compactness.lean`,
   which imports `Effective/A1FlatRecursive.lean` and
   `Effective/A3StrictRecursive.lean`, both of which import
   `Effective/FunctionSpace.lean` where the `def` lives; and
   `A1FlatRecursive.lean:397` consumes the `def`. Naming `scottHomC` in the `def`
   requires relocating three declarations across two other agents' files.
2. **It would repeat the error being fixed.** Naming *any* guard in the `def`
   commits the printed sentence to a tie-break it does not make. That is the same
   class of defect as r0046's (dropped antecedent) and r0047's (dropped operator
   dependence): a transcription asserting more structure than the sentence
   carries. The existential over `IsStepEnumeration` is the exact transcription,
   and `EffectivePresentation`'s own `enum_surjective` field keeps it from being
   satisfiable by a degenerate witness — the enumeration must still exhaust
   `K(D → E)`.

## 2. The result of the round: the paper's index set needs no guard

**Check the paper before convicting it** turned up something r0047 did not.
Theorem 7's printed proof, folio 12:

> Suppose `N ◁ K(D)` is finite and `s : N → K(E)` is monotone. Then the function
> `step(s) : D → E` given by taking `step(s)(x) = ⨆{f(y) | y ∈ N ∩ ↓x}` is
> continuous and compact in the ordering on `D → E`.

Gunter & Scott index the basis by a **pair `(N, s)` with `N` a finite normal
subposet of `K(D)` and `s` monotone into `K(E)`** — not by an arbitrary finite set
of index pairs. On that index there is no boundedness question at all: `N` normal
makes `N ∩ ↓x` directed for every `x` in `D`, `s` monotone carries that to a
directed subset of `E`, and a directed set in a cpo has a supremum. The join in
the displayed formula therefore always exists.

Kernel-checked here:

| # | Declaration | Statement | Axioms |
| -- | ---------- | --------- | ------ |
| 1 | `directedOn_inter_Iic_of_isNormalIn` | `N ◁ K(D)` gives `N ∩ ↓x` directed for **every** `x : D`, not only compact `x` | **none** |
| 2 | `consistent_stepPairs` | `R47.Agent2.Consistent (stepPairs N s)` for every normal `N` and monotone `s` — no finiteness, no compact values, no further hypothesis | **none** |
| 3 | `snd_belowSet_stepPairs` | `R47.Agent2.pairSup (stepPairs N s) x` is the printed `⨆{s(y) | y ∈ N ∩ ↓x}`, symbol for symbol | `[propext, Quot.sound]` |

Item 2 says the consistency guard r0047 built to replace the refuted compactness
guard is **identically true on the paper's index sets**. So *neither* guard is the
paper's, and the boundedness decision `ScottHomCRecursive` still owes is an
artifact of enumerating `K(D → E)` by `Finset (ℕ × ℕ)` — an index set that can
name step-function families the paper's parametrization cannot.

This does not convict the paper and it does not retract r0047: r0047's
`not_forall_isCompactElement_ofPairs_imp_bddAbove` and
`natBot_guard_true_but_unbounded` are real theorems with real proofs, re-read this
round, and they refute what they say they refute. It sharpens r0047's finding —
"our guard tests compactness where the paper tests boundedness" — to **the paper
tests neither**.

### A tenth printed defect, small

The same sentence reads `step(s)(x) = ⨆{f(y) | y ∈ N ∩ ↓x}`. `f` is bound
nowhere; the function is `s`. This is a misprint of the same kind as the two
recorded at `StatementRecovery.md` §2.5, and it is **not** in the nine on record.
I have not edited `StatementRecovery.md` — several streams are writing this round
— so it is flagged here for the orchestrator. It changes no statement: every
consumer reads `s`.

## 3. The residue handed to agent4

`R49.Agent3.ScottHomCRecursive d e := IsRecursive d → IsRecursive e →
IsRecursive (R47.Agent2.scottHomC d e)`, and its `⊸` twin `StrictHomCRecursive`.
`three_claims_of_residue` and `theorem7StrictRecursive_of_residue` prove the
plan's arithmetic: the universal closure of the first yields three claims
(`StepFunctionsDecidable`, `Theorem7ArrowRecursive`,
`PreservesRecursivePresentation` at `R47.Agent3.arrowOp`) and of the second, the
fourth (`Theorem7StrictRecursive`). Four claims, one at a single universe because
`preservesRecursivePresentation_arrowOp_iff` is.

What agent4 needs, narrowed. `consistentEnum_le_iff` removes the function space
from the ordering test:

    consistentEnum d e m ≤ consistentEnum d e n ↔
      (Consistent (pairsOf d e (ofNat m)) →
        ∀ p ∈ pairsOf d e (ofNat m), p.2 ≤ consistentEnum d e n p.1)

and `consistentEnum_apply_of_consistent` / `_of_not_consistent` evaluate the right
side to `sSup (Prod.snd '' belowSet (pairsOf d e (ofNat n)) x)` or `⊥`. After
those two, every quantifier ranges over the decoded finsets and every atom is a
`≤` in `E` against a join of finitely many compacts of `E`. What is left is

1. `Primrec` facts for the `Denumerable (Finset (ℕ × ℕ))` coding — membership and
   bounded quantification. r0045's `Finset ℕ` analogue
   (`R45.Agent1.primrecPred_zero_mem_ofNat_finset`) is the pattern.
2. deciding `b ⊑ ⨆{values below a}` in `E` from `IsRecursive e`.
3. deciding `Consistent (pairsOf d e Q)` — **or avoiding it**, which §2 above says
   is what the paper does. Re-indexing the enumeration by `(u, s)` with
   `{dₙ | n ∈ u} ◁ K(D)` and `s` monotone replaces this item by §3.2's own two
   conditions applied directly, and `consistent_stepPairs` proves that
   re-indexing loses no basis element to an unguarded join.
4. `RecursiveNormal` for the enumeration, over
   `R47.Agent2.isNormalIn_compacts_iff`.

Neither `Nat.bitwise` nor `REPred` appears in any of the four; the plan's
instruction to spend no time on them holds.

**Recommendation.** Item 3's second branch is the better route and it is a
construction, not a search: build the `(u, s)` enumeration, whose two side
conditions are literally conditions 1 and 2 of §3.2. That is a new module of
roughly `A2Compactness`'s size and it is the reason Gunter & Scott could call the
step "tedious, but not difficult". I did not start it — it is outside the item I
was given and it overlaps agent4's brief.

## 4. Declarations

`ScottDomains/ScottDomains/Effective/A3StepDecidable.lean`, namespace
`ScottDomains.R49.Agent3`, 27 declarations — 21 theorems, 6 `def`s.

| # | Declaration | Kind | Axioms |
| -- | ---------- | ---- | ------ |
| 1 | `ofPairs_empty` | theorem | `[propext, Classical.choice, Quot.sound]` |
| 2 | `pairsOf_empty` | theorem | same |
| 3 | `isStepEnumeration_scottHom` | theorem | same |
| 4 | `isStepEnumeration_scottHomC` | theorem | same |
| 5 | `StepFunctionsDecidableCompactGuard` | def | — |
| 6 | `stepFunctionsDecidable_of_compactGuard` | theorem | same |
| 7 | `ScottHomCRecursive` | def | — |
| 8 | `stepFunctionsDecidable_of_scottHomC` | theorem | same |
| 9 | `consistentEnum_apply_of_consistent` | theorem | same |
| 10 | `consistentEnum_apply_of_not_consistent` | theorem | same |
| 11 | `consistentEnum_le_iff` | theorem | same |
| 12 | `IsStrictStepEnumeration` | def | — |
| 13 | `StrictStepFunctionsDecidable` | def | — |
| 14 | `strictPairsOf_empty` | theorem | same |
| 15 | `strictStepJoin_empty` | theorem | same |
| 16 | `isStrictStepEnumeration_strictHom` | theorem | same |
| 17 | `isStrictStepEnumeration_strictHomC` | theorem | same |
| 18 | `StrictHomCRecursive` | def | — |
| 19 | `strictStepFunctionsDecidable_of_strictHomC` | theorem | same |
| 20 | `strictStepFunctionsDecidable_of_strictHom` | theorem | same |
| 21 | `exists_isRecursive_of_strictStepFunctionsDecidable` | theorem | same |
| 22 | `three_claims_of_residue` | theorem | same |
| 23 | `theorem7StrictRecursive_of_residue` | theorem | same |
| 24 | `directedOn_inter_Iic_of_isNormalIn` | theorem | **none** |
| 25 | `stepPairs` | def | — |
| 26 | `snd_belowSet_stepPairs` | theorem | `[propext, Quot.sound]` |
| 27 | `consistent_stepPairs` | theorem | **none** |

Every one printed with `scripts/axioms.sh`. No `sorryAx`, no `axiom`.

### Declarations changed outside my namespace

Three, all forced by the authorized `def` change; no statement outside my
namespace was altered.

| # | Declaration | File | Change |
| -- | ---------- | ---- | ------ |
| 1 | `Effective.StepFunctionsDecidable` | `Effective/FunctionSpace.lean` | **the authorized restatement**, with `Effective.IsStepEnumeration` added beside it and the docstring recording the change and its direction |
| 2 | `Effective.exists_isRecursive_of_stepFunctionsDecidable` | same | proof only — the witness is now the existential's, not `scottHom d e` |
| 3 | `R46.Agent1.stepFunctionsDecidable_of_unconditional` | `A1R46.lean` | proof only — supplies `isStepEnumeration_scottHom` as the extra component; the file gains one import |

Two module docstrings were corrected where the restatement made them false:
`Effective/FunctionSpace.lean`'s row-2 table entry and its closing paragraph on
where the r0047 defect lands. That is staleness repair, not new prose.

## 5. Blockers re-derived

| # | Recorded blocker | Re-derived? | Finding |
| -- | --------------- | ----------- | ------- |
| 1 | `IsCompactElement (ofPairs Q)` is not the boundedness test (r0047) | yes — read the proofs, not the docstrings | **stands.** `not_forall_isCompactElement_ofPairs_imp_bddAbove` and `natBot_guard_true_but_unbounded` are closed proofs with a finite witness |
| 2 | "`StepFunctionsDecidable` is blocked on domain theory, not recursion theory" (`analyses/zero-props-zero-false-prose`) | yes | **now false, and the restatement is what made it false.** The domain theory is `R47.Agent2`'s and is done; what is left is recursion theory |
| 3 | "the enumeration is mechanical, closes 4 claims" (plan, `Status.md` item 1) | yes | **half right.** The restatement is mechanical and the four claims do follow from one residue (`three_claims_of_residue`). The residue itself is not mechanical |
