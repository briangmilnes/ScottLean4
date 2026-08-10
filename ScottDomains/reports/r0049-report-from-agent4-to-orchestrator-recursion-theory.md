---
round: r0049
from: agent4
to: orchestrator
subject: recursion-theory
date: 2026-0809-17:12
started: 2026-0809-16:36
finished: 2026-0809-17:12
related:
  - plans/r0049-plan-from-orchestrator-to-orchestrator-six-at-the-unproven.md
  - ScottDomains/Effective/A4Recursion.lean
  - scripts/a4-decode-probe.lean
  - reports/r0049-report-from-agent3-to-orchestrator-step-functions-restated.md
---

# r0049 agent4 — the recursion theory: both items supplied, and one of them shown unnecessary where the paper works

## Outcome in one table

| # | Item | Classification | Evidence |
| -- | ---- | -------------- | -------- |
| 1 | `Primrec` facts for the `Finset (ℕ × ℕ)` coding | **discharged** | `primrec₂_raise'`, `primrec_idxList`, `primrec_decodeList_pair`, `primrecRel_mem_ofNat_finset` |
| 2 | a `Nat.rfind` with a totality proof for the normal-subposet search | **discharged** | `exists_normal_superset` (totality), `computable_normCode` (the search) |
| 3 | **§3.2's two conditions decide boundedness** — the sentence `R47.Agent2.bddAbove_iff_exists_normal`'s docstring asserts and does not prove | **discharged** | `computablePred_bddAbove` |
| 4 | the join of a bounded finite set of basis elements, as a computable index | **discharged** | `isLUB_enum_joinIdx`, `computable_joinIdx` |
| 5 | agent3's residue item 2 — deciding `b ⊑ ⨆{values below a}` in `E` | **discharged, and without any search** | `le_sSup_stepValues_iff`, `computablePred_le_stepValues` |
| 6 | agent3's residue item 3 — deciding `Consistent (pairsOf d e Q)` | **reduced** to item 3 above; and **avoidable** on the paper's index | see §4 |
| 7 | agent3's residue item 4 — `RecursiveNormal` for the enumeration of `K(D → E)` | **open**, and it is the one place both routes still need work | §5 |
| 8 | `R49.Agent3.ScottHomCRecursive`, `StrictHomCRecursive` | **open** — narrowed to item 7 plus an index coding | §5 |
| 9 | `decide` evidence that the decoding is a program | **refuted as available** — the obstruction is `Nat.sqrt` | §2 |

Build: **1367 jobs, 0 errors, 0 warnings, `sorry` 0**
(`ScottDomains/logs/compile-20260809-170622.agent4.log`). Baseline in this
worktree, measured by removing the new module and rebuilding, is **1365 jobs** at
the same three zeros (`compile-20260809-170652.agent4.log`); the two added jobs
are `ScottDomains.Effective.A4Recursion` and `Mathlib.Data.List.GetD`, which it
imports for `List.getI_eq_getElem`.

One file added: `ScottDomains/ScottDomains/Effective/A4Recursion.lean`, namespace
`ScottDomains.R49.Agent4`, **51 declarations — 39 theorems, 10 `def`s, 2
`instance`s** (one of the instances noncomputable). No declaration outside my
namespace was touched. One `INDEX.md` line added; one probe script added.

## 1. What the round was asked for, and what it produced

The plan named two items. Both are supplied, and they compose into a statement
neither of them is:

    computablePred_bddAbove :
      IsRecursive d → ComputablePred fun n : ℕ => BddAbove (basisSet d n)

for any bounded complete domain, where `basisSet d n = d.enum '' ↑(ofNat (Finset ℕ) n)`.

**This is §3.2's two conditions deciding boundedness.**
`R47.Agent2.bddAbove_iff_exists_normal` proves the order-theoretic equivalence and
its docstring asserts the recursion-theoretic consequence — "so 'is this finite
set of compacts bounded?' is not an extra hypothesis on an effective
presentation — it is a consequence of the two the paper states" — without
proving it. It is now proved. The algorithm is:

1. search for the least code `m` of a finite normal subposet whose index set
   contains the given one (`normCode`);
2. inside it, test `∃ i ∈ ofNat (Finset ℕ) m, ∀ j ∈ ofNat (Finset ℕ) n,
   d_j ⊑ d_i` — a finite test, decided by `RecursiveLE d`.

Step 1 terminates because `R47.Agent2.isNormalIn_joinClosure` puts every finite
set of compacts inside a finite normal one; `exists_normal_superset` is that fact
transported to index sets, which needs `surjective_ofNat_finset_nat` to name each
member of the join closure. Step 2 is `bddAbove_basisSet_iff`, which is
`R47.Agent2.bddAbove_iff_exists_mem_upperBounds` read off the indices.

`Computable.find` (`Mathlib/Computability/RE.lean:177`) is the bridge from
`Partrec.rfind` to a total function; the plan's "a `Nat.rfind` with a totality
proof" is exactly its two arguments, and the totality proof is the work.

### The companion: the join, as an index

`R47.Agent2.ofPairs_le_ofPairs_iff` reduces the ordering on the step-function
enumeration to `p.2 ⊑ sSup (Prod.snd '' belowSet Q p.1)`, and testing that with
`RecursiveLE e` needs an **index** for the join. `computable_joinIdx` supplies
one, by a second total search whose termination rests on a fact stated nowhere in
the development:

    mem_of_isLUB_of_isNormalIn :
      u ◁ K(D) → v ⊆ u → v.Finite → IsLUB v c → c ∈ u

— the *least* upper bound of a bounded finite subset of a normal set is in the
set. `R47.Agent2.bddAbove_iff_exists_mem_upperBounds` produces *some* bound in
the normal set; this produces the least one, which is what makes the join
findable by a bounded search inside `normCode d n`.

## 2. A negative result: `decide` cannot witness these procedures

r0045's `Effective/A1FlatRecursive.lean` closes its "the procedures run" checks
with `decide`, which is the strong evidence: the kernel reduces the decision
procedure, so it is not a `Classical.dec`. **That form is unavailable for any
`Denumerable` decoding in Mathlib v4.32.2**, and the obstruction is one
declaration deep:

    example : Nat.sqrt 5 = 2 := by decide
    -- Tactic `decide` failed … reduction got stuck at `(Nat.sqrt 5).beq 2`

`Nat.sqrt` is compiled by well-founded recursion; `Nat.unpair` calls it; every
`Denumerable` decoding of a pair, a list or a `Finset` goes through `Nat.unpair`.
Measured, not inferred: `idxList 5 = [0,1,2]` fails under `decide` and under
`rfl`, and so does `Nat.sqrt 5 = 2` on its own.

The compiled evaluator runs them. `scripts/a4-decode-probe.lean`, run through
`scripts/a3-run-lean.sh a4-decode-probe`, prints `idxList 5 = [0, 1, 2]`,
`decodeList (ℕ × ℕ) 5 = [(0,0), (0,1), (1,0)]`, the first thirty decoded index
sets, and the membership test. The `#eval`s are kept **out** of the module so the
build carries no `info` output.

A second measurement, cheap and worth recording: `Encodable.encode` on
`Finset ℕ` resolves to `Finset.encodable`, **not** to the `Denumerable.finset`
encoding, so `idxList (encode ({0,2,5} : Finset ℕ))` evaluates to `[0,3,9]`, not
`[0,2,5]`. This is the hazard `Effective.surjective_ofNat_finset`'s docstring
warns about, observed. `surjective_ofNat_finset_nat` is stated for the same
reason.

## 3. The coding, and the Mathlib gap it filled

r0045 proved `0 ∈ ofNat (Finset ℕ) n` primitive recursive by reading the decoded
list's head. That argument is specific to `0` — every later element of the
decoded list sits behind `Denumerable.raise'`'s accumulator — so it does not
generalise, and general membership and bounded quantification are what §3.2's
condition 2 needs. The route taken decodes the whole list:

* `Denumerable.raise'` threads an offset, so it is a **left** fold, not a map.
  `foldl_raiseStep` and `raise'_eq_foldl` put it in the shape
  `Primrec.list_foldl` accepts, giving `primrec₂_raise'`.
* `idxList` and `decodeList α` then decode; `mem_idxList_iff` is the bridge to
  `Finset` membership, and `primrecRel_mem_ofNat_finset` is the general form of
  r0045's single test.
* `primrec_decodeList_nat` and `primrec_decodeList_pair` are stated at the two
  concrete carriers rather than for a general denumerable `α`, because
  `[Denumerable α]` and `[Primcodable α]` as separate binders build **two**
  `Encodable α` instances and `Primrec.ofNat` is then ill-typed. Lean's
  `overlappingInstances` linter flags exactly this; the concrete carriers avoid
  it and are the only ones the development uses.

**A second Mathlib gap, and the one that cost the most.** Mathlib states
`Primrec.forall_mem_list` and `Primrec.exists_mem_list` and **no `Computable`
analogue of either**. The predicates here are `ComputablePred` — they come from
`RecursiveLE d`, a hypothesis — so the `Primrec` versions do not apply.
`computable_allLt` supplies the missing step: bounded quantification is primitive
recursion on the bound, via `Computable.nat_rec`, and it is the only place a
recursion is written in this file. `computablePred_forall_mem` and
`computablePred_exists_mem` are its two consumers, and `computablePred_comp`,
`computablePred_and`, `computablePred_or` are three further closure facts
Mathlib does not state for `ComputablePred`.

## 4. agent3's re-indexing, evaluated

agent3's mid-round finding: Gunter & Scott index the basis of `K(D → E)` by a
pair `(N, s)` — `N` a finite normal subposet of `K(D)`, `s` monotone — so the
join in the printed formula always exists and there is nothing to guard.
`R49.Agent3.consistent_stepPairs` proves r0047's consistency guard identically
true there.

**I evaluated it and it is right, and it changes the answer on one of the two
places the search was aimed at.** Section 5 of the new module measures which:

| # | Where | Does the re-indexing remove the search? |
| -- | ---- | --------------------------------------- |
| 1 | the **order** test on the enumeration (agent3's residue item 2) | **yes, entirely.** `N ∩ ↓x` is directed, its image under a monotone `s` is directed, and a compact element is below a directed join exactly when it is below a member. So `e_b ⊑ ⨆{e_{t j} \| j ∈ u, d_j ⊑ x}` is a **finite** test — `le_sSup_stepValues_iff` — decided by `RecursiveLE d` and `RecursiveLE e` alone (`computablePred_le_stepValues`). No `Nat.rfind`, no boundedness test |
| 2 | `RecursiveNormal` for the enumeration (agent3's residue item 4) | **no.** `R47.Agent2.isNormalIn_compacts_iff` asks whether two basis elements of `D → E` are bounded and, if so, whether their join is in the set. Those are exactly the two questions §3 answers, and re-indexing does not remove them |

So both routes are needed, at different places, and neither subsumes the other.
Had I read agent3's report first I would have built §5 before §3 and §4 — the
order test is the cheaper half and it falls out of compactness in twenty lines —
but §3 and §4 would still have been built, because item 2 of that table needs
them.

I re-derived agent3's `directedOn_inter_Iic_of_isNormalIn` independently, as
`directedOn_inter_Iic`, since agent3's branch is not in this worktree.
**It agrees, and it is axiom-free here too** — `#print axioms` reports "does not
depend on any axioms". One difference to record: my proof spends
`[BoundedComplete γ]` to form the join of the pair below `x`; agent3 reports the
result without qualifying the hypothesis. `R47.Agent2.isNormalIn_compacts_iff`
spends the same instance, so this costs nothing at any use site in the
development, but the two statements are not literally the same theorem and the
orchestrator should keep whichever has the weaker binder.

`le_sSup_iff_exists_of_directedOn` — a compact element is below a directed join
exactly when it is below a member — is also axiom-free, and is the whole
mechanism of item 1 above.

## 5. What is still open, precisely

`R49.Agent3.ScottHomCRecursive` and `StrictHomCRecursive` remain open. Against
agent3's four-item residue:

| # | agent3's item | State after this round |
| -- | ------------ | ---------------------- |
| 1 | `Primrec` facts for the `Finset (ℕ × ℕ)` coding | **discharged** |
| 2 | deciding `b ⊑ ⨆{values below a}` in `E` | **discharged** twice over: by `computable_joinIdx` on the `Finset (ℕ × ℕ)` index, and by `computablePred_le_stepValues` with no search on the paper's index |
| 3 | deciding `Consistent (pairsOf d e Q)` | **reduced** to `computablePred_bddAbove`, plus one piece of coding: `Consistent P` quantifies over **subsets** of `P`, so the decision procedure needs `Primrec List.sublists`. That is provable by `Primrec.list_rec` — `sublists (a :: l) = sublists l ++ (sublists l).map (a :: ·)` is a right fold — and needs **no** `Nat.bitwise`, which is the obvious wrong route. I did not build it |
| 4 | `RecursiveNormal` for the enumeration | **open.** It reduces, by `R47.Agent2.isNormalIn_compacts_iff`, to (a) is `⊥` in the finite set of step functions, (b) are two of them bounded in `D → E`, (c) if so, is their join in the set. (b) and (c) are `computablePred_bddAbove` and `computable_joinIdx` **at the presentation being built**, which is circular; the non-circular route is to characterise boundedness of two `ofPairs` sets directly as consistency of their union, which `R47.Agent2.bddAbove_stepsOf_iff` already gives. That is the next concrete step and it is one lemma plus item 3's coding |

On the paper's `(N, s)` index the same table reads: item 3 disappears
(`consistent_stepPairs`), item 2 becomes `computablePred_le_stepValues`, and item
4 is unchanged. **The remaining cost of that route is the index coding** — a
monotone `s : N → K(E)` has to be named by a natural, and its monotonicity
decided; both are finite tests over the decoded index set, so the bridges in §2
of the module cover them, but the enumeration and its `enum_surjective` proof are
a new module of `A2Compactness`'s size, which is what agent3 estimated.

## 6. Declarations

`ScottDomains/ScottDomains/Effective/A4Recursion.lean`, namespace
`ScottDomains.R49.Agent4`. Axioms printed with `scripts/axioms.sh -i
ScottDomains.Effective.A4Recursion`; `[p, C, Q]` abbreviates
`[propext, Classical.choice, Quot.sound]`.

| # | Declaration | Kind | Axioms |
| -- | ---------- | ---- | ------ |
| 1 | `raiseStep` | def | — |
| 2 | `foldl_raiseStep` | theorem | `[propext]` |
| 3 | `raise'_eq_foldl` | theorem | `[propext]` |
| 4 | `primrec₂_raise'` | theorem | `[p, C, Q]` |
| 5 | `idxList` | def | — |
| 6 | `primrec_idxList` | theorem | `[p, C, Q]` |
| 7 | `decodeList` | def | — |
| 8 | `mem_idxList_iff` | theorem | `[p, C, Q]` |
| 9 | `mem_decodeList` | theorem | `[p, C, Q]` |
| 10 | `primrec_decodeList_nat` | theorem | `[p, C, Q]` |
| 11 | `primrec_decodeList_pair` | theorem | `[p, C, Q]` |
| 12 | `mem_ofNat_finset_nat_iff` | theorem | `[p, C, Q]` |
| 13 | `surjective_ofNat_finset_nat` | theorem | `[p, C, Q]` |
| 14 | `primrecRel_mem_ofNat_finset` | theorem | `[p, C, Q]` |
| 15 | `allLt` | def | — |
| 16 | `allLt_eq_true` | theorem | `[propext, Quot.sound]` |
| 17 | `allLt_eq_rec` | theorem | **none** |
| 18 | `computable_allLt` | theorem | `[p, C, Q]` |
| 19 | `computablePred_comp` | theorem | `[p, C, Q]` |
| 20 | `computablePred_and` | theorem | `[p, C, Q]` |
| 21 | `forall_mem_ofNat_finset_iff` | theorem | `[p, C, Q]` |
| 22 | `exists_mem_ofNat_finset_iff` | theorem | `[p, C, Q]` |
| 23 | `computablePred_forall_mem` | theorem | `[p, C, Q]` |
| 24 | `computablePred_exists_mem` | theorem | `[p, C, Q]` |
| 25 | `basisSet` | def | — |
| 26 | `recursiveNormal_iff_basisSet` | theorem | `[p, C, Q]` |
| 27 | `finite_basisSet` | theorem | `[p, C, Q]` |
| 28 | `basisSet_subset_compacts` | theorem | `[p, C, Q]` |
| 29 | `mem_basisSet` | theorem | `[p, C, Q]` |
| 30 | `basisSet_mono` | theorem | `[p, C, Q]` |
| 31 | `NormAt` | def | — |
| 32 | `decidableNormAt` | instance | — |
| 33 | `exists_normal_superset` | theorem | `[p, C, Q]` |
| 34 | `bddAbove_basisSet_iff` | theorem | `[p, C, Q]` |
| 35 | `normCode` | def (noncomputable) | — |
| 36 | `computablePred_normAt` | theorem | `[p, C, Q]` |
| 37 | `computable_normCode` | theorem | `[p, C, Q]` |
| 38 | **`computablePred_bddAbove`** | theorem | `[p, C, Q]` |
| 39 | `mem_of_isLUB_of_isNormalIn` | theorem | `[p, C, Q]` |
| 40 | `JoinIdxAt` | def | — |
| 41 | `exists_joinIdxAt` | theorem | `[p, C, Q]` |
| 42 | `decidableJoinIdxAt` | instance (noncomputable) | — |
| 43 | `joinIdx` | def (noncomputable) | — |
| 44 | `isLUB_enum_joinIdx` | theorem | `[p, C, Q]` |
| 45 | `computablePred_or` | theorem | `[p, C, Q]` |
| 46 | **`computable_joinIdx`** | theorem | `[p, C, Q]` |
| 47 | `directedOn_inter_Iic` | theorem | **none** |
| 48 | `le_sSup_iff_exists_of_directedOn` | theorem | **none** |
| 49 | `stepValues` | def | — |
| 50 | `le_sSup_stepValues_iff` | theorem | `[p, C, Q]` |
| 51 | **`computablePred_le_stepValues`** | theorem | `[p, C, Q]` |

No `sorryAx`, no `axiom`, no `native_decide`, no `ofReduceBool`.

## 7. Blockers re-derived

| # | Recorded claim | Re-derived? | Finding |
| -- | ------------- | ----------- | ------- |
| 1 | "`Primcodable (Finset ℕ)` does not exist" (`Effective/FunctionSpace.lean`, pre-r0045) | yes | **stays false.** Used throughout; r0045's correction holds |
| 2 | "`Nat.bitwise` is an obstruction" (r0046, r0047) | not re-derived — the plan forbade spending the round on it | **it does not appear anywhere in this file**, and the one place it would have been tempting (item 3's subset quantification) has a `Primrec.list_rec` route that avoids it. Recorded as a route, not built |
| 3 | "`REPred` closure is missing" (r0046, r0047) | not re-derived, same reason | `REPred` appears nowhere here; every predicate is `ComputablePred`, and Mathlib's missing closure lemmas for **that** class (`comp`, `and`, `or`, bounded quantifiers) are supplied in §2 of the module |
| 4 | "the join always exists on the paper's index" (agent3, this round) | yes, independently | **stands**, and `directedOn_inter_Iic` is axiom-free here as agent3 reports. One difference: my proof carries `[BoundedComplete γ]` |
| 5 | `Effective.surjective_ofNat_finset`'s warning that `Finset ℕ` has two encodings | yes, by evaluation | **stands, and it bites.** `encode` resolves to `Finset.encodable`; the round-trip through it decodes `{0,2,5}` as `[0,3,9]` |
