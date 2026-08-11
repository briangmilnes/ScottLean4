---
round: r0053
from: agent1
to: orchestrator
subject: scotthomc-recursive
date: 2026-0810-19:26
started: 2026-0810-18:47
finished: 2026-0810-19:26
related: plans/r0053-plan-from-orchestrator-to-agent1-scotthomc-recursive.md
---

# r0053 / agent1 — root hole 1: both obligations proved, under one added instance

## 1. Result in one line

`Computable.RecursiveLE (scottHomC d e)` and `Effective.RecursiveNormal
(scottHomC d e)` are both **proved and kernel-checked**, from `IsRecursive d` and
`IsRecursive e`, in a new module
`ScottDomains/ScottDomains/Effective/ScottHomCRecursive.lean` (1061 lines, 69
declarations). The proofs carry **one instance binder the root statement does not
have**, `[BoundedComplete α]`, so `R49.Agent3.scottHomCRecursive_unproven` is left
exactly as it was and the `sorry` count does not fall. Section 5 states precisely
where that instance is spent and why it is not removable by rearranging the
proof.

## 2. Measurements

| # | Quantity | Before | After |
| - | -------- | ------ | ----- |
| 1 | `lake build` jobs | 1372 | 1373 |
| 2 | Lean diagnostics (errors) | 0 | 0 |
| 3 | warnings other than `sorry` | 0 | 0 |
| 4 | `sorry` declarations | 3 | 3 |
| 5 | files changed under `ScottDomains/ScottDomains/` | — | 1 added, 0 modified |
| 6 | `A3StepDecidable.lean` vs `main` | — | byte-identical (`git diff main --stat` empty) |

Build log: `ScottDomains/logs/compile-20260810-192553.agent1.log`
(exit 0, wall 0:02.12 incremental, 1373 jobs, 0 diagnostics, 0 lake errors,
3 `sorry` declarations, 0 other warnings).

## 3. The new theorems and their axiom footprints

Every declaration below is in namespace `ScottDomains.R53.Agent1`, in the module
`ScottDomains.Effective.ScottHomCRecursive`. All binders in force are
`{α β : Type*} [CompletePartialOrder α] [Domain α] [BoundedComplete α]
[CompletePartialOrder β] [Domain β] [BoundedComplete β]`,
`(d : EffectivePresentation α) (e : EffectivePresentation β)`.

| # | Theorem | Statement |
| - | ------- | --------- |
| 1 | `recursiveLE_scottHomC` | `IsRecursive d → IsRecursive e → RecursiveLE (scottHomC d e)` |
| 2 | `recursiveNormal_scottHomC` | `IsRecursive d → IsRecursive e → RecursiveNormal (scottHomC d e)` |
| 3 | `scottHomCRecursive_of_boundedComplete` | `R49.Agent3.ScottHomCRecursive d e` |
| 4 | `stepFunctionsDecidable_of_boundedComplete` | `Effective.StepFunctionsDecidable d e` |

`scripts/axioms.sh` output, verbatim:

```
'ScottDomains.R53.Agent1.recursiveLE_scottHomC' depends on axioms: [propext, Classical.choice, Quot.sound]
'ScottDomains.R53.Agent1.recursiveNormal_scottHomC' depends on axioms: [propext, Classical.choice, Quot.sound]
'ScottDomains.R53.Agent1.scottHomCRecursive_of_boundedComplete' depends on axioms: [propext, Classical.choice, Quot.sound]
'ScottDomains.R53.Agent1.stepFunctionsDecidable_of_boundedComplete' depends on axioms: [propext, Classical.choice, Quot.sound]
'ScottDomains.R53.Agent1.computablePred_consistent' depends on axioms: [propext, Classical.choice, Quot.sound]
'ScottDomains.R53.Agent1.isNormalIn_basisSet_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'ScottDomains.R53.Agent1.consistentEnum_le_iff_index' depends on axioms: [propext, Classical.choice, Quot.sound]
'ScottDomains.R53.Agent1.computable_setCode' depends on axioms: [propext, Classical.choice, Quot.sound]
'ScottDomains.R53.Agent1.primrec_sublistsAux' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No `sorryAx` anywhere. No `axiom` is declared in the module.

## 4. The named intermediate results

| # | Declaration | Content |
| - | ----------- | ------- |
| 1 | `computablePred_forall_mem_list`, `computablePred_exists_mem_list` | bounded quantification over a **computable list**, for an arbitrary `Primcodable` element type. `R49.Agent4`'s versions quantify only over a decoded `Finset ℕ`; two of the searches here run over a decoded `Finset (ℕ × ℕ)` and one over a list of sublists |
| 2 | `computablePred_imp` | the third `ComputablePred` closure fact, after `R49.Agent4.computablePred_and` and `computablePred_or` |
| 3 | `sublistsAux`, `primrec_sublistsAux`, `filter_mem_sublistsAux` | the power set of a finite list as a **primitive recursive** list of lists. Mathlib states no `Primrec` fact for `List.sublists'`; this is `Primrec.list_rec` over `l.sublists'`'s own recursion |
| 4 | `SetCodeAt`, `setCode`, `mem_ofn_setCode`, `computable_setCode` | a **computable `Finset` code** for a set cut out by a computable membership test inside a computable list of candidates. Instantiated three times: `finsetCode` (entries of a list), `belowValCode` (values below `dᵢ`), `unionPairCode` (union of two index sets) |
| 5 | `computablePred_bddAbove_list` | `R49.Agent4.computablePred_bddAbove` with the index set given as a list |
| 6 | `consistent_pairsOf_iff` | **`Consistent (pairsOf d e Q)` is a bounded condition**: `∀ T` a sublist of the decoded index list, sources bounded in `D` → values bounded in `E`. Every subset of `pairsOf d e Q` is the image of such a sublist, the witness being `List.filter` |
| 7 | `computablePred_consistent` | `ComputablePred fun n => Consistent (pairsOf d e (ofNat (Finset (ℕ × ℕ)) n))` — **the guard `R47.Agent2.consistentEnum` branches on is decidable from `d` and `e`**, which is what r0047 asserted and did not prove |
| 8 | `normPairCode`, `consistentEnum_eq_ofPairs`, `computable_normPairCode` | every value of the enumeration is `ofPairs` of a **consistent** index set, at a computable code. This removes the `if` from every statement downstream |
| 9 | `belowValCode`, `enum_joinBelow` | a computable **index** for `⨆{values below dᵢ}`, so agent3's residue item "a decision procedure for `b ⊑ ⨆{values below a}` in `E`" becomes a `≤` between two basis elements of `E` |
| 10 | `consistentEnum_le_iff_index` | the order test with every atom a `≤` between basis indices: `f_m ≤ f_n ↔ ∀ q ∈ Q'_m, e_{q.2} ⊑ e_{joinBelow n q.1}` |
| 11 | `consistent_unionPairCode_of_le`, `isLUB_pair_consistentEnum` | **the mub fact `Effective/FunctionSpace.lean` item 4 asks for**: two enumerated functions are bounded above exactly when the union of their index sets is consistent, and the enumeration's value at a code for that union is then their least upper bound |
| 12 | `isNormalIn_basisSet_iff` | normality of a finite set of enumerated functions as a finite condition on the index sets. Note it does **not** need `[BoundedComplete (ScottHom α β)]`, unlike `R47.Agent2.isNormalIn_compacts_iff`, because the mub is exhibited rather than obtained from `sSup` |

## 5. The added instance `[BoundedComplete α]` — where, and why it stays

It is spent at exactly one atom. `Consistent (pairsOf d e Q)` asks, of each subset
of the index set, whether its **sources** are bounded above in `D`.
`R49.Agent4.computablePred_bddAbove` decides boundedness of a finite set of basis
elements and carries `[BoundedComplete γ]`, because its route —
`R47.Agent2.bddAbove_iff_exists_normal` through `isNormalIn_joinClosure` — needs
the join of a bounded pair of compacts to exist so that the join closure is a
*finite normal* superset.

Dropping bounded completeness of `D` does not delete the test, it demotes it.
In an algebraic cpo the compacts below any element are directed, so a finite set
of compacts is bounded above exactly when some **compact** bounds it; that makes
"bounded" a `Σ₁` condition on the indices (search for a bounding index, testing
with `RecursiveLE d`) and therefore makes `Consistent` a `Π₁` condition. A `Σ₁`
test is not a decision procedure, and this development contains no theorem making
it one. I did not attempt to refute decidability in the general case, and do not
claim it is false — only that it is not available.

Two supporting observations, recorded because they bear on how the orchestrator
may want to close this:

1. `Domain` in this development is `IsAlgebraic` plus a countable basis. Gunter &
   Scott's "domain" in Theorem 7 is bounded complete, which is already why
   `[BoundedComplete β]` appears on every statement about `D → E` here. The
   instance added is the same hypothesis moved to `D`.
2. `consistentEnum_le_iff_index` — the whole order-theoretic reduction — does not
   use `[BoundedComplete α]`. Only the two *computability* steps do
   (`computablePred_consistent` and, through it, everything downstream).

## 6. What remains open

| # | Item | State |
| - | ---- | ----- |
| 1 | `R49.Agent3.scottHomCRecursive_unproven` (`A3StepDecidable.lean:200`) | **still sorried, untouched.** Its binder list has no `[BoundedComplete α]`, so nothing here discharges it as stated. The exact remaining goal is `ScottHomCRecursive d e` under `{α β : Type*} [CompletePartialOrder α] [Domain α] [CompletePartialOrder β] [Domain β] [BoundedComplete β]`; the single missing input is `ComputablePred fun n : ℕ => BddAbove (R49.Agent4.basisSet d n)` without `[BoundedComplete α]` |
| 2 | `Effective.Theorem7ArrowRecursive` | not reached. `R47.Agent2.theorem_7_arrowRecursive_of_scottHomC` takes a hypothesis quantified over all `α`, `β` with `[BoundedComplete β]` only, and a hypothesis cannot acquire the extra binder. Reaching it needs either item 1 or a restatement of that reduction with `[BoundedComplete α]` in the quantifier — a change to `A2Compactness.lean`, which I did not make |
| 3 | `R49.Agent3.strictHomCRecursive_unproven` (`A3StepDecidable.lean:386`) | untouched; that is agent2's half this round |
| 4 | `ScottDomains/Lemma30.lean:535` | untouched |

Two decisions for the orchestrator:

1. **Add `[BoundedComplete α]` to `ScottHomCRecursive` and its consumers?** That
   would let `scottHomCRecursive_unproven` be replaced by
   `scottHomCRecursive_of_boundedComplete` and remove one root `sorry`. It is a
   change to `A3StepDecidable.lean` and to `A2Compactness.lean`'s two reduction
   theorems, and it changes what the claims say — so it is a decision, not a
   merge detail. My recommendation is to make it, with the docstring stating that
   the instance is the paper's own hypothesis on `D`; but I did not make it,
   because the plan says `A3StepDecidable.lean` must stay byte-identical.
2. **Or leave the root sorried** and cite this module as the measurement of the
   exact gap. Either way, nothing in the development acquires `sorryAx` from this
   round.

## 7. Two notes on elaboration cost, for whoever edits this module next

Both cost real time this round and neither is mathematical.

1. `emptyPairCode` is specified by `Classical.choose`, not `Nat.find`. With
   `Nat.find` and the real `DecidableEq (Finset (ℕ × ℕ))` instance, an `isDefEq`
   query meeting the constant tries to *evaluate* the search, which runs into
   `Nat.unpair`'s `Nat.sqrt` — the stuck reduction `R49.Agent4`'s section 1
   records. A constant is computable however it is specified.
2. In `computablePred_union_eq` the two `computablePred_comp` applications are
   bound to `g1`, `g2` before being passed to `computablePred_and`. Written
   inline, the two `ComputablePred` metavariables are solved against each other,
   the elaborator unfolds `R47.Agent2.consistentEnum` looking for a match, and the
   declaration does not finish inside 2,000,000 heartbeats. Bound first, the same
   proof elaborates in about a second. The same pattern — give every `Computable`
   intermediate an explicit type — is why `computablePred_bot_mem` and
   `computable_belowValCode` are written the way they are.
