---
round: r0053
from: agent2
to: orchestrator
subject: stricthomc-recursive
date: 2026-0810-19:21
started: 2026-0810-18:49
finished: 2026-0810-19:21
related: plans/r0053-plan-from-orchestrator-to-agent2-stricthomc-recursive.md
---

# r0053 / agent2 — goal A landed: `StrictHomCRecursive` is a consequence of `ScottHomCRecursive`

## 1. Result

Goal A closed. Goal B was not attempted and is not needed.

    ScottDomains.R53.Agent2.strictHomCRecursive_of_scottHomC
      {α β : Type*} [CompletePartialOrder α] [Domain α]
      [CompletePartialOrder β] [Domain β] [BoundedComplete β] [Domain (StrictHom α β)]
      (d : EffectivePresentation α) (e : EffectivePresentation β)
      (h : R49.Agent3.ScottHomCRecursive d e) : R49.Agent3.StrictHomCRecursive d e

Axiom footprint `[propext, Classical.choice, Quot.sound]`. No `sorryAx`, no
`axiom`, no `Classical.propDecidable` standing in for a decision procedure, no
weakened `def`, no hypothesis that is the claim.

This is a **conditional** result and closes no `sorry`. What it removes is a root:
after it, `R49.Agent3.strictHomCRecursive_unproven` is a corollary of
`R49.Agent3.scottHomCRecursive_unproven`. The root count goes from **3 to 2**
(`R49.Agent3.scottHomCRecursive_unproven`, `Lemma30.lean:535`).

The `⊸` half of the paper's Theorem 7 now also follows from the arrow residue
alone:

    ScottDomains.R53.Agent2.theorem_7_strictRecursive_of_scottHomC.{u}
      (h : ∀ {α β : Type u} [CompletePartialOrder α] [Domain α]
        [CompletePartialOrder β] [Domain β] [BoundedComplete β]
        (d : EffectivePresentation α) (e : EffectivePresentation β),
        R49.Agent3.ScottHomCRecursive d e) :
      Effective.Theorem7StrictRecursive.{u, u}

so `R49.Agent3.three_claims_of_residue` is now four claims from one residue, and
`R49.Agent3.theorem_7_strictRecursive_of_residue`'s hypothesis is discharged from
the arrow residue rather than assumed.

## 2. Measurements

| # | Quantity | Before | After |
| - | -------- | ------ | ----- |
| 1 | `sorry` declarations, whole library | 3 | 3 |
| 2 | independent open statements (roots) | 3 | 2 |
| 3 | `lake build` jobs | 1372 | 1373 |
| 4 | build errors / warnings other than `sorry` | 0 / 0 | 0 / 0 |
| 5 | new module, lines | — | 665 |
| 6 | new `theorem`/`def` declarations | — | 48 |
| 7 | files edited outside the new module | — | `INDEX.md` only |

`ScottDomains/ScottDomains/Effective/A3StepDecidable.lean` is **byte-identical to
`main`** (`git diff --stat main -- …A3StepDecidable.lean` is empty), as the plan
requires. The orchestrator's one-line rewire of
`strictHomCRecursive_unproven` is still available and is not done here.

Build log: `ScottDomains/logs/compile-20260810-192054.agent2.log`
(1373 jobs, exit 0, 0 diagnostics, 0 lake errors, 3 `sorry` declarations,
0 other warnings; wall 0:00.84 on a fully replayed tree, 15 s for the one new
module).

## 3. How goal A was closed, step by step against the plan's table

The plan's step 1 is the whole content and it is now proved. Steps 2 and 3 came
out differently from the plan's guess, and the difference is worth recording.

### Step 1 — the injection is computable in the codings: **proved**

`R46.Agent3.strictPairsOf d e Q` is `Effective.pairsOf d e Q` cut down by a
condition on the *pair of indices* — that is exactly what
`R46.Agent3.isStrict_iff_of_isStepPair` buys — so it is `pairsOf d e` of a
**sub-finset** of `Q`. Hence the index map is a `Finset.filter` in the codes:

    R53.Agent2.strictCode d e n := filterCode (strictTest d e) n

    R53.Agent2.pairsOf_ofNat_strictCode :
      Effective.pairsOf d e (Denumerable.ofNat (Finset (ℕ × ℕ)) (strictCode d e n))
        = R46.Agent3.strictPairsOf d e (Denumerable.ofNat (Finset (ℕ × ℕ)) n)

    R53.Agent2.consistentEnum_strictCode [Domain (StrictHom α β)] :
      consistentEnum d e (strictCode d e n) = (strictConsistentEnum d e n).val

The last line is the fact r0052 recorded as missing: the injection
`K(D ⊸ E) ↪ K(D → E)` now *names an enumeration index*. Its computability is

    R53.Agent2.computable_strictCode (hd : RecursiveLE d) (he : RecursiveLE e) :
      Computable (strictCode d e)

and it needs only **condition 1** of `d` and of `e` — not condition 2, and not
`IsRecursive (scottHomC d e)`. Three pieces went into it.

* **Bottom-ness is decided by condition 1.** `⊥` is compact, so it has some index
  `i₀`, and `dᵢ = ⊥` is `dᵢ ⊑ d_{i₀}`:
  `R53.Agent2.computablePred_enum_eq_bot (hd : RecursiveLE d) :
  ComputablePred fun i => d.enum i = ⊥`. No search.
  Hence `R53.Agent2.computable_strictTest`: the strictness condition on an index
  pair is decided by a total recursive function.
* **The encoding half of the `Denumerable (Finset _)` coding.** r0049's
  `Effective/A4Recursion.lean` had the *decoding* half
  (`R49.Agent4.primrec₂_raise'`, `idxList`, `primrec_idxList`, `mem_idxList_iff`),
  which this file imports and reuses. What was absent is `Denumerable.lower'` —
  needed because a code *map* must produce a code, not only read one. It is a
  left fold with a two-component state: `R53.Agent2.primrec_lower'`. With it,
  `R53.Agent2.filterCode` and `R53.Agent2.ofNat_finset_filterCode :
  ofNat (Finset α) (filterCode q n) = (ofNat (Finset α) n).filter (q ∘ encode)`,
  for every denumerable `α`.
* **List operations at the `Computable` level.** Mathlib's `Computable` namespace
  has no list recursor at all — its list API is `list_cons`, `list_reverse`,
  `list_getElem?`, `list_append`, `list_concat`, `list_length` — and the element
  map here is computable, not primitive recursive, so `Primrec.list_map` and
  `Primrec.list_flatMap` do not apply. `R53.Agent2.computable_flatMap` supplies the
  engine (a `Computable.nat_rec` over the indices with the pair
  (remaining, output) as state), and `computable_list_filter`,
  `computable_list_map` follow.

### Step 2 — "the image of the injection is a recursive subset": **not needed**

The plan expected the image of `K(D ⊸ E)` inside `K(D → E)` to have to be
recognized. It does not, because the map runs the other way: **every** index of
the strict enumeration is carried to an index of the arrow enumeration, and the
transport only ever pushes forward. Nothing has to decide whether a given arrow
index is in the image.

The decidability the round actually needed is one level down and is proved:
strictness of an index *pair* (`computable_strictTest`), which is what cuts
`pairsOf` down to `strictPairsOf`. It is decided from condition 1 of `d` and `e`.

### Step 3 — the transport lemma: **proved, in a different shape**

`RecursiveLE` transports by precomposition with `strictCode d e` and nothing else
(`R53.Agent2.recursiveLE_strictHomC`), because the order on `StrictHom α β` is the
subtype order.

`RecursiveNormal` needed two things.

* **The domain-theoretic transport.**

      R53.Agent2.isNormalIn_val_image_iff {N : Set (StrictHom α β)} :
        N ◁ compacts (StrictHom α β) ↔ (Subtype.val '' N) ◁ compacts (ScottHom α β)

  Both sides are read through `R47.Agent2.isNormalIn_compacts_iff` — over a
  bounded complete cpo, `N ◁ K(D)` is "consists of compacts, contains `⊥`, closed
  under the binary joins that exist" — and each conjunct matches its image:
  compactness by `ClosureProperties.isCompactElement_val_of_isCompactElement` and
  its converse; `⊥` because `(⊥ : D ⊸ E).val = ⊥`; the joins by
  `R53.Agent2.isLUB_pair_val_iff`, whose content is
  `R53.Agent2.isStrict_of_isLUB_pair` — a least upper bound of two strict
  functions is strict, proved from the retraction
  `ClosureProperties.strictHom` and the adjunction `R53.Agent2.le_strictHom_iff`.

  A prerequisite was missing and is supplied:
  `R53.Agent2.boundedComplete_strictHom : BoundedComplete (StrictHom α β)` from
  `[BoundedComplete β]` alone. `Skeleton.lemma_10_strict` proves the same
  proposition but asks for `[Domain α] [BoundedComplete α] [Domain β]`, and
  `R49.Agent3.StrictHomCRecursive` grants no `BoundedComplete α`.

* **The image code map.** `RecursiveNormal` is indexed by a code for a
  `Finset ℕ`, so the transport needs the code of `u.image (strictCode d e)`.
  `Finset.image` does not preserve the sorted order the coding stores, so it
  cannot be computed by rewriting the decoded list in place. It is computed by
  re-scanning: the image is bounded by the sum of the mapped list, so filtering
  `List.range (bound + 1)` by membership in the mapped list yields the sorted,
  duplicate-free list the coding wants — `R53.Agent2.imageCode`,
  `ofNat_finset_imageCode`, `computable_imageCode`. **No sorting algorithm had to
  be shown primitive recursive**, which was the visible risk in this step.

## 4. New declarations and their axiom footprints

Every one is `[propext, Classical.choice, Quot.sound]`; none carries `sorryAx`.

| # | Declaration | Statement |
| - | ----------- | --------- |
| 1 | `strictHomCRecursive_of_scottHomC` | `ScottHomCRecursive d e → StrictHomCRecursive d e` |
| 2 | `theorem_7_strictRecursive_of_scottHomC` | universal `ScottHomCRecursive` → `Effective.Theorem7StrictRecursive` |
| 3 | `recursiveLE_strictHomC` | `RecursiveLE d → RecursiveLE e → RecursiveLE (scottHomC d e) → RecursiveLE (strictHomC d e)` |
| 4 | `recursiveNormal_strictHomC` | `RecursiveLE d → RecursiveLE e → RecursiveNormal (scottHomC d e) → RecursiveNormal (strictHomC d e)` |
| 5 | `consistentEnum_strictCode` | `consistentEnum d e (strictCode d e n) = (strictConsistentEnum d e n).val` |
| 6 | `pairsOf_ofNat_strictCode` | `pairsOf d e (ofNat _ (strictCode d e n)) = strictPairsOf d e (ofNat _ n)` |
| 7 | `computable_strictCode` | `RecursiveLE d → RecursiveLE e → Computable (strictCode d e)` |
| 8 | `computable_strictTest` | the strictness test on an index pair is total recursive |
| 9 | `computablePred_enum_eq_bot` | `RecursiveLE d → ComputablePred fun i => d.enum i = ⊥` |
| 10 | `isNormalIn_val_image_iff` | `N ◁ K(D ⊸ E) ↔ val '' N ◁ K(D → E)` |
| 11 | `isLUB_pair_val_iff`, `isStrict_of_isLUB_pair`, `le_strictHom_iff` | the retraction facts the transport runs on |
| 12 | `boundedComplete_strictHom` | `BoundedComplete (StrictHom α β)` from `[BoundedComplete β]` alone |
| 13 | `primrec_lower'` | `Primrec fun l => Denumerable.lower' l 0` |
| 14 | `filterCode`, `ofNat_finset_filterCode`, `computable_filterCode` | `Finset.filter` in the `Denumerable (Finset α)` codes |
| 15 | `imageCode`, `ofNat_finset_imageCode`, `computable_imageCode` | `Finset.image` in the `Denumerable (Finset ℕ)` codes |
| 16 | `computable_flatMap`, `computable_list_filter`, `computable_list_map` | `List.flatMap`/`filter`/`map` by a *computable* element map |

Rows 13–16 are general-purpose and are stated with no domain theory in them; they
are the pieces the arrow half will want too.

## 5. Reuse, and one duplication caught and removed

The first draft restated `Denumerable.raise'`'s primitive recursiveness and the
`ofNat (Finset α)` membership lemma. Both already exist in r0049's
`Effective/A4Recursion.lean` (`R49.Agent4.primrec₂_raise'`, `idxList`,
`primrec_idxList`, `mem_idxList_iff`, `mem_ofNat_finset_nat_iff`). The module now
imports `Effective/A4Recursion.lean` and uses those; the duplicated ~40 lines were
deleted before commit. Only the encoding half (`lower'`) and the two code maps
are new.

## 6. Acceptance criteria

| # | Criterion | Result |
| - | --------- | ------ |
| 1 | `scripts/compile.sh -r r0053` reports 0 errors and 0 warnings other than `sorry` | met — 1373 jobs, 0 diagnostics, 0 lake errors, 0 other warnings |
| 2 | the `sorry` count does not rise | met — 3 before, 3 after |
| 3 | every new theorem's `#print axioms` shows no `sorryAx` | met — 16 declarations checked, all `[propext, Classical.choice, Quot.sound]` |
| 4 | `A3StepDecidable.lean` byte-identical to `main` | met |
| 5 | committed with `scripts/gitcp.sh` on branch `agent2`, not pushed | met |
| 6 | this report with `started:`/`finished:` | met |

## 7. What the orchestrator may want to do at merge

1. Rewire `R49.Agent3.strictHomCRecursive_unproven` to
   `R53.Agent2.strictHomCRecursive_of_scottHomC` applied to
   `R49.Agent3.scottHomCRecursive_unproven`, which deletes one `sorry` from
   `A3StepDecidable.lean` and leaves the library at 2. That edit was deliberately
   not made here because agent1 holds the same file this round.
2. If agent1's round closes `ScottHomCRecursive` unconditionally, this file makes
   the `⊸` half fall with it and no further work is needed there.
3. `primrec_lower'`, `filterCode`, `imageCode` and the three `Computable` list
   lemmas are usable by the arrow half as they stand.
