---
round: r0006
from: orchestrator
to: user
subject: function-space
date: 2026-0806-14:05
started: 2026-0806-13:58
finished: 2026-0806-14:05
related:
  - plans/r0006-plan-from-orchestrator-to-orchestrator-function-space.md
  - reports/r0005-report-from-orchestrator-to-user-powerset-domain.md
---

# r0006 — The continuous function space as a cpo: result

`ScottDomains/ScottHom.lean`: 200 lines, 1 structure, 5 instances, 6 theorems,
2 examples, 0 `sorry`, 0 warnings. Elapsed 7 minutes.

| # | Criterion | Measurement |
| -- | --------- | ----------- |
| 1 | Builds | `lake build` exits 0, 0 errors, 0 warnings, 1.2 s |
| 2 | Nothing unproved | `grep -c sorry` = 0; no `sorryAx` |
| 3 | The instance is usable | `coe_sSup_of_directed` proved; downstream proofs never see the `dite` |
| 4 | Classical dependency confined and reported | `scottContinuous_pointwiseSup` uses `propext` and `Quot.sound` only — **no `Classical.choice`**. `Classical.choice` enters exactly at `coe_sSup_of_directed` and the `SupSet` instance, as predicted |

## The plan revision was the right call

The plan was written before r0005 and carried a revision point. r0005 closed the
concern it named — the r0004 class shapes gave no trouble against a
`CompleteLattice`-derived instance — but raised a different one by contrast: in
r0005 every order instance came from Mathlib, already coherent, whereas here they
are built by hand and `CompletePartialOrder` extends `PartialOrder`, `SupSet` and
`OrderBot`. Declaring a standalone `PartialOrder` and then a separate
`CompletePartialOrder` would have produced two unrelated `LE (ScottHom α β)`
instances — the same instance diamond that broke an `Iff.rfl` in r0004.

The revision replaced the standalone `OrderBot` with a plain definition
(`ScottHom.const`) and had the `CompletePartialOrder` instance splice its parents
from the instances in scope. Two examples in the file now check that this holds:

```
example : (inferInstance : PartialOrder (ScottHom α β)) =
    CompletePartialOrder.toPartialOrder := rfl
example : (inferInstance : SupSet (ScottHom α β)) = CompletePartialOrder.toSupSet := rfl
```

Both are `rfl`, so the parents are definitionally the standalone instances. If the
splice is ever undone these two lines stop typechecking — the property is
maintained by the build rather than by memory.

## The one real proof

`scottContinuous_pointwiseSup`: the pointwise supremum of a directed set `d` of
Scott-continuous functions is Scott-continuous. The plan's four-step argument went
through unchanged, and the point of it is what it *avoids*. The obvious route is
to expand `F(⨆s)` and `⨆(F''s)` into iterated suprema and exchange them, which
costs a directedness proof for each intermediate set. Instead:

1. the evaluation image `(· x) '' d` is directed, because `d` is directed
   pointwise — the only place the pointwise order is unfolded;
2. `F` is monotone, by `DirectedOn.sSup_le` on that image;
3. `F a` bounds `F '' s`, from 2;
4. `F a` is least: for an upper bound `u` of `F '' s`, `DirectedOn.sSup_le`
   reduces the goal to `f a ≤ u` for each `f ∈ d`; continuity of `f` reduces that
   to `f x ≤ u` for `x ∈ s`; and `f x ≤ F x ≤ u`.

No exchange, and no directedness argument beyond step 1. It costs `propext` and
`Quot.sound` and no choice.

## `SupSet` is total; continuity is not

`CompletePartialOrder` extends `SupSet`, so `sSup` must return a `ScottHom` for
*every* set of functions — but the pointwise supremum of a non-directed set need
not be continuous (step 2 above fails without directedness), and in a dcpo the
supremum of a non-directed set is unconstrained regardless. `sSup` is therefore
defined by `dite` on directedness, with the constant-`⊥` function as the junk
value. `CompletePartialOrder` constrains `sSup` only on directed sets, so no
consumer can observe the junk, and `coe_sSup_of_directed` strips the case split
once and for all. The price is `Classical.choice` in that theorem and in the
instance — confined to exactly those two, which is what criterion 4 measures.

## Three elaboration failures

**`FunLike`'s injectivity field is `coe_injective`, not `coe_injective'`.** The
primed name is the field of the `DFunLike` *constructor helper* in older Mathlib.

**The `__ :=` parent splice does not work in `where` syntax here.**
`__ := inferInstanceAs (PartialOrder (ScottHom α β))` failed with "expected type
contains metavariables" — inside a `where` block the parent's type is not yet
determined when the term is elaborated. The term-mode idiom
`{ (inferInstance : PartialOrder _), (inferInstance : SupSet _) with … }` does
work, and is what Mathlib uses.

**`PartialOrder.lift` leaves a beta-redex in the goal.** After `intro f hf x` the
goal read `(fun f => ⇑f) f x ≤ (fun f => ⇑f) (sSup d) x`, so `rw` could not find
the pattern `(sSup d) ?x`. `dsimp only` beta-reduces and the rewrite then fires.
This is the third round in a row where the failure was about the *form* a term
has after elaboration rather than about the mathematics.

## What this does and does not deliver

It delivers the first sentence of Theorem 7's proof — "It is not hard to see that
`D → E` is a bounded complete cpo whenever `E` is" — minus bounded completeness,
which needs suprema of *bounded* rather than directed families and a different
continuity argument. It does not deliver a numbered result. The counts stay at
**9 definitions and 28 results remaining**; what changed is that the object
Theorem 7, Lemmas 8, 9, 10, 17, 23, Theorem 18 and the `D∞` construction all
quantify over now exists and is a cpo.

`docs/PaperInventory.md` now carries the progress table at the top of the file,
and `PaperInventory.pdf` was regenerated from it: 4 pages, 82,998 bytes, exit 0,
no missing glyphs.

## Next

The step-function basis. Given finite `N ⊆ K(D)` and monotone `s : N → K(E)`, the
step function is compact in `ScottHom`, and these form a basis — which turns
r0006's cpo into a `Domain` and, with bounded completeness, yields **Theorem 7**,
the first of the 28 numbered results.
