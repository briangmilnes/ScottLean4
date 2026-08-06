---
round: r0019
from: orchestrator
to: user
subject: product
date: 2026-0806-15:36
started: 2026-0806-15:32
finished: 2026-0806-15:36
related:
  - plans/r0019-plan-from-orchestrator-to-orchestrator-product.md
  - reports/r0018-report-from-orchestrator-to-user-theorem3.md
---

# r0019 — The product cpo, and Lemma 8 parts 1–3

`ScottDomains/Product.lean`: 119 lines, 0 `sorry`, 0 warnings. Elapsed 4 minutes.
§4 opened.

| # | Criterion | Measurement |
| -- | --------- | ----------- |
| 1 | Builds | 0 errors, 0 warnings |
| 2 | Nothing unproved | 0 `sorry`, no `sorryAx` |
| 3 | Parts 1–3 as order isomorphisms | `prodComm`, `prodAssoc`, `scottHomProd` |
| 4 | Lemma 8 **not** claimed complete | the inventory records 3 of 4 parts; the numbered-results count stays at 6 |

## The one cpo construction that costs no case split

Every earlier cpo in this development needed a `dite`, because `SupSet` is total
while the property that makes the obvious supremum correct is not: `ScottHom`
branches on continuity of the pointwise supremum, `↓a` on whether the supremum
stays below `a`, and `im(p)` avoided a branch only by applying `p` to the result.

`D × E` needs none. Mathlib's `Prod.supSet` takes suprema coordinatewise, and
that is *defined for every set* and automatically the least upper bound on
directed ones — because `isLUB_prod` says a least upper bound in a product is
exactly a pair of least upper bounds. So the instance is two lines plus
directedness of the coordinate images. This is the only construction so far that
Mathlib hands over essentially complete.

## Isomorphism as order isomorphism

The paper's `≅` between cpos is rendered `≃o`. That is faithful rather than
convenient: an order isomorphism between cpos preserves directed suprema
automatically, since least upper bounds are defined by the order alone, so no
separate continuity obligation appears in any of the three parts.

Part 3, `D → (E × F) ≅ (D → E) × (D → F)`, is where the function space meets the
product: a continuous map into a product is exactly a pair of continuous maps
(`ScottContinuous.fst`, `.snd`, `.prodMk` from Mathlib), and the pointwise order
on either side is the same relation, so `map_rel_iff'` is a pair of projections.

## Why part 4 is a separate round

Currying, `D → (E → F) ≅ (D × E) → F`, is not a rearrangement of the same data:
it needs the equivalence between **joint** and **separate** Scott continuity. A
map continuous in each argument separately is continuous jointly only via a
directedness argument on the product, and that is the content of the next round.
Claiming Lemma 8 complete now would misreport it, so the inventory says 3 of 4
and the numbered-results count stays at **6 of 29**.

## Elaboration failures

Two. `ScottContinuous.comp` composes as `g ∘ f` from `hf.comp hg`, so
`ScottContinuous.fst.comp f.scottContinuous` produced `⇑f ∘ Prod.fst` — the
composite in the wrong order; `f.scottContinuous.comp ScottContinuous.fst` is
right. And `map_rel_iff'` has implicit binders, so `constructor` met a `∀` rather
than an `Iff` until `intro f g` came first.

## Totals

Seventeen modules, 2522 lines, 129 theorems, 0 `sorry`, 0 warnings.
Numbered results **6 of 29**. Prose claims **11**. Definitions **7 of ≈13**.
