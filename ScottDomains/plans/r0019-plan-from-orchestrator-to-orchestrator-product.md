---
round: r0019
from: orchestrator
to: orchestrator
subject: product
date: 2026-0806-15:32
status: done
related:
  - reports/r0019-report-from-orchestrator-to-user-product.md
---

# r0019 — The product cpo, and Lemma 8 parts 1–3

> **Lemma 8** Let `D`, `E` and `F` be cpo's, then
> 1. `D × E ≅ E × D`,
> 2. `(D × E) × F ≅ D × (E × F)`,
> 3. `D → (E × F) ≅ (D → E) × (D → F)`,
> 4. `D → (E → F) ≅ (D × E) → F`.

Deliverable: `ScottDomains/Product.lean`.

## Scope, and why part 4 is separate

Parts 1–3 are structural: they follow from the coordinatewise description of
suprema and of the order. Part 4 is **currying**, and it needs the equivalence of
joint and separate Scott continuity — a real theorem, not a rearrangement. It is
r0020.

## The one construction Mathlib nearly hands over

`Prod.supSet` (`Order/CompleteLattice/Basic.lean:913`) takes suprema
coordinatewise and `isLUB_prod` (`Order/Bounds/Image.lean:363`) says a least
upper bound in a product is a pair of them. So `CompletePartialOrder (α × β)` is
two lines plus the directedness of the coordinate images.

Unlike `ScottHom`, `im(p)` and `↓a`, **no `dite` is needed**: the coordinatewise
supremum is defined for every set and is automatically the least upper bound on
directed ones. This is the only cpo construction so far that costs no case split.

## Isomorphism means order isomorphism

The paper's `≅` is isomorphism of cpos. An order isomorphism between cpos
preserves directed suprema automatically — least upper bounds are defined by the
order — so `≃o` is the faithful rendering and no separate continuity obligation
appears.

## Steps

| # | Step | Verify |
| -- | ---- | ------ |
| 1 | `directedOn_fst_image`, `directedOn_snd_image` | projections are monotone |
| 2 | `instance : CompletePartialOrder (α × β)` | `isLUB_prod` plus step 1 |
| 3 | Lemma 8.1 `prodComm` | swap; the order is coordinatewise |
| 4 | Lemma 8.2 `prodAssoc` | reassociate |
| 5 | `ScottHom.fstComp`, `.sndComp`, `.pair` | `ScottContinuous.fst/.snd/.prodMk` |
| 6 | Lemma 8.3 `scottHomProd` | step 5 both ways; the pointwise orders agree |

## Acceptance criteria

| # | Criterion | Measurement |
| -- | --------- | ----------- |
| 1 | Builds | 0 errors, 0 warnings |
| 2 | Nothing unproved | 0 `sorry`, no `sorryAx` |
| 3 | Parts 1–3 as order isomorphisms | three `≃o` definitions |
| 4 | Lemma 8 **not** claimed complete | the inventory records 3 of 4 parts |
