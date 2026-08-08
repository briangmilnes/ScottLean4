import ScottDomains.PRepFun
import ScottDomains.PRepSum

/-!
# Lemma 28 over the paper's own `U`, with r0037's two streams joined

Round r0037 split Lemma 28's seven open conjuncts across two agents:

* `ScottDomains.PRepFun` (agent3) proved `→`, `⇸` and `⊗`, each **conditional on
  the paper's retraction pair** for the operator;
* `ScottDomains.PRepSum` (agent4) derived that pair at §7.3's `U` — as `pairAtU`,
  four lines from the now-unconditional `Atomless.thm27` — and used it to land
  `×`, `+`, `⊕` and `()⊥` at `U` with no hypothesis.

Neither could take the last step. They ran in separate worktrees and could not
see each other's work; agent3 deliberately did not attempt the instantiation, to
avoid colliding with agent4. This module is that join, and it belongs to neither
stream.

## What the join costs

Nothing mathematical. Theorem 27's hypothesis is that the operator's *result* be
a bounded complete domain, so each conjunct needs two instances and then reads
off `pairAtU`:

| # | Operator | `Domain` of the result | `BoundedComplete` of the result |
| - | -------- | ---------------------- | ------------------------------- |
| 1 | `→`  | Theorem 7, by `inferInstance`      | Theorem 7, by `inferInstance` |
| 2 | `⇸`  | `PRepFun.strictHomDomain` (r0037)  | `lem10_strict` (r0027) |
| 3 | `⊗`  | `PRepFun.smashDomain` (r0037)      | `lem10_smash` (r0027) |

The right-hand column is **Lemma 10**. That is the sense in which Lemma 10 and
Lemma 28 compose, and it is why the two `Domain` instances agent3 had to prove
were the whole obstacle: before r0037 neither `Domain (D →⊥ E)` nor
`Domain (D ⊗ E)` existed anywhere in the development, so none of these three
conjuncts could have lifted no matter how they were proved.

## Position

**7 of Lemma 28's 9 conjuncts now hold over `Dyadic.U` with no hypothesis**, up
from 0 before r0037 and 4 after agent4's stream. `lemma28AtU_of'` records the
remainder: its arity is 2, against `PRep.lemma28_of`'s 9 and
`PRepSum.lemma28AtU_of`'s 5.

`()♯` and `()♭` are what is left, and their obstruction is *not* the definability
one earlier rounds recorded — `smythOp` and `hoareOp` are definable on `Cpo`
(r0036). Measured by grep in r0037: the development defined **no action of a map
on either powerdomain**, so there was no `r ↦ r♯` from which to build the
conjugating family.

**Superseded (r0041).** Both halves of that paragraph are now settled and neither
came out the way it was written.

1. The action exists: `ScottDomains.PowerdomainMap` builds `f♮`, `f♯` and `f♭`
   the paper's own way, `f♮ = ext({|·|} ∘ f)` — Theorem 12 with the target
   powerdomain as its algebra — with the naturality square, uniqueness, both
   functor laws, and `isProjection_smyth`/`isProjection_hoare`: a projection acts
   as a projection.
2. `p(K(D)) ⊆ K(D)` is **false**, already for a finitary projection —
   `PowerdomainCompacts.finitaryProjection_not_maps_compacts`. It was never the
   step to settle first: `ext` quantifies over ideals and never over a
   transported basis, so the paper's construction does not ask for it.

`ScottDomains.PowerdomainMapRep.lemma28AtU_of''` replaces `lemma28AtU_of'`'s two
hypotheses with four, and the four are of a different kind: two per powerdomain,
each an ordinary statement about the functor — `im(p♯) ≅ (im p)♯` and pointwise
continuity of `p ↦ p♯` — with the retraction pair at `U` discharged by
`PRepSum.pairAtU`, since Lemma 13 makes `U♯` and `U♭` bounded complete.
-/

namespace ScottDomains.Lemma28AtU

open ScottDomains ScottDomains.BifiniteUniversal ScottDomains.PRep

/-- **`→` is p-representable over the paper's `U`**, with no hypothesis. -/
theorem repArrowAtU : IsPRepresentable₂ Dyadic.U funOp := by
  haveI : Domain (ScottHom Dyadic.U Dyadic.U) := inferInstance
  haveI : BoundedComplete (ScottHom Dyadic.U Dyadic.U) := inferInstance
  obtain ⟨_fn, _gr, hfg, hgf⟩ := PRepSum.pairAtU (ScottHom Dyadic.U Dyadic.U)
  exact PRepFun.rep_arrow hfg hgf

/-- **`⇸` is p-representable over the paper's `U`**, with no hypothesis. The
strict function space is a domain by `PRepFun.strictHomDomain`, which r0037 had
to prove — it existed nowhere before. -/
theorem repStrictArrowAtU : IsPRepresentable₂ Dyadic.U strictFunOp := by
  haveI : Domain (StrictHom Dyadic.U Dyadic.U) := PRepFun.strictHomDomain
  haveI : BoundedComplete (StrictHom Dyadic.U Dyadic.U) := lem10_strict
  obtain ⟨_fn, _gr, hfg, hgf⟩ := PRepSum.pairAtU (StrictHom Dyadic.U Dyadic.U)
  exact PRepFun.rep_strictArrow hfg hgf

/-- **`⊗` is p-representable over the paper's `U`**, with no hypothesis.

This is the conjunct r0034 refuted, and the refutation was of the *closure*
reading only: it turns on `r ⊥` sitting strictly above `⊥`, which a projection
forbids. -/
theorem repSmashAtU : IsPRepresentable₂ Dyadic.U smashOp := by
  haveI : Domain (Smash Dyadic.U Dyadic.U) := PRepFun.smashDomain
  haveI : BoundedComplete (Smash Dyadic.U Dyadic.U) := lem10_smash
  obtain ⟨_fn, _gr, hfg, hgf⟩ := PRepSum.pairAtU (Smash Dyadic.U Dyadic.U)
  exact PRepFun.rep_smash hfg hgf

/-- **Lemma 28 at `U` from the two conjuncts still open.** The arity is the
measurement: 9 for `PRep.lemma28_of`, 5 for `PRepSum.lemma28AtU_of`, 2 here. -/
theorem lemma28AtU_of' (h_smyth : IsPRepresentable Dyadic.U smythOp)
    (h_hoare : IsPRepresentable Dyadic.U hoareOp) :
    PRep.Lemma28AtU :=
  PRepSum.lemma28AtU_of repArrowAtU repStrictArrowAtU repSmashAtU h_smyth h_hoare

end ScottDomains.Lemma28AtU
