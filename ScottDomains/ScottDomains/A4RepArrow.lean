import ScottDomains.A4FunctionSpaceBifinite
import ScottDomains.Lemma30

/-!
# Where the `[BoundedComplete]` obstruction on Lemma 30's conjuncts 1–2 actually is

r0047's plan states that `Lemma30AtV`'s conjuncts 1–2 reduce to removing
`[BoundedComplete β]` from `ClosureProperties.lemma_17_fun`. **Measured against the
tree, that reduction is incomplete.** There are *two* independent
`[BoundedComplete V]` obligations on conjunct 1, and Lemma 17 supplies only one
of them:

| # | obligation | where | removed by |
| - | ---------- | ----- | ---------- |
| 1 | `Retracts (ScottHom V V)` | `Lemma30.retracts_fun_of_boundedComplete` | `A4Lemma17Fun.lemma_17_fun` + `A4FunctionSpaceBifinite.domain_scottHom` |
| 2 | `IsPRepresentable₂ V funOp` from that pair | `PRepFun.rep_arrow`'s `[BoundedComplete U]` | **not removed** — see below |

Obligation 2 is not Lemma 17's. `PRepFun.lean:269` records it exactly: the
`[BoundedComplete U]` of `rep_arrow` is spent in one place,
`PRepFun.domain_range_compHom`, which needs `Domain (im p → im q)` for the two
finitary projections indexing the conjugating family, and reaches it through
`PRep.boundedComplete_range`.

`domain_range_compHom_of_bifinite` below replaces that route with
`A4FunctionSpaceBifinite.domain_scottHom`, and `rep_arrow_of_fpImagesBifinite`
carries the replacement through the whole conjunct. What is left is exactly one
proposition:

> `FpImagesBifinite U` — every finitary-projection image of `U` is bifinite.

That is Plotkin's closure of the bifinite domains under projections. It is a true
theorem of domain theory and it is **not in this development**: measured over
every module, no declaration concludes `IsBifinite` of a projection image.

So the correct statement of the residue is: conjuncts 1 and 2 of `Lemma30AtV`
follow from `Theorem29SecondAtDomains` **and** `FpImagesBifinite V`, and the second
is a new open item that r0047's plan did not name.

## Why the route had to be replaced rather than repaired

r0047's agent5 proved `not_thm29SecondAtDomains_and_boundedComplete_V`: the
hypothesis set `{Theorem29SecondAtDomains, BoundedComplete V}` is **contradictory**.
`Lemma30.retracts_fun_of_boundedComplete` and
`retracts_strictFun_of_boundedComplete` take `[BoundedComplete V]` on top of the
already-refuted `Colimit.Theorem29Second`, so the repair r0045 applied to `⊗`, `+`
and `⊕` — swapping the refuted claim for the live one — cannot work here: it
would land on exactly that contradictory pair.

`retracts_fun_V` and `retracts_strictFun_V` below are the replacement. They take
`Theorem29SecondAtDomains` and **carry no bounded-completeness binder at all**, so
whether `V` is bounded complete no longer bears on conjuncts 1–2 in either
direction. That is the sense in which the `[BoundedComplete β]` obstruction on
these two conjuncts is discharged rather than relocated.

Every theorem here is stated with `FpImagesBifinite` as an explicit hypothesis
and **no `[BoundedComplete]` binder anywhere**.
-/

namespace ScottDomains.R47.Agent4

open ScottDomains ScottHom BifiniteUniversal

universe u

/-- **Every finitary-projection image of `U` is bifinite.** The single residual
hypothesis of conjuncts 1 and 2 below. `Fp U` is the finitary projections —
projections whose image is a domain (`ScottHom.IsFinitaryProjection`) — and
`FpImage p` is that image with its inherited cpo structure. -/
def FpImagesBifinite (U : Type u) [CompletePartialOrder U] : Prop :=
  ∀ p : ↥(Fp U), IsBifinite (FpImage p).carrier

section Arrow

variable {U : Type u} [CompletePartialOrder U]

/-- **`PRepFun.domain_range_compHom` with `[BoundedComplete U]` traded for
bifiniteness of the two images.** The script is that theorem's verbatim except
for one line: where it writes `haveI : BoundedComplete ↥(range q) :=
boundedComplete_range hq` and appeals to `FunctionSpaceCountable`'s instance,
this writes `domain_scottHom hbp hbq`. -/
theorem domain_range_compHom_of_bifinite {p q : ScottHom U U}
    (hp : IsProjection p) (hq : IsProjection q)
    (hdp : @Domain _ (IsProjection.rangeCompletePartialOrder hp))
    (hdq : @Domain _ (IsProjection.rangeCompletePartialOrder hq))
    (hbp : @IsBifinite _ (IsProjection.rangeCompletePartialOrder hp))
    (hbq : @IsBifinite _ (IsProjection.rangeCompletePartialOrder hq)) :
    @Domain _ (IsProjection.rangeCompletePartialOrder (isProjection_compHom hp hq)) := by
  letI : CompletePartialOrder ↥(Set.range ⇑p) := IsProjection.rangeCompletePartialOrder hp
  letI : CompletePartialOrder ↥(Set.range ⇑q) := IsProjection.rangeCompletePartialOrder hq
  haveI : Domain ↥(Set.range ⇑p) := hdp
  haveI : Domain ↥(Set.range ⇑q) := hdq
  haveI : Domain (ScottHom ↥(Set.range ⇑p) ↥(Set.range ⇑q)) := domain_scottHom hbp hbq
  letI : CompletePartialOrder ↥(Set.range ⇑(compHom p q)) :=
    IsProjection.rangeCompletePartialOrder (isProjection_compHom hp hq)
  exact PRep.domain_orderIso (PRepFun.evidentOrderIsoP hp hq).symm

/-- **`PRepFun.rep_arrow` with `[BoundedComplete U]` replaced by
`FpImagesBifinite U`.** The term is `rep_arrow`'s verbatim with
`domain_range_compHom_of_bifinite` substituted for `domain_range_compHom`; every
other ingredient (`isPRepresentable₂_of_repFamily`, `isFinitaryProjection_repOf`,
`arrowFamily_mono`, `isLUB_arrowFamily`, `evidentOrderIsoP`) needs only
`[Domain U]`. -/
theorem rep_arrow_of_fpImagesBifinite [Domain U] (hb : FpImagesBifinite U)
    {fn : ScottHom U (ScottHom U U)} {gr : ScottHom (ScottHom U U) U}
    (hfg : ∀ y, fn (gr y) = y) (hgf : ∀ x, gr (fn x) ≤ x) :
    IsPRepresentable₂ U PRep.funOp :=
  PRep.isPRepresentable₂_of_repFamily hfg
    (fun q => PRep.isFinitaryProjection_repOf hfg hgf (PRepFun.isProjection_arrowFamily q)
      (domain_range_compHom_of_bifinite _ _ (mem_Fp.mp q.1.2).domain (mem_Fp.mp q.2.2).domain
        (hb q.1) (hb q.2)))
    PRepFun.arrowFamily_mono PRepFun.isLUB_arrowFamily
    fun q => ⟨PRepFun.evidentOrderIsoP (mem_Fp.mp q.1.2).isProjection
      (mem_Fp.mp q.2.2).isProjection⟩

/-- **`PRepFun.domain_range_strictArrowFamily` with the same trade**, through
`domain_strictHom` instead of `strictHomDomain`. -/
theorem domain_range_strictArrowFamily_of_bifinite [Domain U] (hb : FpImagesBifinite U)
    (c : ↥(Fp U) × ↥(Fp U)) :
    @Domain _ (IsProjection.rangeCompletePartialOrder
      (PRepFun.isProjection_strictArrowFamily c)) := by
  haveI : Domain (FpImage c.1).carrier := (mem_Fp.mp c.1.2).domain
  haveI : Domain (FpImage c.2).carrier := (mem_Fp.mp c.2.2).domain
  haveI : Domain (PRep.strictFunOp (FpImage c.1) (FpImage c.2)).carrier :=
    domain_strictHom (hb c.1) (hb c.2)
  letI : CompletePartialOrder ↥(Set.range ⇑(PRepFun.strictArrowFamily c)) :=
    IsProjection.rangeCompletePartialOrder (PRepFun.isProjection_strictArrowFamily c)
  exact PRep.domain_orderIso (PRepFun.strictEvidentOrderIso c).symm

/-- **`PRepFun.rep_strictArrow` with `[BoundedComplete U]` replaced by
`FpImagesBifinite U`.** -/
theorem rep_strictArrow_of_fpImagesBifinite [Domain U] (hb : FpImagesBifinite U)
    {fn : ScottHom U (StrictHom U U)} {gr : ScottHom (StrictHom U U) U}
    (hfg : ∀ y, fn (gr y) = y) (hgf : ∀ x, gr (fn x) ≤ x) :
    IsPRepresentable₂ U PRep.strictFunOp :=
  PRep.isPRepresentable₂_of_repFamily hfg
    (fun c => PRep.isFinitaryProjection_repOf hfg hgf (PRepFun.isProjection_strictArrowFamily c)
      (domain_range_strictArrowFamily_of_bifinite hb c))
    PRepFun.strictArrowFamily_mono PRepFun.isLUB_strictArrowFamily
    fun c => ⟨PRepFun.strictEvidentOrderIso c⟩

end Arrow

/-! ### At `V`: the retraction pairs, now with no bounded-completeness binder -/

open Colimit Lemma30 in
/-- **`V` retracts onto `V → V`, from Theorem 29's second sentence at the
paper's own hypothesis.** Compare `Lemma30.retracts_fun_of_boundedComplete`,
which carries `[BoundedComplete V]` — refuted by
`R45.Agent3.not_boundedComplete_V` — and takes the stronger `Colimit.Theorem29Second`
— refuted by `R45.Agent3.not_thm29Second`. This version has neither: the
`[Domain (ScottHom V V)]` that `retracts_of_isDomain` needs is
`domain_scottHom`, and the `IsBifinite` is `lemma_17_fun`. -/
theorem retracts_fun_V (h : Theorem29SecondAtDomains) : Retracts (ScottHom V V) := by
  haveI : Domain (ScottHom V V) := domain_scottHom isBifinite_V isBifinite_V
  exact retracts_of_isDomain h _ (lemma_17_fun isBifinite_V isBifinite_V)

open Colimit Lemma30 in
/-- **`V` retracts onto `V ⇸ V`.** Compare
`Lemma30.retracts_strictFun_of_boundedComplete`. -/
theorem retracts_strictFun_V (h : Theorem29SecondAtDomains) : Retracts (StrictHom V V) := by
  haveI : Domain (StrictHom V V) := domain_strictHom isBifinite_V isBifinite_V
  exact retracts_of_isDomain h _ (lemma_17_strictFun isBifinite_V isBifinite_V)

open Colimit Lemma30 in
/-- **Conjunct 1 of Lemma 30: `→` is p-representable over `V`**, from Theorem
29's second sentence and `FpImagesBifinite V`. No instance binder is added: the
`[Domain V]` is `Colimit.domain_V`, found by resolution. -/
theorem rep_fun_V (h : Theorem29SecondAtDomains) (hb : FpImagesBifinite V) :
    IsPRepresentable₂ V PRep.funOp := by
  obtain ⟨gr, fn, hfg, hgf⟩ := retracts_fun_V h
  exact rep_arrow_of_fpImagesBifinite hb hfg hgf

open Colimit Lemma30 in
/-- **Conjunct 2 of Lemma 30: `⇸` is p-representable over `V`**, from the same
two hypotheses. -/
theorem rep_strictFun_V (h : Theorem29SecondAtDomains) (hb : FpImagesBifinite V) :
    IsPRepresentable₂ V PRep.strictFunOp := by
  obtain ⟨gr, fn, hfg, hgf⟩ := retracts_strictFun_V h
  exact rep_strictArrow_of_fpImagesBifinite hb hfg hgf

end ScottDomains.R47.Agent4
