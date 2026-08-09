/-!
Verification of the r0044 Class-2 hits: the elaborated type of every flagged
declaration and of every provider that is supposed to discharge its hypothesis,
read from the built `.olean` rather than off a source line, plus the axiom
footprint of each.

The load-bearing check is the last block: each `example` re-derives the flagged
theorem's conclusion **without** the hypothesis the detector called free, by
handing it the provider. If the `example` is accepted, the hypothesis is free in
fact and not only by the detector's unification test.
-/

open ScottDomains

section Elaborated

-- Instrument 1 (`unusedArguments`) — the six hits in agent5's area.
#check @ScottDomains.ClosureProperties.isBifinite_idealCompletion
#check @ScottDomains.Dyadic.thm27
#check @ScottDomains.PRep.hoareOp_eq
#check @ScottDomains.PRepFun.domain_range_strictArrowFamily
#check @ScottDomains.PRepFun.domain_range_smashFamily
#check @ScottDomains.Section62.HasGreatestStableNormal

-- Instrument 4 (free hypothesis) — the flagged theorems.
#check @ScottDomains.Dyadic.thm27
#check @ScottDomains.PRepSum.lemma28AtU_of
#check @ScottDomains.PropertyM.thm18_of_cor136
#check @ScottDomains.Thm18.thm18_of_thm137Chains_and_cor136
#check @ScottDomains.Thm18.thm18_of_thm137_and_cor136
#check @ScottDomains.Thm18.thm18_viaProjections_of_thm137_and_cor136
#check @ScottDomains.JungFinite.lemma22
#check @ScottDomains.JungFinite.thm18_of_propertyM
#check @ScottDomains.ClosureProperties.lemma17
#check @ScottDomains.ClosureProperties.lem17_strictFun
#check @ScottDomains.ClosureProperties.exists_finite_projection_fixing
#check @ScottDomains.lem17_fun

-- ... and the providers that are supposed to discharge those hypotheses.
#check @ScottDomains.Atomless.isNormallyRepresented
#check @ScottDomains.Lemma28AtU.repArrowAtU
#check @ScottDomains.Lemma28AtU.repStrictArrowAtU
#check @ScottDomains.Lemma28AtU.repSmashAtU
#check @ScottDomains.JungCor136.fixedPointOfCompactDeflationIsCompact
#check @ScottDomains.prop15

-- The unconditional forms the development already carries, for comparison.
#check @ScottDomains.Atomless.thm27
#check @ScottDomains.thm18

#print axioms ScottDomains.thm18
#print axioms ScottDomains.PropertyM.thm18_of_cor136
#print axioms ScottDomains.JungCor136.fixedPointOfCompactDeflationIsCompact
#print axioms ScottDomains.Atomless.thm27
#print axioms ScottDomains.prop15

end Elaborated

section Free

/-- `Dyadic.thm27`'s `h` is free: `Atomless.isNormallyRepresented` supplies it at
`↥(compacts D)`, whose `Atomless.CountableBC` instance is derived from
`[Domain D] [BoundedComplete D]` — the instances `thm27` already carries. -/
example (D : Type) [CompletePartialOrder D] [Domain D] [BoundedComplete D] :
    ∃ (e : ScottHom D Dyadic.U) (p : ScottHom Dyadic.U D),
      ScottHom.IsEmbeddingProjectionPair e p :=
  Dyadic.thm27 D (Atomless.isNormallyRepresented _)

/-- `PropertyM.thm18_of_cor136`'s `hcor` is free under the instances it already
carries: `JungCor136.fixedPointOfCompactDeflationIsCompact` needs only
`IsAlgebraic (ScottHom D D)`, which `Domain (ScottHom D D)` supplies. -/
example (D : Type) [CompletePartialOrder D] [Domain D] [Domain (ScottHom D D)] :
    IsBifinite D :=
  PropertyM.thm18_of_cor136 JungCor136.fixedPointOfCompactDeflationIsCompact

/-- The same for the three `Thm18` staging theorems: `hcor` costs nothing, so
each is `Thm137`-conditional only. -/
example (D : Type) [CompletePartialOrder D] [Domain D] [Domain (ScottHom D D)]
    (h137 : JungNets.Thm137Chains D) : IsBifinite D :=
  Thm18.thm18_of_thm137Chains_and_cor136 h137
    JungCor136.fixedPointOfCompactDeflationIsCompact

/-- …and in fact `h137` is not needed either, which is what `ScottDomains.thm18`
records: the whole of `thm18_of_thm137Chains_and_cor136` is subsumed. -/
example (D : Type) [CompletePartialOrder D] [Domain D] [Domain (ScottHom D D)] :
    IsBifinite D :=
  ScottDomains.thm18

/-- `PRepSum.lemma28AtU_of` takes **five** hypotheses, not the three the detector
flagged. Three — `→`, `⇸`, `⊗` — are proved outright in `Lemma28AtU` and are
therefore free; the remaining two, the Smyth `♯` and Hoare `♭` conjuncts, are
open, which is what keeps the theorem conditional and honest. -/
example (hSmyth : BifiniteUniversal.IsPRepresentable Dyadic.U PRep.smythOp)
    (hHoare : BifiniteUniversal.IsPRepresentable Dyadic.U PRep.hoareOp) :
    PRep.Lemma28AtU :=
  PRepSum.lemma28AtU_of Lemma28AtU.repArrowAtU Lemma28AtU.repStrictArrowAtU
    Lemma28AtU.repSmashAtU hSmyth hHoare

/-- Lemma 17's **second** bifiniteness hypothesis is free: the codomain carries
`[Domain β] [BoundedComplete β]`, and `prop15` — Proposition 15, every bounded
complete domain is bifinite — supplies `IsBifinite β` from exactly those. The
first hypothesis is not free: `α` carries no `BoundedComplete`. -/
example {α β : Type} [CompletePartialOrder α] [CompletePartialOrder β]
    [Domain α] [Domain β] [BoundedComplete β] (h₁ : IsBifinite α) :
    IsBifinite (ScottHom α β) :=
  lem17_fun h₁ prop15

example {α β : Type} [CompletePartialOrder α] [CompletePartialOrder β]
    [Domain α] [Domain β] [BoundedComplete β] (h₁ : IsBifinite α) :
    IsBifinite (StrictHom α β) :=
  ClosureProperties.lem17_strictFun h₁ prop15

end Free
