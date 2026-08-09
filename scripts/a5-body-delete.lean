/-!
Instrument 2 of the r0044 Class-2 sweep: **hypothesis deletion**, run as agent1
ran it — restate the theorem with the flagged binder removed and reprove it. If
the kernel accepts, the binder is removable in fact, not only by a linter's fvar
test.

Scope note, and it matters. Deletion answers a *different* question from
`unusedArguments`:

* `unusedArguments` finds hypotheses the **current proof term does not mention**.
  Removability then follows without a rebuild — the same term typechecks with the
  binder gone — so these probes are confirmations, not discoveries.
* Deletion plus a **new** proof finds hypotheses that are used yet unnecessary.
  agent1's `Kleene.sSup_recoverAt` is that case: `[BoundedComplete β]` is
  genuinely consumed, and a different argument does without it. Nothing here
  measures that class in general; only reproving each declaration does.

So: every probe below is a class-2a confirmation. The class-2b population in this
area is unmeasured, and the report says so.
-/

-- The same `open`s the source files carry, so the probes can be textual copies
-- of the original proofs with one binder removed and nothing else changed.
open ScottDomains ScottDomains.PRep ScottDomains.PRepFun
open ScottDomains.BifiniteUniversal ScottDomains.ScottHom

namespace A5Probe

/-- `PRep.hoareOp_eq` without `[Domain D.carrier]`. The proof is `rfl` either way.
This one is more than bookkeeping: `PRep.lean:110-124` argues at length that
`(·)♭` is definable at a bare cpo and that `[Domain D]` is *not* where the work
goes — and then states the agreement lemma under a `[Domain D.carrier]` it never
uses, which is weaker than what the file itself proves. -/
theorem hoareOp_eq (D : Cpo.{u}) :
    (PRep.hoareOp D).carrier = Hoare.Powerdomain D.carrier := rfl

/-- `PRepFun.domain_range_smashFamily` without `[Domain U]`. The proof takes its
`Domain`s from the finitary-projection images `FpImage c.1`, `FpImage c.2` via
`(mem_Fp.mp _).domain`, never from `U`. -/
theorem domain_range_smashFamily {U : Type u} [CompletePartialOrder U]
    (c : ↥(Fp U) × ↥(Fp U)) :
    @Domain _ (IsProjection.rangeCompletePartialOrder
      (PRepFun.isProjection_smashFamily c)) := by
  haveI : Domain (FpImage c.1).carrier := (mem_Fp.mp c.1.2).domain
  haveI : Domain (FpImage c.2).carrier := (mem_Fp.mp c.2.2).domain
  haveI : Domain (PRep.smashOp (FpImage c.1) (FpImage c.2)).carrier :=
    PRepFun.smashDomain
  letI : CompletePartialOrder ↥(Set.range ⇑(PRepFun.smashFamily c)) :=
    IsProjection.rangeCompletePartialOrder (PRepFun.isProjection_smashFamily c)
  exact domain_orderIso (PRepFun.smashRangeOrderIso c).symm

/-- `PRepFun.domain_range_strictArrowFamily` without `[Domain U]`;
`[BoundedComplete U]` is kept because `boundedComplete_range` does consume it. -/
theorem domain_range_strictArrowFamily {U : Type u} [CompletePartialOrder U]
    [BoundedComplete U] (c : ↥(Fp U) × ↥(Fp U)) :
    @Domain _ (IsProjection.rangeCompletePartialOrder
      (PRepFun.isProjection_strictArrowFamily c)) := by
  haveI : Domain (FpImage c.1).carrier := (mem_Fp.mp c.1.2).domain
  haveI : Domain (FpImage c.2).carrier := (mem_Fp.mp c.2.2).domain
  haveI : BoundedComplete (FpImage c.2).carrier :=
    boundedComplete_range (mem_Fp.mp c.2.2).isProjection
  haveI : Domain (PRep.strictFunOp (FpImage c.1) (FpImage c.2)).carrier :=
    PRepFun.strictHomDomain
  letI : CompletePartialOrder ↥(Set.range ⇑(PRepFun.strictArrowFamily c)) :=
    IsProjection.rangeCompletePartialOrder (PRepFun.isProjection_strictArrowFamily c)
  exact domain_orderIso (PRepFun.strictEvidentOrderIso c).symm

/-- `ClosureProperties.isBifinite_idealCompletion` without `[Countable P]`. The
paper's Theorem 11 does require a countable pre-order for the ideal completion to
be a *domain*; this statement concludes only `IsBifinite`, for which countability
is not spent anywhere in the argument. -/
theorem isBifinite_idealCompletion {P : Type u} [Preorder P] [OrderBot P]
    (h : ∀ v : Set P, v.Finite →
      ∃ M : Set P, M.Finite ∧ ClosureProperties.SelectsGreatest M ∧ v ⊆ M) :
    IsBifinite (IdealCompletion P) := by
  intro u hu husub
  have hrep : ∀ I ∈ u, ∃ w : P, I = IdealCompletion.principal w := fun I hI =>
    IdealCompletion.isCompactElement_iff_exists_eq_principal.mp (husub hI)
  choose! rep hrep using hrep
  obtain ⟨M, hMfin, hMsel, hMsub⟩ := h (rep '' u) (hu.image _)
  refine ⟨IdealCompletion.principal '' M, hMfin.image _,
    ClosureProperties.isNormalIn_image_principal hMsel, ?_⟩
  intro I hI
  exact ⟨rep I, hMsub ⟨I, hI, rfl⟩, (hrep I hI).symm⟩

end A5Probe

#print axioms A5Probe.hoareOp_eq
#print axioms A5Probe.domain_range_smashFamily
#print axioms A5Probe.domain_range_strictArrowFamily
#print axioms A5Probe.isBifinite_idealCompletion
