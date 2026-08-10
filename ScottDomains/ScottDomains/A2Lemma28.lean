import ScottDomains.PowerdomainMapRep
import ScottDomains.Flat

/-!
# r0045, agent2: what `PRep.Lemma28` and `PRep.Lemma28AtU` still owe

Round r0044 listed `ScottDomains.PRep.Lemma28` and `ScottDomains.PRep.Lemma28AtU`
among 19 `Prop`-valued `def`s that no theorem proves with zero hypotheses. This
module measures the two rows. It proves three things, none of which changes any
existing statement.

## 1. `PRep.Lemma28` is a schema, and its universal reading is false

`Lemma28` takes the carrier as a parameter:

    def Lemma28 (U : Type u) [CompletePartialOrder U] : Prop := …

so "discharge `Lemma28`" — a theorem whose conclusion is `Lemma28 ?U` with no
hypotheses — reads as `∀ U [CompletePartialOrder U], Lemma28 U`. **That
proposition is false**, and `not_forall_lemma28` below is the kernel-checked
refutation. The counterexample is `Flat Empty`, the one-point cpo: `Fp` of a
subsingleton contains the identity, its image has one element, and conjunct 7's
`(im p)⊥` has two, so no order isomorphism exists.

The refutation survives every structural hypothesis the development can add:
`Flat Empty` is a bounded complete domain, so `not_forall_lemma28_bcd` refutes
the universal reading even under `[Domain U]` and `[BoundedComplete U]`. What
Lemma 28 actually needs of `U` is **universality** — Theorem 27's retraction
pair for every bounded complete domain — which `Flat Empty` does not have and no
class in `Domain.lean` states.

So the `PRep.Lemma28` row can never be closed as an unconditional theorem. The
paper's claim is its instance at §7.3's carrier, which is the separate row
`PRep.Lemma28AtU`. This is a defect in the row, not in the definition: the count
of undischarged claims should carry `Lemma28` as a schema, not as an open
theorem. Section 4 isolates the one hypothesis separating the two rows and shows
the counterexample fails at exactly that hypothesis.

## 2. The residue of `Lemma28AtU` is exactly two conjuncts

`lemma_28_atU_iff` proves

    Lemma28AtU ↔ IsPRepresentable U (·)♯ ∧ IsPRepresentable U (·)♭

so `Lemma28AtU.lemma_28_atU_of'`'s two hypotheses are not merely sufficient, they
are **necessary**: seven of the nine conjuncts hold outright and the remaining
two are the whole of what is left. The reduction from arity 9 to arity 2 is
therefore tight — no further reduction of that shape exists.

## 3. What `lemma_28_atU_of''` did, measured

`PowerdomainMapRep.lemma_28_atU_of''` has arity 4 where `lemma_28_atU_of'` has 2, and
its proof *calls* `lemma_28_atU_of'`. So the four hypotheses **imply** the two
(`residue_of_powerdomainMap_obligations` records this as a theorem), while the
two are equivalent to the goal by `lemma_28_atU_iff`. Composing:

    SmythImageIso ∧ SmythFamilyLUB ∧ HoareImageIso ∧ HoareFamilyLUB
      → IsPRepresentable U (·)♯ ∧ IsPRepresentable U (·)♭
      ↔ Lemma28AtU

Read as logic alone, the arity-4 form assumes strictly more: it names one
particular representing family, `p ↦ p♯` and `p ↦ p♭`, where `IsPRepresentable`
quantifies existentially over all of them. So arity 4 versus arity 2 is not a
comparison of the same propositions and the count is not the measurement here.

**Settled in r0045, and in favour of the restructure.** `ScottDomains.R45.Agent4`
discharged all four obligations outright, so the family it named was the right
one and the decomposition was correct. The four were not "still open hypotheses"
in any adverse sense — they were the right four to isolate, and isolating them is
what made them provable. `lemma_28_atU_of''` is therefore a correct decomposition,
not a lateral move, and `PRep.Lemma28AtU` — Lemma 28 of §7.3 over the paper's own
`U` — is kernel-verified. This module no longer carries any open work on it;
`lemma_28_atU_iff` remains as the measurement that the residue was tight.
-/

namespace ScottDomains.R45.Agent2

open ScottDomains ScottDomains.BifiniteUniversal

universe u

/-! ## A one-point cpo is a finitary-projection domain with a one-point `Fp` image

Everything in this section is about a `Subsingleton` cpo, where every statement
about the order is `Subsingleton.elim`. The point of writing it out is that
`Fp α` must be shown **nonempty** before the counterexample can be instantiated,
and `IsFinitaryProjection` carries a `Domain` on the image, which is not free. -/

section Subsingleton

variable {α : Type u} [CompletePartialOrder α] [Subsingleton α]

/-- Every element of a subsingleton order is compact: the witness demanded by
`IsCompactElement` is any member of the nonempty set. -/
theorem isCompactElement_of_subsingleton (k : α) : IsCompactElement k := by
  intro s _ hne _ _ _
  obtain ⟨z, hz⟩ := hne
  exact ⟨z, hz, le_of_eq (Subsingleton.elim k z)⟩

/-- **A subsingleton cpo is a domain.** Not an `instance` — it would fire on every
`Domain` goal and is only ever wanted at the image of a projection on a
subsingleton, where it is supplied explicitly. -/
theorem domain_of_subsingleton : Domain α := by
  refine { toIsAlgebraic := ⟨?_, ?_⟩, countable_compacts := ?_ }
  · intro _ a ha b _
    exact ⟨a, ha, le_rfl, le_of_eq (Subsingleton.elim b a)⟩
  · intro x
    exact ⟨fun _ hk => hk.2, fun u _ => le_of_eq (Subsingleton.elim x u)⟩
  · exact Set.Subsingleton.countable fun a _ b _ => Subsingleton.elim a b

/-- Every continuous self-map of a subsingleton cpo is a projection: both laws
are `Subsingleton.elim`. -/
theorem isProjection_of_subsingleton (p : ScottHom α α) : ScottHom.IsProjection p :=
  ⟨fun _ => Subsingleton.elim _ _, fun _ => le_of_eq (Subsingleton.elim _ _)⟩

/-- **`Fp α` is everything, for a subsingleton `α`.** The `Domain` on `im(p)` —
the conjunct `Fp` adds and `Fc` does not — is `domain_of_subsingleton` at the
subtype, whose cpo structure is `IsProjection.rangeCompletePartialOrder`. -/
theorem isFinitaryProjection_of_subsingleton (p : ScottHom α α) :
    ScottHom.IsFinitaryProjection p :=
  ⟨isProjection_of_subsingleton p,
    @domain_of_subsingleton _
      (ScottHom.IsProjection.rangeCompletePartialOrder (isProjection_of_subsingleton p))
      ⟨fun _ _ => Subtype.ext (Subsingleton.elim _ _)⟩⟩

end Subsingleton

/-! ## The p-representability square cannot commute at a one-point cpo -/

/-- **A commuting square needs the two sides to have the same cardinality.** If
every pair of points of `A` is equal and `B` has two distinct points, no `≃o`
exists. Stated at `Cpo` so the instances are the `Cpo.str` ones that
`IsPRepresentable` uses, rather than instances rediscovered by search. -/
theorem not_nonempty_orderIso_of_subsingleton {A B : Cpo.{u}}
    (hA : ∀ a b : A.carrier, a = b) {b₁ b₂ : B.carrier} (hb : b₁ ≠ b₂) :
    ¬ Nonempty (A.carrier ≃o B.carrier) := by
  rintro ⟨e⟩
  refine hb ?_
  rw [← e.apply_symm_apply b₁, ← e.apply_symm_apply b₂, hA (e.symm b₁) (e.symm b₂)]

/-- **Conjunct 7 of Lemma 28 fails over a one-point cpo.** Take `p = id`, which
is a finitary projection by `isFinitaryProjection_of_subsingleton`. Then
`im(R p)` is a subtype of a subsingleton and so has one point, while
`(·)⊥` applied to `im p` is `WithBot` of a nonempty type and so has at least
two — `⊥` and the image of `p ⊥`. -/
theorem not_isPRepresentable_liftOp {α : Type u} [CompletePartialOrder α] [Subsingleton α] :
    ¬ IsPRepresentable α PRep.liftOp := by
  rintro ⟨R, -, hiso⟩
  refine not_nonempty_orderIso_of_subsingleton
    (A := FpImage (R ⟨ScottHom.id, isFinitaryProjection_of_subsingleton _⟩))
    (B := PRep.liftOp (FpImage (⟨ScottHom.id, isFinitaryProjection_of_subsingleton _⟩ : ↥(Fp α))))
    (fun a b => Subtype.ext (Subsingleton.elim _ _))
    (b₁ := (⊥ : WithBot ↥(Set.range ⇑(ScottHom.id : ScottHom α α))))
    (b₂ := ((⟨(ScottHom.id : ScottHom α α) ⊥, Set.mem_range_self ⊥⟩ :
        ↥(Set.range ⇑(ScottHom.id : ScottHom α α))) :
      WithBot ↥(Set.range ⇑(ScottHom.id : ScottHom α α))))
    (fun h => WithBot.bot_ne_coe h)
    (hiso _)

/-- **Lemma 28 fails over a one-point cpo**, through conjunct 7. -/
theorem not_lemma28_of_subsingleton {α : Type u} [CompletePartialOrder α] [Subsingleton α] :
    ¬ PRep.Lemma28 α :=
  fun h => not_isPRepresentable_liftOp h.2.2.2.2.2.2.1

/-! ## The concrete counterexample: `Flat Empty` -/

theorem subsingleton_flatEmpty : Subsingleton (Flat Empty) :=
  ⟨fun a b => by
    cases a with
    | bot =>
      cases b with
      | bot => rfl
      | up x => exact x.elim
    | up x => exact x.elim⟩

/-- `Flat Empty` is a bounded complete domain — so the counterexample is not a
degenerate object outside the development's own classes. -/
theorem domain_flatEmpty : Domain (Flat Empty) := inferInstance

theorem boundedComplete_flatEmpty : BoundedComplete (Flat Empty) := inferInstance

theorem not_lemma28_flatEmpty : ¬ PRep.Lemma28 (Flat Empty) := by
  haveI := subsingleton_flatEmpty
  exact not_lemma28_of_subsingleton

/-- **The universal reading of `PRep.Lemma28` is false.** A theorem discharging
the `Lemma28` row in agent6's sense would have this type. -/
theorem not_forall_lemma28 :
    ¬ ∀ (U : Type) (inst : CompletePartialOrder U), @PRep.Lemma28 U inst :=
  fun h => not_lemma28_flatEmpty (h (Flat Empty) inferInstance)

/-- **…and it stays false after adding every structural class the development
has.** `Flat Empty` is an algebraic, countably based, bounded complete cpo. The
hypothesis Lemma 28 really needs is universality of `U`, which is a property of
§7.3's carrier and not a typeclass. -/
theorem not_forall_lemma28_bcd :
    ¬ ∀ (U : Type) (inst : CompletePartialOrder U),
        @Domain U inst → @BoundedComplete U inst → @PRep.Lemma28 U inst :=
  fun h =>
    not_lemma28_flatEmpty
      (h (Flat Empty) inferInstance domain_flatEmpty boundedComplete_flatEmpty)

/-! ## `Lemma28AtU`: the residue is exactly two conjuncts -/

/-- **The arity-2 reduction is tight.** Seven of the nine conjuncts hold over
`Dyadic.U` with no hypothesis, so `Lemma28AtU` is *equivalent* to the remaining
two — `Lemma28AtU.lemma_28_atU_of'`'s hypotheses are necessary as well as
sufficient. The forward direction is projection out of the nine-fold
conjunction; the backward direction is `lemma_28_atU_of'` itself. -/
theorem lemma_28_atU_iff :
    PRep.Lemma28AtU ↔
      IsPRepresentable Dyadic.U PRep.smythOp ∧ IsPRepresentable Dyadic.U PRep.hoareOp :=
  ⟨fun h => ⟨h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2⟩,
    fun h => Lemma28AtU.lemma_28_atU_of' h.1 h.2⟩

/-- **The four `PowerdomainMap.Rep` obligations imply the two-conjunct residue.**
Recorded as a theorem so the dependency of this stream on that cluster is
kernel-checked rather than asserted in prose. With `lemma_28_atU_iff` this says the
arity-4 hypothesis set is *sufficient* for `Lemma28AtU`; nothing here says it is
necessary, and it is not implied by `Lemma28AtU`, because it names a particular
representing family while `IsPRepresentable` quantifies existentially over
all of them. -/
theorem residue_of_powerdomainMap_obligations
    (hisoSmyth : PowerdomainMap.Rep.SmythImageIso Dyadic.U)
    (hlubSmyth : PowerdomainMap.Rep.SmythFamilyLUB Dyadic.U)
    (hisoHoare : PowerdomainMap.Rep.HoareImageIso Dyadic.U)
    (hlubHoare : PowerdomainMap.Rep.HoareFamilyLUB Dyadic.U) :
    IsPRepresentable Dyadic.U PRep.smythOp ∧ IsPRepresentable Dyadic.U PRep.hoareOp :=
  ⟨PowerdomainMap.Rep.repSmythAtU hisoSmyth hlubSmyth,
    PowerdomainMap.Rep.repHoareAtU hisoHoare hlubHoare⟩

/-! ## What `pairAtU` supplies, isolated

`PRep.Lemma28`'s own `def` line carries exactly one binder,
`[CompletePartialOrder U]`. `not_forall_lemma28` above shows the claim is false
at those binders, and `not_forall_lemma28_bcd` shows it is still false after
adding `[Domain U]` and `[BoundedComplete U]`. So no amount of instance-binder
strengthening from `Domain.lean`'s classes closes this row — the missing content
is not a class.

It is this proposition, and nothing else. -/

/-- **`U` is universal for bounded complete domains**: every bounded complete
domain is a projection-retract of `U`, in `PRep`'s coordinates —
`fn ∘ gr = id` and `gr ∘ fn ⊑ id`.

This is the exact content `PRepSum.pairAtU` supplies at `Dyadic.U` and a generic
`U` does not. `pairAtU` gets it from `Atomless.theorem_27`, Theorem 27 at the atomless
dyadic-interval domain. It is a **hypothesis**, not an instance binder: no class
in `Domain.lean` states it, and `not_universalForBCD_of_subsingleton` below shows
it is a genuine restriction. -/
def UniversalForBCD (U : Type) [CompletePartialOrder U] : Prop :=
  ∀ (V : Type) [CompletePartialOrder V] [Domain V] [BoundedComplete V],
    ∃ (fn : ScottHom U V) (gr : ScottHom V U),
      (∀ y, fn (gr y) = y) ∧ ∀ x, gr (fn x) ≤ x

/-- `PRepSum.pairAtU` *is* universality of `Dyadic.U`, transposed. Recorded so
the hypothesis below is known non-vacuous. -/
theorem universalForBCD_dyadicU : UniversalForBCD Dyadic.U :=
  fun V => PRepSum.pairAtU V

/-- **Universality fails at the counterexample, and that is the only thing that
fails.** A three-element bounded complete domain (`Flat Bool`) cannot be a
retract of a one-point cpo, because `fn ∘ gr = id` makes `gr` injective. -/
theorem not_universalForBCD_of_subsingleton {U : Type} [CompletePartialOrder U]
    [Subsingleton U] : ¬ UniversalForBCD U := by
  intro h
  obtain ⟨fn, gr, hfg, -⟩ := h (Flat Bool)
  have hbot : (Flat.up true : Flat Bool) = ⊥ := by
    rw [← hfg (Flat.up true), ← hfg ⊥, Subsingleton.elim (gr (Flat.up true)) (gr ⊥)]
  exact Flat.up_ne_bot hbot

theorem not_universalForBCD_flatEmpty : ¬ UniversalForBCD (Flat Empty) := by
  haveI := subsingleton_flatEmpty
  exact not_universalForBCD_of_subsingleton

/-- **Lemma 28 at a generic carrier, from universality.**

Every one of the nine conjuncts reaches `Dyadic.U` the same way: the operator's
*result* is shown to be a bounded complete domain (Theorem 7 for `→`, Lemma 10
for `⇸ ⊗ × + ⊕ (·)⊥`, Theorem 11 with Lemma 13 for `(·)♯ (·)♭`), and then the
retraction pair is read off Theorem 27. Replacing that last step by the
hypothesis `huniv` generalises all nine at once — the seven conjuncts
`PRepFun`/`PRepSum` prove and the two `PowerdomainMap.Rep` reduces are all
already stated over an abstract `U`, so no conjunct proof needed rewriting.

**This is a reduction, not a discharge.** `PRep.Lemma28`'s own binder list is
`[CompletePartialOrder U]`; this theorem adds two instance binders
(`[Domain U]`, `[BoundedComplete U]`) *and* an ordinary hypothesis
(`UniversalForBCD U`). By `not_forall_lemma28_bcd` the two instance binders
cannot close the row on their own, and by `not_universalForBCD_of_subsingleton`
the hypothesis is exactly what the counterexample lacks. The four
`PowerdomainMap.Rep` hypotheses are agent4's cluster and drop out when its
generic discharges are merged, leaving one hypothesis and two added binders. -/
theorem lemma_28_of_universal (U : Type) [CompletePartialOrder U] [Domain U] [BoundedComplete U]
    (hisoSmyth : PowerdomainMap.Rep.SmythImageIso U)
    (hlubSmyth : PowerdomainMap.Rep.SmythFamilyLUB U)
    (hisoHoare : PowerdomainMap.Rep.HoareImageIso U)
    (hlubHoare : PowerdomainMap.Rep.HoareFamilyLUB U)
    (huniv : UniversalForBCD U) :
    PRep.Lemma28 U := by
  refine PRep.lemma_28_of ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · obtain ⟨_fn, _gr, hfg, hgf⟩ := huniv (ScottHom U U)
    exact PRepFun.rep_arrow hfg hgf
  · haveI : Domain (StrictHom U U) := PRepFun.strictHomDomain
    haveI : BoundedComplete (StrictHom U U) := lemma_10_strict
    obtain ⟨_fn, _gr, hfg, hgf⟩ := huniv (StrictHom U U)
    exact PRepFun.rep_strictArrow hfg hgf
  · haveI : Domain (U × U) := PowerdomainRep.domain_prod
    haveI : BoundedComplete (U × U) := lemma_10_prod
    obtain ⟨_fn, _gr, hfg, hgf⟩ := huniv (U × U)
    exact PRep.rep_prod hfg hgf
  · haveI : Domain (Smash U U) := PRepFun.smashDomain
    haveI : BoundedComplete (Smash U U) := lemma_10_smash
    obtain ⟨_fn, _gr, hfg, hgf⟩ := huniv (Smash U U)
    exact PRepFun.rep_smash hfg hgf
  · haveI : Domain (ClosureProperties.SeparatedSum U U) := PRepSum.domain_coalescedSum
    haveI : BoundedComplete (ClosureProperties.SeparatedSum U U) :=
      ClosureProperties.lemma_10_separated
    obtain ⟨_fn, _gr, hfg, hgf⟩ := huniv (ClosureProperties.SeparatedSum U U)
    exact PRepSum.rep_sepSum hfg hgf
  · haveI : Domain (CoalescedSum U U) := PRepSum.domain_coalescedSum
    haveI : BoundedComplete (CoalescedSum U U) := lemma_10_sum
    obtain ⟨_fn, _gr, hfg, hgf⟩ := huniv (CoalescedSum U U)
    exact PRepSum.rep_coalSum hfg hgf
  · haveI : BoundedComplete (WithBot U) := lemma_10_lift
    obtain ⟨_fn, _gr, hfg, hgf⟩ := huniv (WithBot U)
    exact PRep.rep_lift hfg hgf
  · haveI : Domain (Smyth.Powerdomain U) := Smyth.instDomain
    haveI : BoundedComplete (Smyth.Powerdomain U) := PowerdomainBC.instBoundedCompleteSmyth U
    obtain ⟨_fn, _gr, hfg, hgf⟩ := huniv (Smyth.Powerdomain U)
    exact PowerdomainMap.Rep.rep_smyth_of hisoSmyth hlubSmyth hfg hgf
  · haveI : Domain (IdealCompletion (Hoare.Pf ↥(compacts U))) := IdealCompletion.instDomain
    haveI : BoundedComplete (IdealCompletion (Hoare.Pf ↥(compacts U))) :=
      PowerdomainBC.instBoundedCompleteHoare U
    obtain ⟨_fn, _gr, hfg, hgf⟩ := huniv (IdealCompletion (Hoare.Pf ↥(compacts U)))
    exact PowerdomainMap.Rep.rep_hoare_of hisoHoare hlubHoare hfg hgf

/-- **The generic theorem specialises back to the paper's carrier.** A
consistency check on `lemma_28_of_universal`: at `Dyadic.U` the universality
hypothesis is `universalForBCD_dyadicU`, so this has exactly the four hypotheses
of `PowerdomainMapRep.lemma_28_atU_of''` and re-derives it by the generic route
instead of the `U`-specific one. Nothing in the seven non-powerdomain conjuncts
needed `Dyadic.U` beyond the retraction pair. -/
theorem lemma_28_atU_of_universal
    (hisoSmyth : PowerdomainMap.Rep.SmythImageIso Dyadic.U)
    (hlubSmyth : PowerdomainMap.Rep.SmythFamilyLUB Dyadic.U)
    (hisoHoare : PowerdomainMap.Rep.HoareImageIso Dyadic.U)
    (hlubHoare : PowerdomainMap.Rep.HoareFamilyLUB Dyadic.U) :
    PRep.Lemma28AtU :=
  lemma_28_of_universal Dyadic.U hisoSmyth hlubSmyth hisoHoare hlubHoare universalForBCD_dyadicU

end ScottDomains.R45.Agent2
