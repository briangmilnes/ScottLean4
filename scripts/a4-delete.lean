/-
a4-delete.lean — r0044 Class 2 instrument, part D: a **deletion experiment** for
the used-but-unnecessary class of hypotheses.

`#lint only unusedArguments` reports a binder absent from the statement *and*
from the proof term.  It cannot see a binder that the proof genuinely consumes
yet a different proof would do without (agent1's `Kleene.sSup_recoverAt` is the
exemplar).  Deciding one of those needs an actual reproof, which is what this
file does — outside the package, so no `.lean` file of the development is edited
and the round's frozen counts are untouched.

The chain tested here, found by `scripts/a4-hyps.lean`'s DELETABLE-FROM-STATEMENT
report plus the `#lint` list:

* `ClosureProperties.isBifinite_idealCompletion` carries `[Countable P]`, which
  `#lint` reports **unused** — class 1, a decided defect.
* `ClosureProperties.lem17_hoare`, `lem17_smyth`, `lem17_plotkin` each carry
  `[Domain D]`, which `#lint` does **not** report, because each proof does
  consume it: it is what synthesizes `Countable (Hoare.Pf ↥(compacts D))` and its
  two siblings, so that `isBifinite_idealCompletion` can be applied at all.

So `[Domain D]` on the three Lemma 17 conjuncts is consumed only to feed a
hypothesis that is itself unused.  If that is right, deleting `[Countable P]`
from the general lemma lets all three drop `[Domain D]`.  The four `theorem`s
below are that claim, at the weakened signatures, with the development's own
proof scripts.  Kernel acceptance is the verdict.

Run with `scripts/a4-run-delete.sh`.
-/
open ScottDomains ScottDomains.ClosureProperties

namespace A4Delete

universe u

/-- `isBifinite_idealCompletion` **without** `[Countable P]`: the development's
own proof script, verbatim. -/
theorem isBifinite_idealCompletion' {P : Type u} [Preorder P] [OrderBot P]
    (h : ∀ v : Set P, v.Finite → ∃ M : Set P, M.Finite ∧ SelectsGreatest M ∧ v ⊆ M) :
    IsBifinite (IdealCompletion P) := by
  intro u hu husub
  have hrep : ∀ I ∈ u, ∃ w : P, I = IdealCompletion.principal w := fun I hI =>
    IdealCompletion.isCompactElement_iff_exists_eq_principal.mp (husub hI)
  choose! rep hrep using hrep
  obtain ⟨M, hMfin, hMsel, hMsub⟩ := h (rep '' u) (hu.image _)
  refine ⟨IdealCompletion.principal '' M, hMfin.image _, isNormalIn_image_principal hMsel, ?_⟩
  intro I hI
  exact ⟨rep I, hMsub ⟨I, hI, rfl⟩, (hrep I hI).symm⟩

/-- Lemma 17's `D♭` conjunct **without** `[Domain D]`. -/
theorem lem17_hoare' {D : Type u} [CompletePartialOrder D] (h : IsBifinite D) :
    IsBifinite (Hoare.Powerdomain D) := by
  refine isBifinite_idealCompletion' fun v hv => ?_
  have hmention : (Subtype.val ''
      (⋃ w ∈ v, (↑w.toFinset : Set ↥(compacts D))) : Set D).Finite :=
    (hv.biUnion fun w _ => w.toFinset.finite_toSet).image _
  have hsub : Subtype.val '' (⋃ w ∈ v, (↑w.toFinset : Set ↥(compacts D)))
      ⊆ compacts D := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  obtain ⟨N, hNfin, hN, hNsub⟩ := h _ hmention hsub
  refine ⟨hoareBasisOf N, finite_hoareBasisOf hNfin, selectsGreatest_hoareBasisOf hN hNfin, ?_⟩
  intro w hw x hx
  exact hNsub ⟨x, Set.mem_biUnion hw (Hoare.Pf.mem_def.mp hx), rfl⟩

/-- Lemma 17's `D♯` conjunct **without** `[Domain D]`. -/
theorem lem17_smyth' {D : Type u} [CompletePartialOrder D] (h : IsBifinite D) :
    IsBifinite (Smyth.Powerdomain D) := by
  refine isBifinite_idealCompletion' fun v hv => ?_
  have hmention : (Subtype.val ''
      (⋃ w ∈ v, (↑w.toFinset : Set ↥(compacts D))) : Set D).Finite :=
    (hv.biUnion fun w _ => w.toFinset.finite_toSet).image _
  have hsub : Subtype.val '' (⋃ w ∈ v, (↑w.toFinset : Set ↥(compacts D)))
      ⊆ compacts D := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  obtain ⟨N, hNfin, hN, hNsub⟩ := h _ hmention hsub
  refine ⟨smythBasisOf N, finite_smythBasisOf hNfin, selectsGreatest_smythBasisOf hN hNfin, ?_⟩
  intro w hw x hx
  exact hNsub ⟨x, Set.mem_biUnion hw hx, rfl⟩

/-- Lemma 17's `D♮` conjunct **without** `[Domain D]`. -/
theorem lem17_plotkin' {D : Type u} [CompletePartialOrder D] (h : IsBifinite D) :
    IsBifinite (Plotkin.Powerdomain D) := by
  refine isBifinite_idealCompletion' fun v hv => ?_
  have hmention : (Subtype.val '' (⋃ w ∈ v, (w.carrier : Set ↥(compacts D))) : Set D).Finite :=
    (hv.biUnion fun w _ => w.finite).image _
  have hsub : Subtype.val '' (⋃ w ∈ v, (w.carrier : Set ↥(compacts D))) ⊆ compacts D := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  obtain ⟨N, hNfin, hN, hNsub⟩ := h _ hmention hsub
  refine ⟨plotkinBasisOf N, finite_plotkinBasisOf hNfin,
    selectsGreatest_plotkinBasisOf hN hNfin, ?_⟩
  intro w hw x hx
  exact hNsub ⟨x, Set.mem_biUnion hw hx, rfl⟩

end A4Delete
