import ScottDomains.Bifinite
import ScottDomains.Skeleton.Lemma17
import ScottDomains.Powerdomain.Hoare
import ScottDomains.Powerdomain.Smyth
import ScottDomains.Powerdomain.Plotkin

/-!
# Lemma 17, the three powerdomain conjuncts `D♮`, `D♯`, `D♭`

Gunter & Scott, *Semantic Domains*, §6.2, quoted from the source PDF:

> **Lemma 17** If `D` and `E` are bifinite domains, then so are the cpo's
> `D → E`, `D →⊥ E`, `D × E`, `D ⊗ E`, `D + E`, `D ⊕ E`, `D⊥`, `D♮`, `D♯` and
> `D♭`.
>
> **Proof:** … To see that `D♮` is bifinite, one shows that the set
> `M = {p♮ | p ∈ Fp(D) and im(p) is finite}` is directed and has the identity as
> its least upper bound. The functions in `M` are themselves finitary projections
> with finite images so `D♮` is bifinite.

The paper's argument is carried out here on the **basis** rather than on the
function space, because `IsBifinite` is defined as the Plotkin condition on
`K(D)` (`Bifinite.lean`). The translation is exact and it makes the three
conjuncts one argument instead of three:

* Theorem 11 gives `K(D♮) = {↓u | u ∈ Pf(K(D))}` — the principal ideals — with
  `↓u ⊑ ↓v` iff `u ⊑ v` in the pre-order. So a normal subposet of `K(D♮)` is the
  image under `principal` of a set of finite sets of compacts, and the condition
  to check is about the pre-order, not about ideals: `isNormalIn_image_principal`
  says a set `M` that has a **greatest** member below every `w` is normal.
* `p_N`, the finitary projection attached to a finite normal `N ◁ K(D)`, is on
  the basis the map sending a compact `y` to the greatest member of `N ∩ ↓y`
  (`normalGreatest`). The paper's `p♮` is its image map `w ↦ p_N[w]`.
* For **each** of the three pre-orders `⊑♭`, `⊑♯` and `⊑♮`, `p_N[w]` is the
  greatest member of `{m ∈ Pf(N) | m ⊑ w}`. That is the whole content of the
  three conjuncts, and the three proofs are five lines each; only the direction
  in which the witnesses are chased differs.

The uniformity is worth stating precisely, because it is not obvious from the
definitions: the *Hoare* candidate `{n ∈ N | ∃ y ∈ w, n ⊑ y}` — the largest
subset of `N` that is `⊑♭`-below `w` — is **not** greatest for `⊑♮`, since its
Smyth conjunct can fail. `p_N[w]` is greatest for all three.

No countability of `K(D)` and no bounded completeness is used. `[Domain D]`
enters only through `Countable` on the pre-order, which Theorem 11 consumes to
make the powerdomain a domain at all.
-/

namespace ScottDomains.ClosureProperties

open ScottDomains

universe u

/-! ### Bifiniteness of an ideal completion

Stated for an arbitrary pre-order with a least element, so the three powerdomains
share it. -/

section IdealCompletionBifinite

variable {P : Type u} [Preorder P] [OrderBot P]

/-- `M` **selects greatest approximants**: below every `w` the members of `M`
have a greatest one. This is the pre-order form of "`M` is a normal subposet with
a projection onto it" — a normal subposet is one whose members below any point
are *directed*, and a greatest member is the finite case of that. -/
def SelectsGreatest (M : Set P) : Prop :=
  ∀ w : P, ∃ m ∈ M, m ≤ w ∧ ∀ m' ∈ M, m' ≤ w → m' ≤ m

/-- **The image of a greatest-approximant-selecting set is a normal subposet of
`K(IdealCompletion P)`.** The compacts of an ideal completion are the principal
ideals (Theorem 11), and `principal` is monotone and order-reflecting, so the
whole statement transports to the pre-order, where the greatest member supplies
nonemptiness and directedness at once. -/
theorem isNormalIn_image_principal {M : Set P} (hM : SelectsGreatest M) :
    (IdealCompletion.principal '' M) ◁ compacts (IdealCompletion P) := by
  constructor
  · rintro _ ⟨m, _, rfl⟩
    exact IdealCompletion.isCompactElement_principal m
  · intro I hI
    obtain ⟨w, rfl⟩ := IdealCompletion.isCompactElement_iff_exists_eq_principal.mp hI
    obtain ⟨m, hm, hmw, hgreat⟩ := hM w
    refine ⟨⟨IdealCompletion.principal m, ⟨m, hm, rfl⟩,
      Set.mem_Iic.mpr (IdealCompletion.principal_mono hmw)⟩, ?_⟩
    rintro _ ⟨⟨m₁, hm₁, rfl⟩, h₁⟩ _ ⟨⟨m₂, hm₂, rfl⟩, h₂⟩
    have hle₁ : m₁ ≤ w := IdealCompletion.mem_principal.mp (IdealCompletion.principal_le_iff.mp h₁)
    have hle₂ : m₂ ≤ w := IdealCompletion.mem_principal.mp (IdealCompletion.principal_le_iff.mp h₂)
    exact ⟨IdealCompletion.principal m, ⟨⟨m, hm, rfl⟩,
        Set.mem_Iic.mpr (IdealCompletion.principal_mono hmw)⟩,
      IdealCompletion.principal_mono (hgreat m₁ hm₁ hle₁),
      IdealCompletion.principal_mono (hgreat m₂ hm₂ hle₂)⟩

/-- **A sufficient condition for the ideal completion to be bifinite:** every
finite subset of the pre-order sits inside a finite set that selects greatest
approximants. Each compact of `IdealCompletion P` is `↓w` for some `w`
(Theorem 11), so a finite set of compacts is the image of a finite set of `w`'s,
and the hypothesis applied to that set produces the required normal subposet. -/
theorem isBifinite_idealCompletion [Countable P]
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

end IdealCompletionBifinite

/-! ### `p_N` on the basis: the greatest member of `N ∩ ↓y` -/

section NormalGreatest

variable {D : Type u} [CompletePartialOrder D] {N : Set D}

/-- **A finite normal subposet has a greatest member below every compact.**
`N ∩ ↓y` is nonempty and directed because `N ◁ K(D)` and `y` is compact, and it
is finite because `N` is; a finite nonempty directed set has a greatest member
(`exists_greatest_of_finite_directedOn`, r0027). This is `p_N y` — Theorem 6's
finitary projection, read on the basis. -/
theorem exists_greatest_mem_normal (hN : N ◁ compacts D) (hfin : N.Finite)
    (y : ↥(compacts D)) :
    ∃ m : ↥(compacts D), (m : D) ∈ N ∧ m ≤ y ∧
      ∀ x : ↥(compacts D), (x : D) ∈ N → x ≤ y → x ≤ m := by
  obtain ⟨c, hc, hmax⟩ :=
    exists_greatest_of_finite_directedOn (hfin.subset Set.inter_subset_left)
      (hN.nonempty y.2) (hN.directedOn y.2)
  exact ⟨⟨c, hN.subset hc.1⟩, hc.1, hc.2, fun x hx hxy => hmax x.val ⟨hx, hxy⟩⟩

/-- `p_N y`, the greatest member of `N` below the compact `y`. -/
noncomputable def normalGreatest (hN : N ◁ compacts D) (hfin : N.Finite)
    (y : ↥(compacts D)) : ↥(compacts D) :=
  (exists_greatest_mem_normal hN hfin y).choose

theorem normalGreatest_mem (hN : N ◁ compacts D) (hfin : N.Finite) (y : ↥(compacts D)) :
    ((normalGreatest hN hfin y : ↥(compacts D)) : D) ∈ N :=
  (exists_greatest_mem_normal hN hfin y).choose_spec.1

theorem normalGreatest_le (hN : N ◁ compacts D) (hfin : N.Finite) (y : ↥(compacts D)) :
    normalGreatest hN hfin y ≤ y :=
  (exists_greatest_mem_normal hN hfin y).choose_spec.2.1

theorem le_normalGreatest (hN : N ◁ compacts D) (hfin : N.Finite) {x y : ↥(compacts D)}
    (hx : (x : D) ∈ N) (hxy : x ≤ y) : x ≤ normalGreatest hN hfin y :=
  (exists_greatest_mem_normal hN hfin y).choose_spec.2.2 x hx hxy

/-- The compacts of `D` that lie in `N`, as a set of the subtype. Finite when `N`
is, because the coercion is injective. -/
theorem finite_preimage_val (hfin : N.Finite) :
    (Subtype.val ⁻¹' N : Set ↥(compacts D)).Finite :=
  hfin.preimage Subtype.val_injective.injOn

end NormalGreatest

/-! ### `D♭`, the Hoare (lower) powerdomain -/

section Hoare

open ScottDomains.Hoare

variable {D : Type u} [CompletePartialOrder D] {N : Set D}

/-- `Pf(N) ⊆ Pf(K(D))`, the finite nonempty sets of compacts drawn from `N`. -/
def hoareBasisOf (N : Set D) : Set (Hoare.Pf ↥(compacts D)) :=
  {w | ∀ x ∈ w, (x : D) ∈ N}

theorem finite_hoareBasisOf (hfin : N.Finite) : (hoareBasisOf N).Finite := by
  have hsub : hoareBasisOf N ⊆
      (fun w : Hoare.Pf ↥(compacts D) => ((w.toFinset : Finset ↥(compacts D)) : Set _)) ⁻¹'
        {t | t ⊆ (Subtype.val ⁻¹' N : Set ↥(compacts D))} := by
    intro w hw x hx
    exact hw x (Hoare.Pf.mem_def.mpr (Finset.mem_coe.mp hx))
  refine Set.Finite.subset (Set.Finite.preimage ?_ (finite_preimage_val hfin).finite_subsets) hsub
  exact (fun w _ v _ h => Hoare.Pf.ext (Finset.coe_injective h))

/-- **`p_N[w]` is the greatest member of `Pf(N)` that is `⊑♭`-below `w`.**
`⊑♭` asks that every member of the smaller set be below *some* member of the
larger. `p_N[w] ⊑♭ w` because `p_N y ⊑ y`; and if `m ⊑♭ w` with `m ⊆ N`, each
`x ∈ m` has some `y ∈ w` with `x ⊑ y`, and then `x ⊑ p_N y ∈ p_N[w]` because
`p_N y` is greatest in `N ∩ ↓y`. -/
theorem selectsGreatest_hoareBasisOf (hN : N ◁ compacts D) (hfin : N.Finite) :
    SelectsGreatest (hoareBasisOf N) := by
  classical
  intro w
  refine ⟨Hoare.Pf.ofFinset (w.toFinset.image (normalGreatest hN hfin))
      (w.toFinset_nonempty.image _), ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp (Hoare.Pf.mem_def.mp hx)
    exact normalGreatest_mem hN hfin y
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp (Hoare.Pf.mem_def.mp hx)
    exact ⟨y, hy, normalGreatest_le hN hfin y⟩
  · intro m hm hmw x hx
    obtain ⟨y, hy, hxy⟩ := hmw x hx
    exact ⟨normalGreatest hN hfin y,
      Hoare.Pf.mem_def.mpr (Finset.mem_image.mpr ⟨y, hy, rfl⟩),
      le_normalGreatest hN hfin (hm x hx) hxy⟩

/-- **Lemma 17, the `D♭` conjunct.** `D♭` is the ideal completion of
`⟨Pf(K(D)), ⊑♭⟩`, so `isBifinite_idealCompletion` reduces the claim to producing,
for each finite set of finite sets of compacts, a finite superset that selects
greatest approximants. Collect every compact mentioned, expand that finite set to
a finite normal `N ◁ K(D)` — this is the one use of `IsBifinite D` — and take
`Pf(N)`. -/
theorem lem17_hoare [Domain D] (h : IsBifinite D) : IsBifinite (Hoare.Powerdomain D) := by
  refine isBifinite_idealCompletion fun v hv => ?_
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

end Hoare

/-! ### `D♯`, the Smyth (upper) powerdomain -/

section Smyth

variable {D : Type u} [CompletePartialOrder D] {N : Set D}

/-- `Pf(N)`, at the Smyth carrier. -/
def smythBasisOf (N : Set D) : Set (Smyth.Basis D) :=
  {w | ∀ x ∈ w.toFinset, (x : D) ∈ N}

theorem finite_smythBasisOf (hfin : N.Finite) : (smythBasisOf N).Finite := by
  have hsub : smythBasisOf N ⊆
      (fun w : Smyth.Basis D => ((w.toFinset : Finset ↥(compacts D)) : Set _)) ⁻¹'
        {t | t ⊆ (Subtype.val ⁻¹' N : Set ↥(compacts D))} := by
    intro w hw x hx
    exact hw x (Finset.mem_coe.mp hx)
  refine Set.Finite.subset (Set.Finite.preimage ?_ (finite_preimage_val hfin).finite_subsets) hsub
  exact (fun w _ v _ h => Smyth.Basis.ext (Finset.coe_injective h))

/-- **`p_N[w]` is the greatest member of `Pf(N)` that is `⊑♯`-below `w`.**
`⊑♯` asks that every member of the *larger* set be above some member of the
smaller, so both directions run the opposite way from the Hoare case: `p_N y` is
the witness under `y ∈ w`, and if `m ⊑♯ w` then the witness `a ⊑ y` it supplies
satisfies `a ⊑ p_N y` because `a ∈ N`. -/
theorem selectsGreatest_smythBasisOf (hN : N ◁ compacts D) (hfin : N.Finite) :
    SelectsGreatest (smythBasisOf N) := by
  classical
  intro w
  refine ⟨⟨w.toFinset.image (normalGreatest hN hfin), w.nonempty'.image _⟩, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hx
    exact normalGreatest_mem hN hfin y
  · intro y hy
    exact ⟨normalGreatest hN hfin y, Finset.mem_image.mpr ⟨y, hy, rfl⟩,
      normalGreatest_le hN hfin y⟩
  · intro m hm hmw x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨a, ha, hay⟩ := hmw y hy
    exact ⟨a, ha, le_normalGreatest hN hfin (hm a ha) hay⟩

/-- **Lemma 17, the `D♯` conjunct.** The same reduction as `lem17_hoare`, at the
upper pre-order. -/
theorem lem17_smyth [Domain D] (h : IsBifinite D) : IsBifinite (Smyth.Powerdomain D) := by
  refine isBifinite_idealCompletion fun v hv => ?_
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

end Smyth

/-! ### `D♮`, the Plotkin (convex) powerdomain -/

section Plotkin

variable {D : Type u} [CompletePartialOrder D] {N : Set D}

/-- `Pf(N)`, at the Egli–Milner carrier. -/
def plotkinBasisOf (N : Set D) : Set (Plotkin.FinCompacts D) :=
  {w | ∀ x ∈ w, (x : D) ∈ N}

theorem finite_plotkinBasisOf (hfin : N.Finite) : (plotkinBasisOf N).Finite := by
  have hsub : plotkinBasisOf N ⊆
      (fun w : Plotkin.FinCompacts D => w.carrier) ⁻¹'
        {t | t ⊆ (Subtype.val ⁻¹' N : Set ↥(compacts D))} := fun w hw x hx => hw x hx
  refine Set.Finite.subset (Set.Finite.preimage ?_ (finite_preimage_val hfin).finite_subsets) hsub
  intro w _ v _ h
  exact Plotkin.FinCompacts.ext fun a => by
    simp only [← Plotkin.FinCompacts.mem_carrier, show w.carrier = v.carrier from h]

/-- **`p_N[w]` is the greatest member of `Pf(N)` that is `⊑♮`-below `w`.**
Egli–Milner is the conjunction of the two previous orderings, and `p_N[w]` is
greatest for both conjuncts at once — which the *Hoare-maximal* candidate
`{n ∈ N | ∃ y ∈ w, n ⊑ y}` is not: for two members `x, z ∈ N ∩ ↓y` the Smyth
conjunct would need `x ⊑ z`, and normality gives only that both lie under
`p_N y`. Choosing the image under `p_N` is exactly what repairs that. -/
theorem selectsGreatest_plotkinBasisOf (hN : N ◁ compacts D) (hfin : N.Finite) :
    SelectsGreatest (plotkinBasisOf N) := by
  intro w
  refine ⟨⟨normalGreatest hN hfin '' w.carrier,
    w.finite.image _, w.nonempty.image _⟩, ?_, ⟨?_, ?_⟩, ?_⟩
  · rintro _ ⟨y, -, rfl⟩
    exact normalGreatest_mem hN hfin y
  · rintro _ ⟨y, hy, rfl⟩
    exact ⟨y, hy, normalGreatest_le hN hfin y⟩
  · intro y hy
    exact ⟨normalGreatest hN hfin y, ⟨y, hy, rfl⟩, normalGreatest_le hN hfin y⟩
  · intro m hm hmw
    refine ⟨fun x hx => ?_, ?_⟩
    · obtain ⟨y, hy, hxy⟩ := hmw.1 x hx
      exact ⟨normalGreatest hN hfin y, ⟨y, hy, rfl⟩, le_normalGreatest hN hfin (hm x hx) hxy⟩
    · rintro _ ⟨y, hy, rfl⟩
      obtain ⟨a, ha, hay⟩ := hmw.2 y hy
      exact ⟨a, ha, le_normalGreatest hN hfin (hm a ha) hay⟩

/-- **Lemma 17, the `D♮` conjunct** — the case the paper writes out, here on the
basis: `p♮` is `w ↦ p_N[w]`, and `Pf(N)` is its (finite) image. -/
theorem lem17_plotkin [Domain D] (h : IsBifinite D) : IsBifinite (Plotkin.Powerdomain D) := by
  refine isBifinite_idealCompletion fun v hv => ?_
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

end Plotkin

end ScottDomains.ClosureProperties
