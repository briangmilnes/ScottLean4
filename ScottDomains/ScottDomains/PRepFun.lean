import ScottDomains.PRep

/-!
# Lemma 28's function-space conjuncts, at the projection notion

Gunter & Scott, *Semantic Domains*, §7.3. Read from the rendered source page
(physical page 42 of `papers/Gunter Scott 1990.pdf`, printed folio 41), because
the file's Type 3 bitmap fonts carry no usable `ToUnicode` map and `pdftotext`
substitutes or drops every operator glyph in the statement:

> **Lemma 28** *The following operators are representable over* `U`:
> `→`, `⇸`, `×`, `⊗`, `+`, `⊕`, `(·)⊥`, `(·)♯`, `(·)♭`.

Nine operators; the second is drawn `∘→`, the strict continuous function space of
§4.2. This confirms `PRep.Lemma28`'s list exactly — no correction is needed to it
this round, and the r0037 stream plan's three-conjunct assignment (`→`, `⇸`, `⊗`
as conjuncts 1, 2 and 4) matches the source's order.

Two further sentences on the same page fix hypotheses that the conjuncts below
carry, and are worth quoting because they are the reason the hypotheses are the
paper's rather than an artifact of the formalization:

> **Theorem 27** *For any bounded complete domain* `D`, *there is a projection*
> `p : U → D`.

so §7.3's `U` is universal for **bounded complete** domains, and bounded
completeness of the carrier is part of the setting rather than an extra
assumption; and

> The proof that `→` is representable over `U` is almost identical to the proof
> we gave above that it is representable over `PN`.

which is the paper's own statement that `rep_arrow` below should be Lemma 23's
proof with the notion changed — and is what this file measures.

## What this file proves

| # | Conjunct | Statement | Status |
| - | -------- | --------- | ------ |
| 1 | `→` | `IsPRepresentable₂ U funOp` | **proved** — `rep_arrow`, under `[Domain U] [BoundedComplete U]` and the paper's pair |
| 2 | `⇸` | `IsPRepresentable₂ U strictFunOp` | **proved** — `rep_strictArrow`, same hypotheses |
| 4 | `⊗` | `IsPRepresentable₂ U smashOp` | **proved** — `rep_smash`, under `[Domain U]` alone |

Nothing is stubbed with `sorry`, and no conjunct carries a hypothesis beyond
`[Domain U]`, `[BoundedComplete U]` and the paper's own retraction pair.

Two closure properties the development did not have are proved here, because
`Fp`'s second conjunct needs them at the images and nothing else supplied them:
`strictHomDomain : Domain (D →⊥ E)` and `smashDomain : Domain (D ⊗ E)`. Both are
new; the second rests on `smashIsAlgebraic`, and no round before this one had
proved the smash product algebraic.

## The one obligation that is not Lemma 23's

`PRep.lean`'s module docstring records that `Fp` adds a second component to every
conjunct: for each index `q`, `im(R q)` must be a **domain**, where the closure
notion asked only for two equations. `PRep.isFinitaryProjection_repOf` reduces
that to a `Domain` on `im(C q)`, and `PRep.domain_orderIso` transports it along
any `≃o`. So the arrow conjunct's new content is exactly

    Domain (im(p) → im(q))

for `p`, `q` finitary projections of `U`. `FunctionSpaceCountable.lean` supplies
`Domain (ScottHom α β)` under `[Domain α] [Domain β] [BoundedComplete β]`. The
first two are what `IsFinitaryProjection` hands over. The third is
`PRep.boundedComplete_range`, which needs `[BoundedComplete U]` — and Theorem 27
above says that is the hypothesis §7.3's `U` was built to satisfy.

That is the whole delta at `→`. Measured against `Combinator.rep_arrow`:

| # | Ingredient | Closure notion (r0034) | Here |
| - | ---------- | ---------------------- | ---- |
| 1 | conjugating family `(s, r)` | `compHom`, `CombinatorRep.arrowFamily` | reused unchanged |
| 2 | monotonicity in `(r, s)` | `compHom_mono` | reused unchanged |
| 3 | the two equations | `isClosure_compHom` | `isProjection_compHom` (`Skeleton/Lemma17.lean`) — already existed |
| 4 | `im((s,r)) ≅ im(r) → im(s)` | `evidentOrderIso` | **re-proved** as `evidentOrderIsoP`; the two continuity lemmas it rests on reverse |
| 5 | `im(R(s,r))` a domain | not required | **new** — `domain_range_compHom` |
| 6 | the index least upper bound | `isLUB_val_image_of_isLUB` | `PRep.isLUB_val_image_of_isLUB_fp'`, which costs `isFinitaryProjection_sSup` |
| 7 | the pair hypothesis | `Retracts U (U → U)`, i.e. `id ⊑ gr ∘ fn` | **incompatible** — `gr ∘ fn ⊑ id`; `PRep.gr_fn_eq_of_both` forces `U ≅ (U → U)` if both hold |

Rows 1–3 transfer verbatim, row 4 is re-proved, rows 5 and 6 are new, and row 7
is a different hypothesis. The paper's "almost identical" is accurate about the
*construction* and inaccurate about the *obligations*: five of the seven rows
change.

## What `⊗` cost, and what it did not

The r0037 plan's claim that `⊗` is "no longer refuted" is **confirmed by the
kernel**. r0034 refuted `⊗` at the closure notion with a three-chain
counterexample, and the counterexample turns on `r ⊥` being allowed to sit
strictly above `⊥`. `isProjection_smashMap` below is where the difference is
spent: a projection has `r ⊥ = ⊥`, the collapse to the adjoined bottom is
therefore idempotent, and the conjunct goes through. The change of notion was the
whole obstruction.

What `⊗` did cost is two constructions the development did not have:

1. **`r ⊗ s` did not exist.** `grep` over every module finds no functorial action
   on the smash — `Isomorphism/Smash.lean` supplies only `smashComm` and
   `smashAssoc`. `smashMap` below is it, built as `π ∘ (r × s) ∘ ι` for a
   Scott-continuous pair `ι : D ⊗ E → D × E`, `π : D × E → D ⊗ E`, so that
   continuity is a composite rather than a case analysis over `Smash`'s branching
   `sSup`.
2. **`Domain (D ⊗ E)` did not exist.** `ClosureProperties.lean` states Lemma 10
   (`lem10_smash : BoundedComplete (Smash α β)`) and Lemma 17
   (`lem17_smash : IsBifinite (Smash α β)`), and the `IsAlgebraic` instances in
   the development are `Set X`, `ScottHom α β`, `α × β`, `WithBot α` and
   `IdealCompletion A` — the smash is not among them. `smashIsAlgebraic` and
   `smashDomain` close that.

`⇸` hit the same kind of gap and a cheaper one: `Domain (D →⊥ E)` was also
absent, but it follows in twenty lines from `Domain (D → E)` because the strict
functions are a **downward-closed** sub-cpo — anything below a strict function is
strict — so the compacts of the subtype are literally the compacts of `D → E`
lying below, with no strictification needed. The smash has no such embedding into
a space already known to be algebraic, which is why its algebraicity is a
hundred-line proof and the strict function space's is a twenty-line one.

## Lifting these three conjuncts to §7.3's `U`

Theorem 27 supplies the retraction pair for an operator whose *result* is a
bounded complete domain, so each conjunct lifts from the abstract `U` to
`Dyadic.U` exactly when Lemma 10 and a `Domain` cover its result type. All three
are covered: `→` by `ScottHom`'s `BoundedComplete` instance and
`FunctionSpaceCountable.lean`'s `Domain`; `⇸` by `lem10_strict` and
`strictHomDomain`; `⊗` by `lem10_smash` and `smashDomain`. The two `Domain`
halves are new in this file, so before it no conjunct here could have lifted.
-/

namespace ScottDomains.PRepFun

open ScottDomains ScottDomains.PRep ScottDomains.BifiniteUniversal ScottHom PowerdomainRep

universe u

/-! ## The image of a projection as a sub-cpo of `D`

`evidentOrderIsoP` restricts a map `G : D → D` to `im(p) → im(q)` and extends it
back, and both directions need the inclusion and the corestriction to be Scott
continuous. `UniversalDomain.lean` proves these for a closure; here they are the
projection counterparts, and both get *cheaper*:

* the inclusion is `IsProjection.isLUB_val_image`, which is already a theorem
  needing neither nonemptiness nor directedness, where the closure version has to
  build the ambient supremum and check it lands back in the image;
* the corestriction is Scott continuity of `p` itself — where the closure version
  spends the inflationary law `x ⊑ r x` to see that an upper bound of `r '' D`
  inside `im(r)` already bounds `D`. -/

section ProjectionRange

variable {U : Type*} [CompletePartialOrder U] {p : ScottHom U U}

/-- **The inclusion `im(p) ↪ D` is Scott continuous**, for any projection `p`.
This is `IsProjection.isLUB_val_image` read as a continuity statement; the
closure counterpart is `IsClosure.scottContinuous_val`. -/
theorem scottContinuous_val (hp : IsProjection p) :
    ScottContinuous (Subtype.val : ↥(Set.range ⇑p) → U) :=
  fun _ _ _ _ ha => hp.isLUB_val_image ha

/-- **The corestriction `x ↦ p x` onto `im(p)` is Scott continuous.** The
upper-bound half is monotonicity of `p`; the least half is continuity of `p` in
`D`, since an upper bound taken inside `im(p)` is in particular an ambient one.

Measured: **no projection law is used**, so this holds for an arbitrary
continuous `p` and takes no hypothesis. The closure counterpart
`IsClosure.scottContinuous_val` does spend the inflationary law `x ⊑ r x`, to see
that an upper bound of `r '' D` inside `im(r)` already bounds `D`. -/
theorem scottContinuous_corestrict (p : ScottHom U U) :
    ScottContinuous (fun x : U => (⟨p x, Set.mem_range_self x⟩ : ↥(Set.range ⇑p))) := by
  intro d hne hd a ha
  have hcont : IsLUB (⇑p '' d) (p a) := p.scottContinuous hne hd ha
  refine ⟨?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact p.monotone (ha.1 hx)
  · rintro ⟨b, hb⟩ hub
    show p a ≤ b
    exact hcont.2 (by rintro _ ⟨x, hx, rfl⟩; exact hub ⟨x, hx, rfl⟩)

end ProjectionRange

/-! ## `im((q, p)) ≅ (im p → im q)` at a projection pair

The paper's "evident isomorphism":

> Now, there is an evident isomorphism between continuous functions
> `f : im(r) → im(s)` and continuous functions `g : P N → P N` such that
> `g = s ∘ g ∘ r`.

`im((q, p))` *is* the set of such `g`, because `(q, p)` is idempotent
(`isProjection_compHom`). The four declarations below are
`UniversalDomain.lean`'s `restrictHom`, `extendHom`, `extendHom_mem_range` and
`evidentOrderIso` with `IsClosure` replaced by `IsProjection`. Every step that
used a closure law used only `apply_of_mem_range` and `idem`, which a projection
has as well; the inflationary law appears nowhere in this section. -/

section EvidentEquiv

variable {U : Type u} [CompletePartialOrder U] {p q : ScottHom U U}

/-- `G ↦ G` restricted to `im(p)` and corestricted to `im(q)`. The projection
proof on the *codomain* side is unused here — `scottContinuous_corestrict` needs
none — which is the first half of the measurement that the closure laws are
spent nowhere in this section. -/
noncomputable def restrictHomP (hp : IsProjection p) (_hq : IsProjection q)
    (G : ScottHom U U) : ScottHom ↥(Set.range ⇑p) ↥(Set.range ⇑q) :=
  ⟨fun x => ⟨q (G x.val), Set.mem_range_self _⟩,
    ScottContinuous.comp (ScottContinuous.comp (scottContinuous_val hp) G.scottContinuous)
      (scottContinuous_corestrict q)⟩

/-- `F ↦ ι ∘ F ∘ (x ↦ p x)`, the inverse direction. Symmetrically, the
projection proof on the *domain* side is unused. -/
noncomputable def extendHomP (_hp : IsProjection p) (hq : IsProjection q)
    (F : ScottHom ↥(Set.range ⇑p) ↥(Set.range ⇑q)) : ScottHom U U :=
  ⟨fun x => (F ⟨p x, Set.mem_range_self x⟩).val,
    ScottContinuous.comp
      (ScottContinuous.comp (scottContinuous_corestrict p) F.scottContinuous)
      (scottContinuous_val hq)⟩

/-- **`ι ∘ F ∘ (x ↦ p x)` is fixed by `(q, p)`**:
`q (F (p (p x))) = q (F (p x)) = F (p x)`, the first equation by idempotence of
`p` and the second because `F` already takes values in `im(q)`. -/
theorem compHom_extendHomP (hp : IsProjection p) (hq : IsProjection q)
    (F : ScottHom ↥(Set.range ⇑p) ↥(Set.range ⇑q)) :
    compHom p q (extendHomP hp hq F) = extendHomP hp hq F := by
  refine ScottHom.ext fun x => ?_
  show q ((F ⟨p (p x), _⟩).val) = (F ⟨p x, _⟩).val
  have hidem : (⟨p (p x), Set.mem_range_self (p x)⟩ : ↥(Set.range ⇑p)) =
      ⟨p x, Set.mem_range_self x⟩ := Subtype.ext (hp.idem x)
  rw [hidem]
  exact hq.apply_of_mem_range (F ⟨p x, Set.mem_range_self x⟩).2

/-- `ι ∘ F ∘ (x ↦ p x)` therefore lies in `im((q, p))`. -/
theorem extendHomP_mem_range (hp : IsProjection p) (hq : IsProjection q)
    (F : ScottHom ↥(Set.range ⇑p) ↥(Set.range ⇑q)) :
    extendHomP hp hq F ∈ Set.range ⇑(compHom p q) :=
  ⟨extendHomP hp hq F, compHom_extendHomP hp hq F⟩

/-- **`im((q, p)) ≅ (im p → im q)`**, the paper's "evident isomorphism", at a
projection pair. -/
noncomputable def evidentOrderIsoP (hp : IsProjection p) (hq : IsProjection q) :
    ↥(Set.range ⇑(compHom p q)) ≃o ScottHom ↥(Set.range ⇑p) ↥(Set.range ⇑q) :=
  Equiv.toOrderIso
    { toFun := fun G => restrictHomP hp hq G.val
      invFun := fun F => ⟨extendHomP hp hq F, extendHomP_mem_range hp hq F⟩
      left_inv := fun G => by
        refine Subtype.ext (ScottHom.ext fun x => ?_)
        show q (G.val (p x)) = G.val x
        exact DFunLike.congr_fun ((isProjection_compHom hp hq).apply_of_mem_range G.2) x
      right_inv := fun F => by
        refine ScottHom.ext fun x => Subtype.ext ?_
        show q ((F ⟨p x.val, Set.mem_range_self x.val⟩).val) = (F x).val
        have hx : (⟨p x.val, Set.mem_range_self x.val⟩ : ↥(Set.range ⇑p)) = x :=
          Subtype.ext (hp.apply_of_mem_range x.2)
        rw [hx]
        exact hq.apply_of_mem_range (F x).2 }
    (fun _ _ h x => q.monotone (h x.val)) (fun _ _ h x => h _)

end EvidentEquiv

/-! ## Conjunct 1: `→` is p-representable -/

section ArrowConjunct

variable {U : Type u} [CompletePartialOrder U]

/-- **`im((q, p))` is a domain when `im(p)` and `im(q)` are**, over a bounded
complete domain `U`. This is the obligation `Fp` adds and `Fc` does not, and it
is the only place `[BoundedComplete U]` is spent in the whole arrow conjunct.

Through `evidentOrderIsoP` it reduces to `Domain (im p → im q)`, which is
`FunctionSpaceCountable.lean`'s instance under `[Domain (im p)]`,
`[Domain (im q)]` and `[BoundedComplete (im q)]`; the first two are what
`IsFinitaryProjection` supplies and the third is `PRep.boundedComplete_range`. -/
theorem domain_range_compHom [BoundedComplete U] {p q : ScottHom U U}
    (hp : IsProjection p) (hq : IsProjection q)
    (hdp : @Domain _ (IsProjection.rangeCompletePartialOrder hp))
    (hdq : @Domain _ (IsProjection.rangeCompletePartialOrder hq)) :
    @Domain _ (IsProjection.rangeCompletePartialOrder (isProjection_compHom hp hq)) := by
  letI : CompletePartialOrder ↥(Set.range ⇑p) := IsProjection.rangeCompletePartialOrder hp
  letI : CompletePartialOrder ↥(Set.range ⇑q) := IsProjection.rangeCompletePartialOrder hq
  haveI : Domain ↥(Set.range ⇑p) := hdp
  haveI : Domain ↥(Set.range ⇑q) := hdq
  haveI : BoundedComplete ↥(Set.range ⇑q) := boundedComplete_range hq
  haveI : Domain (ScottHom ↥(Set.range ⇑p) ↥(Set.range ⇑q)) := inferInstance
  letI : CompletePartialOrder ↥(Set.range ⇑(compHom p q)) :=
    IsProjection.rangeCompletePartialOrder (isProjection_compHom hp hq)
  exact domain_orderIso (evidentOrderIsoP hp hq).symm

/-- The conjugating family for `→`, indexed by `Fp(U) × Fp(U)` rather than
`Fc(U) × Fc(U)`: Gunter & Scott's `(s, r)(f) = s ∘ f ∘ r`. -/
noncomputable def arrowFamily (q : ↥(Fp U) × ↥(Fp U)) :
    ScottHom (ScottHom U U) (ScottHom U U) :=
  compHom q.1.val q.2.val

theorem isProjection_arrowFamily (q : ↥(Fp U) × ↥(Fp U)) :
    IsProjection (arrowFamily q) :=
  isProjection_compHom (mem_Fp.mp q.1.2).isProjection (mem_Fp.mp q.2.2).isProjection

theorem arrowFamily_mono {q q' : ↥(Fp U) × ↥(Fp U)} (h : q ≤ q') :
    arrowFamily q ≤ arrowFamily q' := fun f => compHom_mono h.1 h.2 f

/-- **The `Fp` counterpart of `isLUB_compHom_of_isLUB`.** The script is the
closure version's verbatim, with the index type changed and the two coordinate
least upper bounds supplied by `PRep.isLUB_val_image_of_isLUB_fp'` instead of
`isLUB_val_image_of_isLUB`. That substitution is where `[Domain U]` is spent:
`isFinitaryProjection_sSup` is what makes least upper bounds in `Fp(U)`
pointwise, and it holds over a domain and is not free.

At a point `y` the argument unwinds three suprema — `a₁ y = ⨆ r y`, then `f`'s
continuity, then `a₂`'s — leaving `s (f (r y)) ⊑ v y` for an *arbitrary* pair
`(r, s)` drawn from the two coordinates separately; directedness of `d` puts them
back on the diagonal. -/
theorem isLUB_arrowFamily [Domain U] {d : Set (↥(Fp U) × ↥(Fp U))}
    (hne : d.Nonempty) (hd : DirectedOn (· ≤ ·) d) {a : ↥(Fp U) × ↥(Fp U)}
    (ha : IsLUB d a) (f : ScottHom U U) :
    IsLUB ((fun q => arrowFamily q f) '' d) (arrowFamily a f) := by
  have hdfst : DirectedOn (· ≤ ·) (Prod.fst '' d) := by
    rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩
    obtain ⟨c, hc, hpc, hqc⟩ := hd p hp q hq
    exact ⟨c.1, ⟨c, hc, rfl⟩, hpc.1, hqc.1⟩
  have hdsnd : DirectedOn (· ≤ ·) (Prod.snd '' d) := by
    rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩
    obtain ⟨c, hc, hpc, hqc⟩ := hd p hp q hq
    exact ⟨c.2, ⟨c, hc, rfl⟩, hpc.2, hqc.2⟩
  have h₁ : IsLUB ((fun q : ↥(Fp U) × ↥(Fp U) => q.1.val) '' d) a.1.val := by
    have := isLUB_val_image_of_isLUB_fp' (hne.image _) hdfst (isLUB_prod.mp ha).1
    rwa [Set.image_image] at this
  have h₂ : IsLUB ((fun q : ↥(Fp U) × ↥(Fp U) => q.2.val) '' d) a.2.val := by
    have := isLUB_val_image_of_isLUB_fp' (hne.image _) hdsnd (isLUB_prod.mp ha).2
    rwa [Set.image_image] at this
  have hd₁ : DirectedOn (· ≤ ·) ((fun q : ↥(Fp U) × ↥(Fp U) => q.1.val) '' d) := by
    rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩
    obtain ⟨c, hc, hpc, hqc⟩ := hd p hp q hq
    exact ⟨c.1.val, ⟨c, hc, rfl⟩, hpc.1, hqc.1⟩
  have hd₂ : DirectedOn (· ≤ ·) ((fun q : ↥(Fp U) × ↥(Fp U) => q.2.val) '' d) := by
    rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩
    obtain ⟨c, hc, hpc, hqc⟩ := hd p hp q hq
    exact ⟨c.2.val, ⟨c, hc, rfl⟩, hpc.2, hqc.2⟩
  refine ⟨?_, ?_⟩
  · rintro _ ⟨c, hc, rfl⟩
    exact compHom_mono (h₁.1 ⟨c, hc, rfl⟩) (h₂.1 ⟨c, hc, rfl⟩) f
  · intro v hv y
    have hAne : ((fun g : ScottHom U U => g y) ''
        ((fun q : ↥(Fp U) × ↥(Fp U) => q.1.val) '' d)).Nonempty :=
      (hne.image _).image _
    have hAdir := ScottHom.directedOn_eval_image hd₁ y
    have hA := ScottHom.isLUB_eval_image_of_isLUB hd₁ h₁ y
    have hfA := f.scottContinuous hAne hAdir hA
    have hfAdir := ScottHom.directedOn_image f hAdir
    have h2 := a.2.val.scottContinuous (hAne.image _) hfAdir hfA
    refine h2.2 ?_
    rintro _ ⟨_, ⟨_, ⟨_, ⟨c, hc, rfl⟩, rfl⟩, rfl⟩, rfl⟩
    refine (ScottHom.isLUB_eval_image_of_isLUB hd₂ h₂ (f (c.1.val y))).2 ?_
    rintro _ ⟨_, ⟨c', hc', rfl⟩, rfl⟩
    obtain ⟨e, he, hce, hc'e⟩ := hd c hc c' hc'
    exact (compHom_mono hce.1 hc'e.2 f y).trans (hv ⟨e, he, rfl⟩ y)

/-- **`→` is p-representable over any bounded complete domain that retracts onto
its own function space** — conjunct 1 of Lemma 28, at the notion §7.3 fixes.

The hypothesis is the paper's own pair, `→⁻ ∘ →⁺ = id` and `→⁺ ∘ →⁻ ⊑ id`. The
second inequality points the **opposite** way from `Combinator.Retracts`, which
is what `Combinator.rep_arrow` assumes; `PRep.gr_fn_eq_of_both` shows the two are
simultaneously satisfiable only when `U ≅ (U → U)`, so this is not `rep_arrow`
re-stated but a different theorem. At §7.3's `U` the pair is what **Theorem 27**
supplies, and `[BoundedComplete U]` is the hypothesis of that theorem. -/
theorem rep_arrow [Domain U] [BoundedComplete U]
    {fn : ScottHom U (ScottHom U U)} {gr : ScottHom (ScottHom U U) U}
    (hfg : ∀ y, fn (gr y) = y) (hgf : ∀ x, gr (fn x) ≤ x) :
    IsPRepresentable₂ U funOp :=
  isPRepresentable₂_of_repFamily hfg
    (fun q => isFinitaryProjection_repOf hfg hgf (isProjection_arrowFamily q)
      (domain_range_compHom _ _ (mem_Fp.mp q.1.2).domain (mem_Fp.mp q.2.2).domain))
    arrowFamily_mono isLUB_arrowFamily
    fun q => ⟨evidentOrderIsoP (mem_Fp.mp q.1.2).isProjection
      (mem_Fp.mp q.2.2).isProjection⟩

end ArrowConjunct

/-! ## `Domain (D →⊥ E)` — the closure property `⇸` needs, which was not present

`ClosureProperties.lean` states Lemma 10 and Lemma 17 for the strict function
space — `lem10_strict : BoundedComplete (StrictHom α β)` and
`lem17_strictFun : IsBifinite (StrictHom α β)` — but the development **had** no
`Domain (StrictHom α β)`, and `Fp`'s second conjunct asks for exactly that at the
images. Measured over every module before this section, the `IsAlgebraic`
instances present were `Set X`, `ScottHom α β`, `α × β`, `WithBot α` and
`IdealCompletion A`; the strict function space was not among them.
`strictHomDomain`, below in this file, closes that.

It is nonetheless cheap, because `D →⊥ E` is a **downward-closed** sub-cpo of
`D → E`: anything below a strict function is strict (`isStrict_of_le`). So the
compact approximants of `f` in the subtype are, on the nose, the compact
approximants of `f.val` in `D → E` (`val_image_compactsBelow`) — no
strictification is needed here, unlike in
`ClosureProperties/StrictFunction.lean`, where the two *compactness* transfers do
need it because an arbitrary directed family of `D → E` need not be strict. -/

section StrictDomain

variable {α β : Type*} [CompletePartialOrder α] [CompletePartialOrder β]

/-- **Anything below a strict function is strict**: `g ⊑ f` and `f ⊥ = ⊥` give
`g ⊥ ⊑ ⊥`. This is the whole reason the section is short. -/
theorem isStrict_of_le {f g : ScottHom α β} (hf : IsStrict f) (hg : g ≤ f) : IsStrict g :=
  le_antisymm ((hg ⊥).trans (le_of_eq hf)) bot_le

/-- **The compact approximants of `f` in `D →⊥ E` are those of `f.val` in
`D → E`.** Left to right is `isCompactElement_val_of_isCompactElement`; right to
left is `isCompactElement_of_isCompactElement_val` together with
`isStrict_of_le`, which is what makes the right-hand side land in the subtype at
all. -/
theorem val_image_compactsBelow (f : StrictHom α β) :
    Subtype.val '' compactsBelow f = compactsBelow (f.val : ScottHom α β) := by
  ext g
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨ClosureProperties.isCompactElement_val_of_isCompactElement hk.1, hk.2⟩
  · rintro ⟨hgc, hgf⟩
    exact ⟨⟨g, isStrict_of_le f.2 hgf⟩,
      ⟨ClosureProperties.isCompactElement_of_isCompactElement_val hgc, hgf⟩, rfl⟩

/-- **`D →⊥ E` is algebraic when `D → E` is.** Both fields transport across
`val_image_compactsBelow`; the only step with content is that the ambient
approximant produced by directedness is automatically strict. -/
theorem strictHomIsAlgebraic [Domain α] [Domain β] [BoundedComplete β] :
    IsAlgebraic (StrictHom α β) where
  directedOn_compactsBelow f := by
    intro k₁ hk₁ k₂ hk₂
    have h₁ : (k₁.val : ScottHom α β) ∈ compactsBelow (f.val : ScottHom α β) := by
      rw [← val_image_compactsBelow]; exact ⟨k₁, hk₁, rfl⟩
    have h₂ : (k₂.val : ScottHom α β) ∈ compactsBelow (f.val : ScottHom α β) := by
      rw [← val_image_compactsBelow]; exact ⟨k₂, hk₂, rfl⟩
    obtain ⟨K, hK, hK₁, hK₂⟩ :=
      IsAlgebraic.directedOn_compactsBelow (f.val : ScottHom α β) _ h₁ _ h₂
    exact ⟨⟨K, isStrict_of_le f.2 hK.2⟩,
      ⟨ClosureProperties.isCompactElement_of_isCompactElement_val hK.1, hK.2⟩, hK₁, hK₂⟩
  isLUB_compactsBelow f := by
    refine ⟨fun k hk => hk.2, fun v hv => ?_⟩
    show (f.val : ScottHom α β) ≤ v.val
    refine (IsAlgebraic.isLUB_compactsBelow (f.val : ScottHom α β)).2 ?_
    rw [← val_image_compactsBelow]
    rintro _ ⟨k, hk, rfl⟩
    exact hv hk

/-- **`D →⊥ E` is a domain when `D` and `E` are and `E` is bounded complete.**
Countability is `Subtype.val` injecting `K(D →⊥ E)` into `K(D → E)`, which is
countable by `FunctionSpaceCountable.lean`'s instance (Theorem 7). Stated as a
theorem rather than an `instance`, so that it fires only where it is named. -/
theorem strictHomDomain [Domain α] [Domain β] [BoundedComplete β] :
    Domain (StrictHom α β) where
  __ := strictHomIsAlgebraic
  countable_compacts := by
    have hsub : compacts (StrictHom α β) ⊆ Subtype.val ⁻¹' compacts (ScottHom α β) :=
      fun _ hc => ClosureProperties.isCompactElement_val_of_isCompactElement hc
    exact Set.Countable.mono hsub
      ((Domain.countable_compacts (α := ScottHom α β)).preimage Subtype.val_injective)

end StrictDomain

/-! ## Conjunct 2: `⇸` is p-representable

The paper draws this operator `∘→`; it is §4.2's strict continuous function
space, `StrictHom`. The conjugating object is `U ⇸ U` rather than `U → U`, and
the conjugating family is the **same** `(q, p)`, restricted — which is legitimate
because `isStrict_compHom` says `(q, p) f` is strict whenever `p`, `q` and `f`
are, and a projection is strict for free (`IsProjection.map_bot`, `p ⊥ = ⊥`).

So the arrow's pattern goes through with strictness threaded along one component
at a time. The plan asked whether that is all there is to it; measured, it is
*not*: the extra content is the `Domain` obligation, which needed
`strictHomDomain` above — a closure property the development did not have. -/

section StrictArrowConjunct

variable {U : Type u} [CompletePartialOrder U]

/-- **The conjugating family for `⇸`**, indexed by `Fp(U) × Fp(U)`: Gunter &
Scott's `(s, r)` cut down to the strict function space.

Continuity in `f` is `compHom`'s, moved across the subtype: least upper bounds in
`U ⇸ U` are those of `U → U` (`ClosureProperties.isLUB_val_image_of_isLUB`), so
neither half needs a case split on `⊥`. -/
noncomputable def strictArrowFamily (c : ↥(Fp U) × ↥(Fp U)) :
    ScottHom (StrictHom U U) (StrictHom U U) :=
  ⟨fun f => ⟨compHom c.1.val c.2.val f.val,
      ClosureProperties.isStrict_compHom (mem_Fp.mp c.1.2).isProjection.map_bot
        (mem_Fp.mp c.2.2).isProjection.map_bot f.2⟩, by
    intro d hne hd a ha
    have hdv : DirectedOn (· ≤ ·) ((Subtype.val : StrictHom U U → ScottHom U U) '' d) := by
      rintro _ ⟨f, hf, rfl⟩ _ ⟨g, hg, rfl⟩
      obtain ⟨e, he, hfe, hge⟩ := hd f hf g hg
      exact ⟨e.val, ⟨e, he, rfl⟩, hfe, hge⟩
    have hval : IsLUB ((Subtype.val : StrictHom U U → ScottHom U U) '' d) a.val :=
      ClosureProperties.isLUB_val_image_of_isLUB hd ha
    have hC := (compHom c.1.val c.2.val).scottContinuous (hne.image _) hdv hval
    refine ⟨?_, ?_⟩
    · rintro _ ⟨f, hf, rfl⟩
      exact (compHom c.1.val c.2.val).monotone (ha.1 hf)
    · rintro v hv
      show compHom c.1.val c.2.val a.val ≤ v.val
      refine hC.2 ?_
      rintro _ ⟨_, ⟨f, hf, rfl⟩, rfl⟩
      exact hv ⟨f, hf, rfl⟩⟩

@[simp] theorem strictArrowFamily_val (c : ↥(Fp U) × ↥(Fp U)) (f : StrictHom U U) :
    (strictArrowFamily c f).val = compHom c.1.val c.2.val f.val := rfl

/-- `(q, p)` restricted to `U ⇸ U` is a projection: both laws are the ambient
ones, because the order on the subtype is the ambient order on `.val`. -/
theorem isProjection_strictArrowFamily (c : ↥(Fp U) × ↥(Fp U)) :
    IsProjection (strictArrowFamily c) := by
  have h := isProjection_compHom (mem_Fp.mp c.1.2).isProjection (mem_Fp.mp c.2.2).isProjection
  exact ⟨fun f => Subtype.ext (h.idem f.val), fun f => h.le f.val⟩

theorem strictArrowFamily_mono {c c' : ↥(Fp U) × ↥(Fp U)} (h : c ≤ c') :
    strictArrowFamily c ≤ strictArrowFamily c' :=
  fun f => compHom_mono h.1 h.2 f.val

/-- The `Fp`-indexed least upper bound for `⇸`, obtained from the arrow's by
`ClosureProperties.isLUB_val_image_of_isLUB`'s observation that suprema of
`U ⇸ U` are suprema of `U → U`: an upper bound in the subtype is in particular
an ambient one, so nothing beyond `isLUB_arrowFamily` is needed. -/
theorem isLUB_strictArrowFamily [Domain U] {d : Set (↥(Fp U) × ↥(Fp U))}
    (hne : d.Nonempty) (hd : DirectedOn (· ≤ ·) d) {a : ↥(Fp U) × ↥(Fp U)}
    (ha : IsLUB d a) (f : StrictHom U U) :
    IsLUB ((fun c => strictArrowFamily c f) '' d) (strictArrowFamily a f) := by
  have hA := isLUB_arrowFamily hne hd ha f.val
  refine ⟨?_, ?_⟩
  · rintro _ ⟨c, hc, rfl⟩
    exact compHom_mono (ha.1 hc).1 (ha.1 hc).2 f.val
  · rintro v hv
    show compHom a.1.val a.2.val f.val ≤ v.val
    refine hA.2 ?_
    rintro _ ⟨c, hc, rfl⟩
    exact hv ⟨c, hc, rfl⟩

/-! ### `im((q, p)|⇸) ≅ (im p ⇸ im q)`

The paper's evident isomorphism again, with `StrictHom` on both sides. The two
underlying maps are `restrictHomP` and `extendHomP` unchanged; all that is new is
that each preserves strictness, and each of those two facts is one equation:
`q (G ⊥) = ⊥` and `(F ⊥)ᵥ = ⊥`, using `p ⊥ = ⊥` and `q ⊥ = ⊥`. -/

section StrictEvident

variable (c : ↥(Fp U) × ↥(Fp U))

/-- `G` in the image of the restricted `(q, p)` has `G.val` in the image of the
ambient `(q, p)`. -/
theorem val_mem_range_compHom {G : StrictHom U U}
    (hG : G ∈ Set.range ⇑(strictArrowFamily c)) :
    (G.val : ScottHom U U) ∈ Set.range ⇑(compHom c.1.val c.2.val) := by
  obtain ⟨f, rfl⟩ := hG
  exact ⟨f.val, rfl⟩

/-- **Restriction preserves strictness**: `q (G ⊥) = q ⊥ = ⊥`. Stated as the map
into `im p ⇸ im q`, so the `OrderBot` and `CompletePartialOrder` instances are
the ones `strictFunOp` uses rather than ones re-synthesized. -/
noncomputable def strictRestrict (G : StrictHom U U) :
    (strictFunOp (FpImage c.1) (FpImage c.2)).carrier :=
  ⟨restrictHomP (mem_Fp.mp c.1.2).isProjection (mem_Fp.mp c.2.2).isProjection G.val, by
    apply Subtype.ext
    show c.2.val (G.val ⊥) = (⊥ : U)
    rw [G.2]
    exact (mem_Fp.mp c.2.2).isProjection.map_bot⟩

/-- **Extension preserves strictness**: `(F ⟨p ⊥, _⟩)ᵥ = (F ⊥)ᵥ = ⊥`, using
`p ⊥ = ⊥` to identify the argument with `⊥` of `im(p)`. -/
noncomputable def strictExtend (F : (strictFunOp (FpImage c.1) (FpImage c.2)).carrier) :
    StrictHom U U :=
  ⟨extendHomP (mem_Fp.mp c.1.2).isProjection (mem_Fp.mp c.2.2).isProjection F.val, by
    show (F.val ⟨c.1.val ⊥, Set.mem_range_self ⊥⟩).val = (⊥ : U)
    have harg : (⟨c.1.val ⊥, Set.mem_range_self ⊥⟩ : ↥(Set.range ⇑c.1.val)) =
        ⟨⊥, (mem_Fp.mp c.1.2).isProjection.bot_mem_range⟩ :=
      Subtype.ext (mem_Fp.mp c.1.2).isProjection.map_bot
    rw [harg]
    exact congrArg Subtype.val F.2⟩

/-- **`im((q,p)|⇸) ≅ (im p ⇸ im q)`.** The forward map is `restrictHomP`, whose
strictness is `q (G ⊥) = q ⊥ = ⊥`; the inverse is `extendHomP`, whose strictness
is `(F ⟨p ⊥, _⟩)ᵥ = (F ⊥)ᵥ = ⊥`. The two round trips are `evidentOrderIsoP`'s,
wrapped in one extra `Subtype.ext` each. -/
noncomputable def strictEvidentOrderIso :
    ↥(Set.range ⇑(strictArrowFamily c)) ≃o
      (strictFunOp (FpImage c.1) (FpImage c.2)).carrier :=
  have hp : IsProjection c.1.val := (mem_Fp.mp c.1.2).isProjection
  have hq : IsProjection c.2.val := (mem_Fp.mp c.2.2).isProjection
  Equiv.toOrderIso
    { toFun := fun G => strictRestrict c G.val
      invFun := fun F => ⟨strictExtend c F,
        ⟨strictExtend c F, Subtype.ext (compHom_extendHomP hp hq F.val)⟩⟩
      left_inv := fun G => by
        refine Subtype.ext (Subtype.ext (ScottHom.ext fun x => ?_))
        show c.2.val (G.val.val (c.1.val x)) = G.val.val x
        exact DFunLike.congr_fun
          ((isProjection_compHom hp hq).apply_of_mem_range (val_mem_range_compHom c G.2)) x
      right_inv := fun F => by
        refine Subtype.ext (ScottHom.ext fun x => Subtype.ext ?_)
        show c.2.val ((F.val ⟨c.1.val x.val, _⟩).val) = (F.val x).val
        have hx : (⟨c.1.val x.val, Set.mem_range_self x.val⟩ : ↥(Set.range ⇑c.1.val)) = x :=
          Subtype.ext (hp.apply_of_mem_range x.2)
        rw [hx]
        exact hq.apply_of_mem_range (F.val x).2 }
    (fun _ _ h x => c.2.val.monotone (h x.val)) (fun _ _ h x => h _)

end StrictEvident

/-- **`im(R⇸(p,q))` is a domain**, the obligation `Fp` adds. Through
`strictEvidentOrderIso` it reduces to `Domain (im p ⇸ im q)`, which is
`strictHomDomain` — the closure property proved above precisely for this step. -/
theorem domain_range_strictArrowFamily [Domain U] [BoundedComplete U]
    (c : ↥(Fp U) × ↥(Fp U)) :
    @Domain _ (IsProjection.rangeCompletePartialOrder (isProjection_strictArrowFamily c)) := by
  haveI : Domain (FpImage c.1).carrier := (mem_Fp.mp c.1.2).domain
  haveI : Domain (FpImage c.2).carrier := (mem_Fp.mp c.2.2).domain
  haveI : BoundedComplete (FpImage c.2).carrier :=
    boundedComplete_range (mem_Fp.mp c.2.2).isProjection
  haveI : Domain (strictFunOp (FpImage c.1) (FpImage c.2)).carrier := strictHomDomain
  letI : CompletePartialOrder ↥(Set.range ⇑(strictArrowFamily c)) :=
    IsProjection.rangeCompletePartialOrder (isProjection_strictArrowFamily c)
  exact domain_orderIso (strictEvidentOrderIso c).symm

/-- **`⇸` is p-representable over any bounded complete domain that retracts onto
its own strict function space** — conjunct 2 of Lemma 28.

The hypothesis is again the paper's pair, with the inequality pointing the
projection way. `[BoundedComplete U]` is spent in exactly one place,
`boundedComplete_range` inside `domain_range_strictArrowFamily`, and Theorem 27
is the sentence that makes it the setting's own hypothesis rather than an extra
one. -/
theorem rep_strictArrow [Domain U] [BoundedComplete U]
    {fn : ScottHom U (StrictHom U U)} {gr : ScottHom (StrictHom U U) U}
    (hfg : ∀ y, fn (gr y) = y) (hgf : ∀ x, gr (fn x) ≤ x) :
    IsPRepresentable₂ U strictFunOp :=
  isPRepresentable₂_of_repFamily hfg
    (fun c => isFinitaryProjection_repOf hfg hgf (isProjection_strictArrowFamily c)
      (domain_range_strictArrowFamily c))
    strictArrowFamily_mono isLUB_strictArrowFamily
    fun c => ⟨strictEvidentOrderIso c⟩

end StrictArrowConjunct

/-! ## Conjunct 4: `⊗`, and the two things the development did not have

r0034 refuted `⊗` at the *closure* notion with a three-chain counterexample. That
refutation does not apply here: a projection satisfies `p ⊥ = ⊥`, which is
exactly the hypothesis the counterexample violated. Measured, nothing in this
section reproduces it — the smash's `⊥` is the adjoined one and every map below
sends it to itself.

What blocked `⊗` was different, and it was two missing constructions rather than
an obstruction. Both are now present in this file; the past tense is the point,
and it matches the corrected wording of this module's own header above.

1. **`r ⊗ s` did not exist.** `grep` over every module found no functorial action
   on the smash; `Isomorphism/Smash.lean` supplies only `smashComm` and
   `smashAssoc`. This section builds it — `smashMap`, below in this file.
2. **`Domain (D ⊗ E)` did not exist.** `ClosureProperties.lean` has
   `lem10_smash : BoundedComplete (Smash α β)` and
   `lem17_smash : IsBifinite (Smash α β)`, and the `IsAlgebraic` instances in the
   development were `Set X`, `ScottHom α β`, `α × β`, `WithBot α` and
   `IdealCompletion A` — the smash was not among them. `SmashObstruction` below
   names this as a `Prop`, so the gap is a statement the kernel elaborates rather
   than a sentence of prose, and `smashIsAlgebraic` and `smashDomain` — also
   below in this file — close it.

The decomposition this section is built on is worth stating separately, because
it is what makes `r ⊗ s` cheap: `D ⊗ E` sits between `D × E` and itself by a
**Scott-continuous pair**

    ι : D ⊗ E → D × E     the adjoined bottom to `(⊥, ⊥)`, a pair to itself
    π : D × E → D ⊗ E     a pair with both coordinates non-`⊥` to itself,
                          anything else to the adjoined bottom

and `r ⊗ s = π ∘ (r × s) ∘ ι`. Continuity of `r ⊗ s` is then a composite instead
of a case analysis over `Smash`'s branching `sSup`. `ι` is *not* a retraction of
`π` in either direction — `π (ι x) = x` holds but `ι (π p) ≠ p` when `p` has one
`⊥` coordinate — so this is a decomposition, not a conjugation. -/

section SmashMaps

variable {α β : Type*} [CompletePartialOrder α] [CompletePartialOrder β]

/-- `ι : D ⊗ E → D × E`. -/
def smashEmbed : Smash α β → α × β :=
  WithBot.recBotCoe (⊥, ⊥) Subtype.val

@[simp] theorem smashEmbed_bot : smashEmbed (⊥ : Smash α β) = (⊥, ⊥) := rfl

@[simp] theorem smashEmbed_coe (q : NonBotPair α β) :
    smashEmbed (↑q : Smash α β) = q.val := rfl

open Classical in
/-- `π : D × E → D ⊗ E`, collapsing every pair with a `⊥` coordinate onto the
adjoined bottom. -/
noncomputable def smashCollapse (p : α × β) : Smash α β :=
  if h : p.1 ≠ ⊥ ∧ p.2 ≠ ⊥ then ↑(⟨p, h⟩ : NonBotPair α β) else ⊥

theorem smashCollapse_of {p : α × β} (h : p.1 ≠ ⊥ ∧ p.2 ≠ ⊥) :
    smashCollapse p = ↑(⟨p, h⟩ : NonBotPair α β) := by
  classical simp only [smashCollapse, dif_pos h]

theorem smashCollapse_of_not {p : α × β} (h : ¬ (p.1 ≠ ⊥ ∧ p.2 ≠ ⊥)) :
    smashCollapse p = (⊥ : Smash α β) := by
  classical simp only [smashCollapse, dif_neg h]

theorem monotone_smashCollapse : Monotone (smashCollapse : α × β → Smash α β) := by
  intro x y hxy
  by_cases hx : x.1 ≠ ⊥ ∧ x.2 ≠ ⊥
  · have hy : y.1 ≠ ⊥ ∧ y.2 ≠ ⊥ :=
      ⟨fun h => hx.1 (le_bot_iff.mp (hxy.1.trans (le_of_eq h))),
        fun h => hx.2 (le_bot_iff.mp (hxy.2.trans (le_of_eq h)))⟩
    rw [smashCollapse_of hx, smashCollapse_of hy]
    exact WithBot.coe_le_coe.mpr hxy
  · rw [smashCollapse_of_not hx]
    exact bot_le

/-- **`ι` is Scott continuous.** On a family whose base is empty every member is
the adjoined bottom and both sides are `(⊥, ⊥)`; otherwise the least upper bound
is a coercion, and `smashSup_of_directed` identifies its value with the ambient
supremum of the base, which the arbitrary upper bound in `D × E` already
dominates. -/
theorem scottContinuous_smashEmbed :
    ScottContinuous (smashEmbed : Smash α β → α × β) := by
  intro d hne hd u hu
  by_cases hb : (smashBase d).Nonempty
  · obtain ⟨q₀, hq₀⟩ := hb
    have hdb : DirectedOn (· ≤ ·) (smashBase d) := directedOn_smashBase hd
    have hvdb : DirectedOn (· ≤ ·) (Subtype.val '' smashBase d) :=
      directedOn_val_smashBase hdb
    have hsup : u = smashSup d := hu.unique hd.isLUB_sSup
    rw [smashSup_of_directed ⟨q₀, hq₀⟩ hdb] at hsup
    subst hsup
    refine ⟨?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩
      induction x using WithBot.recBotCoe with
      | bot => exact ⟨bot_le, bot_le⟩
      | coe q => exact hvdb.le_sSup ⟨q, hx, rfl⟩
    · intro v hv
      refine hvdb.sSup_le ?_
      rintro _ ⟨q, hq, rfl⟩
      exact hv ⟨(↑q : Smash α β), coe_mem_of_mem_smashBase hq, rfl⟩
  · have hbot : ∀ x ∈ d, x = (⊥ : Smash α β) := by
      intro x hx
      induction x using WithBot.recBotCoe with
      | bot => rfl
      | coe q => exact absurd ⟨q, hx⟩ hb
    have hubot : u = (⊥ : Smash α β) :=
      le_antisymm (hu.2 fun x hx => le_of_eq (hbot x hx)) bot_le
    subst hubot
    obtain ⟨x₀, hx₀⟩ := hne
    refine ⟨?_, fun v hv => ?_⟩
    · rintro _ ⟨x, hx, rfl⟩
      rw [hbot x hx]
    · rw [← hbot x₀ hx₀]
      exact hv ⟨x₀, hx₀, rfl⟩

/-- **`π` is Scott continuous.** The branch where the supremum has a `⊥`
coordinate is forced: every member of the family is below it, so every member has
that coordinate `⊥` too, and the whole image is the adjoined bottom.

The other branch is the one with content, and the step it turns on is that the
members with **both** coordinates non-`⊥` are *cofinal*: `isLUB_prod` gives an
`x₁ ∈ t` with `x₁.1 ≠ ⊥` and an `x₂ ∈ t` with `x₂.2 ≠ ⊥`, directedness produces
one above both — which then has both coordinates non-`⊥` — and directedness again
puts any member below such a one. -/
theorem scottContinuous_smashCollapse :
    ScottContinuous (smashCollapse : α × β → Smash α β) := by
  intro t hne ht w hw
  by_cases hb : w.1 ≠ ⊥ ∧ w.2 ≠ ⊥
  · rw [smashCollapse_of hb]
    refine ⟨?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩
      rw [← smashCollapse_of hb]
      exact monotone_smashCollapse (hw.1 hx)
    · intro v hv
      -- a member of `t` with both coordinates non-`⊥`
      obtain ⟨x₁, hx₁t, hx₁⟩ : ∃ x ∈ t, x.1 ≠ ⊥ := by
        by_contra hcon
        refine hb.1 (le_bot_iff.mp ((isLUB_prod.mp hw).1.2 ?_))
        rintro _ ⟨x, hx, rfl⟩
        exact le_of_eq (not_not.mp fun h => hcon ⟨x, hx, h⟩)
      obtain ⟨x₂, hx₂t, hx₂⟩ : ∃ x ∈ t, x.2 ≠ ⊥ := by
        by_contra hcon
        refine hb.2 (le_bot_iff.mp ((isLUB_prod.mp hw).2.2 ?_))
        rintro _ ⟨x, hx, rfl⟩
        exact le_of_eq (not_not.mp fun h => hcon ⟨x, hx, h⟩)
      obtain ⟨c, hct, hc₁, hc₂⟩ := ht x₁ hx₁t x₂ hx₂t
      have hcne : c.1 ≠ ⊥ ∧ c.2 ≠ ⊥ :=
        ⟨fun h => hx₁ (le_bot_iff.mp (hc₁.1.trans (le_of_eq h))),
          fun h => hx₂ (le_bot_iff.mp (hc₂.2.trans (le_of_eq h)))⟩
      -- so `v` is not the adjoined bottom
      have hvc : (↑(⟨c, hcne⟩ : NonBotPair α β) : Smash α β) ≤ v := by
        rw [← smashCollapse_of hcne]; exact hv ⟨c, hct, rfl⟩
      induction v using WithBot.recBotCoe with
      | bot => exact absurd hvc (WithBot.not_coe_le_bot _)
      | coe r =>
        refine WithBot.coe_le_coe.mpr (hw.2 fun x hx => ?_)
        obtain ⟨e, het, hxe, hce⟩ := ht x hx c hct
        have hene : e.1 ≠ ⊥ ∧ e.2 ≠ ⊥ :=
          ⟨fun h => hcne.1 (le_bot_iff.mp (hce.1.trans (le_of_eq h))),
            fun h => hcne.2 (le_bot_iff.mp (hce.2.trans (le_of_eq h)))⟩
        have hle : (↑(⟨e, hene⟩ : NonBotPair α β) : Smash α β) ≤ (↑r : Smash α β) := by
          rw [← smashCollapse_of hene]
          exact hv ⟨e, het, rfl⟩
        have hle2 : (⟨e, hene⟩ : NonBotPair α β) ≤ r := WithBot.coe_le_coe.mp hle
        exact hxe.trans hle2
  · have hbot : ∀ x ∈ t, smashCollapse x = (⊥ : Smash α β) := by
      intro x hx
      refine smashCollapse_of_not fun hxne => hb ?_
      exact ⟨fun h => hxne.1 (le_bot_iff.mp ((hw.1 hx).1.trans (le_of_eq h))),
        fun h => hxne.2 (le_bot_iff.mp ((hw.1 hx).2.trans (le_of_eq h)))⟩
    rw [smashCollapse_of_not hb]
    obtain ⟨x₀, hx₀⟩ := hne
    refine ⟨?_, fun v hv => ?_⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact le_of_eq (hbot x hx)
    · rw [← hbot x₀ hx₀]
      exact hv ⟨x₀, hx₀, rfl⟩

/-! The order on `D ⊗ E` between two coercions is the order of `D × E`. Both
directions are `WithBot.coe_le_coe`, named here because the coercion `D × E ↪
(D × E)⊥` is also in scope and the elaborator picks it from the expected type
otherwise. -/

theorem smash_le_of_coe_le {q r : NonBotPair α β} (h : (↑q : Smash α β) ≤ ↑r) :
    q.val ≤ r.val :=
  have h' : q ≤ r := WithBot.coe_le_coe.mp h
  h'

theorem smash_coe_le_of_le {q r : NonBotPair α β} (h : q.val ≤ r.val) :
    (↑q : Smash α β) ≤ ↑r := WithBot.coe_le_coe.mpr h

/-- Being non-`⊥` in both coordinates is an upward-closed property. -/
theorem nonBot_of_le {x y : α × β} (h : x ≤ y) (hx : x.1 ≠ ⊥ ∧ x.2 ≠ ⊥) :
    y.1 ≠ ⊥ ∧ y.2 ≠ ⊥ :=
  ⟨fun hb => hx.1 (le_bot_iff.mp (h.1.trans (le_of_eq hb))),
    fun hb => hx.2 (le_bot_iff.mp (h.2.trans (le_of_eq hb)))⟩

/-- **A directed family whose least upper bound has both coordinates non-`⊥` has a
member with both coordinates non-`⊥`.** If every member had first coordinate `⊥`
then `isLUB_prod` would make the supremum's first coordinate `⊥`; the same on the
second; and directedness puts the two witnesses under one member. -/
theorem exists_nonBot_of_isLUB {t : Set (α × β)} (ht : DirectedOn (· ≤ ·) t)
    {w : α × β} (hw : IsLUB t w) (hb : w.1 ≠ ⊥ ∧ w.2 ≠ ⊥) :
    ∃ c ∈ t, c.1 ≠ ⊥ ∧ c.2 ≠ ⊥ := by
  obtain ⟨x₁, hx₁t, hx₁⟩ : ∃ x ∈ t, x.1 ≠ ⊥ := by
    by_contra hcon
    refine hb.1 (le_bot_iff.mp ((isLUB_prod.mp hw).1.2 ?_))
    rintro _ ⟨x, hx, rfl⟩
    exact le_of_eq (not_not.mp fun h => hcon ⟨x, hx, h⟩)
  obtain ⟨x₂, hx₂t, hx₂⟩ : ∃ x ∈ t, x.2 ≠ ⊥ := by
    by_contra hcon
    refine hb.2 (le_bot_iff.mp ((isLUB_prod.mp hw).2.2 ?_))
    rintro _ ⟨x, hx, rfl⟩
    exact le_of_eq (not_not.mp fun h => hcon ⟨x, hx, h⟩)
  obtain ⟨c, hct, hc₁, hc₂⟩ := ht x₁ hx₁t x₂ hx₂t
  exact ⟨c, hct, fun h => hx₁ (le_bot_iff.mp (hc₁.1.trans (le_of_eq h))),
    fun h => hx₂ (le_bot_iff.mp (hc₂.2.trans (le_of_eq h)))⟩

end SmashMaps

/-! ## `IsAlgebraic (D ⊗ E)` and `Domain (D ⊗ E)`

The gap named in this section's opening docstring, and confirmed independently by
this round's stream 5: the smash product carries Lemma 10 and Lemma 17 in the
library and is proved algebraic nowhere. `IsPRepresentable` routes obligation 4
through `Domain` of the operator's image, and `Domain` is `IsAlgebraic` plus a
countable basis, so `⊗` cannot be closed without this.

It is proved here rather than assumed, and the continuous pair `ι`, `π` above is
what makes it short. The characterization of the compacts runs one direction
through each map:

* `q.val` compact in `D × E` ⟹ `↑q` compact in `D ⊗ E` — push the family through
  `ι`, and note the witness cannot be the adjoined bottom because `q` has no `⊥`
  coordinate;
* `↑q` compact in `D ⊗ E` ⟹ `q.val` compact in `D × E` — push the family through
  `π`, whose value at the supremum is a coercion precisely because `q.val` sits
  below it.

Algebraicity then transports from `isAlgebraic_prod`, with `exists_nonBot_of_isLUB`
supplying the one step that is not formal: the compact approximants of `q.val`
with a `⊥` coordinate are discarded, and what remains is still cofinal. -/

section SmashDomain

variable {α β : Type*} [CompletePartialOrder α] [CompletePartialOrder β]

/-- **Compactness in `D ⊗ E` is compactness in `D × E`**, for the non-bottom
elements. -/
theorem isCompactElement_smash_coe_iff {q : NonBotPair α β} :
    IsCompactElement (↑q : Smash α β) ↔ IsCompactElement q.val := by
  constructor
  · -- push a family of `D × E` through `π`
    intro hq t w hne ht hw hqw
    have hb : w.1 ≠ ⊥ ∧ w.2 ≠ ⊥ := nonBot_of_le hqw q.2
    have hdir : DirectedOn (· ≤ ·) ((smashCollapse : α × β → Smash α β) '' t) := by
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb', rfl⟩
      obtain ⟨c, hc, hac, hbc⟩ := ht a ha b hb'
      exact ⟨_, ⟨c, hc, rfl⟩, monotone_smashCollapse hac, monotone_smashCollapse hbc⟩
    have hlub := scottContinuous_smashCollapse hne ht hw
    rw [smashCollapse_of hb] at hlub
    obtain ⟨_, ⟨x, hx, rfl⟩, hle⟩ :=
      hq _ _ (hne.image _) hdir hlub (smash_coe_le_of_le (r := ⟨w, hb⟩) hqw)
    by_cases hxb : x.1 ≠ ⊥ ∧ x.2 ≠ ⊥
    · rw [smashCollapse_of hxb] at hle
      exact ⟨x, hx, smash_le_of_coe_le hle⟩
    · rw [smashCollapse_of_not hxb] at hle
      exact absurd hle (WithBot.not_coe_le_bot q)
  · -- push a family of `D ⊗ E` through `ι`
    intro hq s u hne hs hu hqu
    have hdir : DirectedOn (· ≤ ·) ((smashEmbed : Smash α β → α × β) '' s) := by
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      obtain ⟨c, hc, hac, hbc⟩ := hs a ha b hb
      exact ⟨_, ⟨c, hc, rfl⟩,
        (scottContinuous_smashEmbed).monotone hac, (scottContinuous_smashEmbed).monotone hbc⟩
    obtain ⟨_, ⟨x, hx, rfl⟩, hle⟩ :=
      hq _ _ (hne.image _) hdir (scottContinuous_smashEmbed hne hs hu)
        ((scottContinuous_smashEmbed).monotone hqu)
    refine ⟨x, hx, ?_⟩
    induction x using WithBot.recBotCoe with
    | bot => exact absurd (le_bot_iff.mp hle.1) q.2.1
    | coe k => exact WithBot.coe_le_coe.mpr hle

/-- **`D ⊗ E` is algebraic when `D` and `E` are.** -/
theorem smashIsAlgebraic [IsAlgebraic α] [IsAlgebraic β] : IsAlgebraic (Smash α β) := by
  haveI : IsAlgebraic (α × β) := isAlgebraic_prod
  constructor
  · -- directedness of `compactsBelow x`
    intro x
    induction x using WithBot.recBotCoe with
    | bot =>
      intro y hy z hz
      exact ⟨⊥, bot_mem_compactsBelow ⊥, le_of_eq (le_bot_iff.mp hy.2),
        le_of_eq (le_bot_iff.mp hz.2)⟩
    | coe q =>
      intro y
      induction y using WithBot.recBotCoe with
      | bot => exact fun _ z hz => ⟨z, hz, bot_le, le_rfl⟩
      | coe ky =>
        intro hy z
        induction z using WithBot.recBotCoe with
        | bot => exact fun _ => ⟨(↑ky : Smash α β), hy, le_rfl, bot_le⟩
        | coe kz =>
          intro hz
          have hcy : IsCompactElement ky.val := isCompactElement_smash_coe_iff.mp hy.1
          have hcz : IsCompactElement kz.val := isCompactElement_smash_coe_iff.mp hz.1
          obtain ⟨K, hK, hKy, hKz⟩ := IsAlgebraic.directedOn_compactsBelow q.val
            ky.val ⟨hcy, smash_le_of_coe_le hy.2⟩ kz.val ⟨hcz, smash_le_of_coe_le hz.2⟩
          have hKne : K.1 ≠ ⊥ ∧ K.2 ≠ ⊥ := nonBot_of_le hKy ky.2
          exact ⟨(↑(⟨K, hKne⟩ : NonBotPair α β) : Smash α β),
            ⟨isCompactElement_smash_coe_iff.mpr hK.1,
              smash_coe_le_of_le (q := ⟨K, hKne⟩) hK.2⟩,
            smash_coe_le_of_le (q := ky) (r := ⟨K, hKne⟩) hKy,
            smash_coe_le_of_le (q := kz) (r := ⟨K, hKne⟩) hKz⟩
  · -- `x` is the least upper bound of its compact approximants
    intro x
    refine ⟨fun k hk => hk.2, ?_⟩
    intro v hv
    induction x using WithBot.recBotCoe with
    | bot => exact bot_le
    | coe q =>
      -- a non-`⊥` compact approximant of `q.val` exists, so `v` is not the bottom
      obtain ⟨c, hc, hcne⟩ := exists_nonBot_of_isLUB
        (IsAlgebraic.directedOn_compactsBelow q.val)
        (IsAlgebraic.isLUB_compactsBelow q.val) q.2
      have hcv : (↑(⟨c, hcne⟩ : NonBotPair α β) : Smash α β) ≤ v :=
        hv ⟨isCompactElement_smash_coe_iff.mpr hc.1,
          smash_coe_le_of_le (q := ⟨c, hcne⟩) (r := q) hc.2⟩
      induction v using WithBot.recBotCoe with
      | bot => exact absurd hcv (WithBot.not_coe_le_bot _)
      | coe r =>
        refine smash_coe_le_of_le ((IsAlgebraic.isLUB_compactsBelow q.val).2 ?_)
        intro k hk
        by_cases hkne : k.1 ≠ ⊥ ∧ k.2 ≠ ⊥
        · have h : (↑(⟨k, hkne⟩ : NonBotPair α β) : Smash α β) ≤ ↑r :=
            hv ⟨isCompactElement_smash_coe_iff.mpr hk.1,
              smash_coe_le_of_le (q := ⟨k, hkne⟩) (r := q) hk.2⟩
          exact smash_le_of_coe_le h
        · -- a compact approximant with a `⊥` coordinate is dominated by one without
          obtain ⟨K, hK, hKc, hKk⟩ := IsAlgebraic.directedOn_compactsBelow q.val
            c hc k hk
          have hKne : K.1 ≠ ⊥ ∧ K.2 ≠ ⊥ := nonBot_of_le hKc hcne
          have h : (↑(⟨K, hKne⟩ : NonBotPair α β) : Smash α β) ≤ ↑r :=
            hv ⟨isCompactElement_smash_coe_iff.mpr hK.1,
              smash_coe_le_of_le (q := ⟨K, hKne⟩) (r := q) hK.2⟩
          exact hKk.trans (smash_le_of_coe_le h)

/-- **`D ⊗ E` is a domain when `D` and `E` are.** The basis injects into
`K(D × E)` with one extra point, the adjoined bottom; `domain_prod` supplies the
countability of the former. -/
theorem smashDomain [Domain α] [Domain β] : Domain (Smash α β) := by
  haveI : Domain (α × β) := domain_prod
  refine { __ := smashIsAlgebraic, countable_compacts := ?_ }
  have hsub : compacts (Smash α β) ⊆
      insert (⊥ : Smash α β)
        ((fun p : α × β => (smashCollapse p : Smash α β)) '' compacts (α × β)) := by
    intro x hx
    induction x using WithBot.recBotCoe with
    | bot => exact Set.mem_insert _ _
    | coe q =>
      refine Set.mem_insert_of_mem _ ⟨q.val, isCompactElement_smash_coe_iff.mp hx, ?_⟩
      exact (smashCollapse_of q.2).trans rfl
  exact Set.Countable.mono hsub
    (Set.Countable.insert _ ((Domain.countable_compacts (α := α × β)).image _))

end SmashDomain

/-! ## `r ⊗ s`, the conjugating family for `⊗`

Built as `π ∘ (r × s) ∘ ι`, so its Scott continuity is a composite of three
continuous maps and no case analysis over `Smash`'s branching `sSup` is needed.
The projection laws still need the two cases, but each is one line: at the
adjoined bottom `r ⊥ = ⊥` and `s ⊥ = ⊥` send it to itself, and on a coercion the
laws are `r`'s and `s`'s pushed through `π`'s monotonicity.

The collapse to `⊥` when a coordinate lands on `⊥` is the step that has no
analogue in `×`. It is also the step r0034's counterexample turned on at the
closure notion: there `r ⊥ ⊒ ⊥` could be strictly above `⊥`, so the collapse was
not idempotent. A projection has `r ⊥ = ⊥`, and `isProjection_smashMap` below is
the kernel-checked confirmation. -/

section SmashMap

variable {U : Type u} [CompletePartialOrder U]

/-- **`r ⊗ s`**, as `π ∘ (r × s) ∘ ι`. -/
noncomputable def smashMap (r s : ScottHom U U) : ScottHom (Smash U U) (Smash U U) :=
  ⟨(smashCollapse : U × U → Smash U U) ∘ ⇑(prodMap r s) ∘ (smashEmbed : Smash U U → U × U),
    ScottContinuous.comp
      (ScottContinuous.comp scottContinuous_smashEmbed (prodMap r s).scottContinuous)
      scottContinuous_smashCollapse⟩

@[simp] theorem smashMap_apply (r s : ScottHom U U) (x : Smash U U) :
    smashMap r s x = smashCollapse (r (smashEmbed x).1, s (smashEmbed x).2) := rfl

/-- `r ⊗ s` fixes the adjoined bottom. Only `r ⊥ = ⊥` is used — the collapse
already discards the pair as soon as one coordinate is `⊥` — but the hypothesis
on `s` is kept so the lemma reads as a statement about the pair. -/
theorem smashMap_bot {r s : ScottHom U U} (hr : IsProjection r) (_hs : IsProjection s) :
    smashMap r s (⊥ : Smash U U) = ⊥ := by
  refine smashCollapse_of_not fun h => h.1 ?_
  show r ⊥ = ⊥
  exact hr.map_bot

/-- **`r ⊗ s` is a projection when `r` and `s` are.** `⊑ id` is `π`'s
monotonicity applied to `(r x, s y) ⊑ (x, y)`; idempotence splits on whether the
image coordinates are `⊥`, and on the branch where they are not it is the two
idempotences composed. -/
theorem isProjection_smashMap {r s : ScottHom U U} (hr : IsProjection r) (hs : IsProjection s) :
    IsProjection (smashMap r s) := by
  have hle : ∀ x : Smash U U, smashMap r s x ≤ x := by
    intro x
    induction x using WithBot.recBotCoe with
    | bot => exact le_of_eq (smashMap_bot hr hs)
    | coe q =>
      have h : (r q.val.1, s q.val.2) ≤ q.val := ⟨hr.le _, hs.le _⟩
      have := monotone_smashCollapse h
      rwa [smashCollapse_of q.2] at this
  refine ⟨fun x => ?_, hle⟩
  induction x using WithBot.recBotCoe with
  | bot => rw [smashMap_bot hr hs, smashMap_bot hr hs]
  | coe q =>
    by_cases hb : (r q.val.1) ≠ ⊥ ∧ (s q.val.2) ≠ ⊥
    · show smashCollapse (r (smashEmbed (smashMap r s ↑q)).1,
        s (smashEmbed (smashMap r s ↑q)).2) = smashMap r s ↑q
      have hq : smashMap r s (↑q : Smash U U) =
          ↑(⟨(r q.val.1, s q.val.2), hb⟩ : NonBotPair U U) := smashCollapse_of hb
      rw [hq]
      show smashCollapse (r (r q.val.1), s (s q.val.2)) = _
      rw [hr.idem, hs.idem]
      exact smashCollapse_of hb
    · have hq : smashMap r s (↑q : Smash U U) = ⊥ := smashCollapse_of_not hb
      rw [hq, smashMap_bot hr hs]

theorem smashMap_mono {r r' s s' : ScottHom U U} (hr : r ≤ r') (hs : s ≤ s') :
    smashMap r s ≤ smashMap r' s' :=
  fun _ => monotone_smashCollapse ⟨hr _, hs _⟩

/-! ### The family, indexed by `Fp(U) × Fp(U)` -/

/-- The conjugating family for `⊗`, indexed by `Fp(U) × Fp(U)`. -/
noncomputable def smashFamily (c : ↥(Fp U) × ↥(Fp U)) :
    ScottHom (Smash U U) (Smash U U) :=
  smashMap c.1.val c.2.val

theorem isProjection_smashFamily (c : ↥(Fp U) × ↥(Fp U)) :
    IsProjection (smashFamily c) :=
  isProjection_smashMap (mem_Fp.mp c.1.2).isProjection (mem_Fp.mp c.2.2).isProjection

theorem smashFamily_mono {c c' : ↥(Fp U) × ↥(Fp U)} (h : c ≤ c') :
    smashFamily c ≤ smashFamily c' := smashMap_mono h.1 h.2

/-- The `Fp`-indexed least upper bound for `⊗`. `PRep.isLUB_prodFamily` supplies
it for `r × s` at the argument `ι y`, and `scottContinuous_smashCollapse` carries
it across `π` — which is legitimate because the family is directed there, by
`prodMap_mono`. This is the only place `[Domain U]` is spent in the conjunct, and
it is spent through `PRep.isFinitaryProjection_sSup` exactly as for `→`. -/
theorem isLUB_smashFamily [Domain U] {d : Set (↥(Fp U) × ↥(Fp U))}
    (hne : d.Nonempty) (hd : DirectedOn (· ≤ ·) d) {a : ↥(Fp U) × ↥(Fp U)}
    (ha : IsLUB d a) (y : Smash U U) :
    IsLUB ((fun c => smashFamily c y) '' d) (smashFamily a y) := by
  have hP := isLUB_prodFamily hne hd ha (smashEmbed y)
  have hPdir : DirectedOn (· ≤ ·)
      ((fun c : ↥(Fp U) × ↥(Fp U) => prodFamily c (smashEmbed y)) '' d) := by
    rintro _ ⟨c, hc, rfl⟩ _ ⟨c', hc', rfl⟩
    obtain ⟨e, he, hce, hc'e⟩ := hd c hc c' hc'
    exact ⟨_, ⟨e, he, rfl⟩, prodMap_mono hce.1 hce.2 _, prodMap_mono hc'e.1 hc'e.2 _⟩
  have h := scottContinuous_smashCollapse (hne.image _) hPdir hP
  rwa [Set.image_image] at h

/-! ### `im(r ⊗ s) ≅ (im r) ⊗ (im s)`

Built in the direction that carries no proof obligation in its data — a map
*into* the range, order-reflecting and surjective — and then inverted, which is
`PRep.liftRangeOrderIso`'s pattern. Going the other way would require eliminating
`WithBot` while carrying the range-membership proof, which is dependent
elimination for no gain.

The one fact that has to be checked in both directions is that `⊥` of `im(p)` is
`⊥` of `D`: an element of `im(p)` is non-`⊥` there exactly when its value is
non-`⊥` in `D`. That is `p ⊥ = ⊥` again, and it is what makes the non-bottom
pairs of `im(p) × im(q)` correspond to the non-bottom pairs of `D × E` lying in
the two images. -/

section SmashRange

variable (c : ↥(Fp U) × ↥(Fp U))

theorem val_ne_bot_of_ne_bot {a : ↥(Fp U)} {x : (FpImage a).carrier} (h : x ≠ ⊥) :
    x.val ≠ ⊥ := by
  intro hb
  refine h (Subtype.ext ?_)
  show x.val = (⊥ : U)
  exact hb

theorem ne_bot_of_val_ne_bot {a : ↥(Fp U)} {x : (FpImage a).carrier} (h : x.val ≠ ⊥) :
    x ≠ ⊥ := by
  intro hb
  exact h (by rw [hb]; rfl)

theorem bot_mem_range_smashFamily : (⊥ : Smash U U) ∈ Set.range ⇑(smashFamily c) :=
  ⟨⊥, smashMap_bot (mem_Fp.mp c.1.2).isProjection (mem_Fp.mp c.2.2).isProjection⟩

/-- A non-bottom pair lies in `im(r ⊗ s)` as soon as each coordinate lies in the
corresponding image, because `r` and `s` then fix it. -/
theorem coe_mem_range_smashFamily {k : NonBotPair U U}
    (h₁ : k.val.1 ∈ Set.range ⇑c.1.val) (h₂ : k.val.2 ∈ Set.range ⇑c.2.val) :
    (↑k : Smash U U) ∈ Set.range ⇑(smashFamily c) := by
  refine ⟨(↑k : Smash U U), ?_⟩
  show smashCollapse (c.1.val k.val.1, c.2.val k.val.2) = ↑k
  rw [(mem_Fp.mp c.1.2).isProjection.apply_of_mem_range h₁,
    (mem_Fp.mp c.2.2).isProjection.apply_of_mem_range h₂]
  exact smashCollapse_of k.2

/-- Conversely, a member of `im(r ⊗ s)` is the adjoined bottom or a pair whose
coordinates lie in the two images. -/
theorem range_smashFamily_cases {x : Smash U U} (hx : x ∈ Set.range ⇑(smashFamily c)) :
    x = ⊥ ∨ ∃ k : NonBotPair U U, x = ↑k ∧
      k.val.1 ∈ Set.range ⇑c.1.val ∧ k.val.2 ∈ Set.range ⇑c.2.val := by
  obtain ⟨w, rfl⟩ := hx
  by_cases hb : (c.1.val (smashEmbed w).1) ≠ ⊥ ∧ (c.2.val (smashEmbed w).2) ≠ ⊥
  · exact Or.inr ⟨⟨_, hb⟩, smashCollapse_of hb,
      ⟨(smashEmbed w).1, rfl⟩, ⟨(smashEmbed w).2, rfl⟩⟩
  · exact Or.inl (smashCollapse_of_not hb)

/-- A non-bottom pair of `im(p) × im(q)`, read as a non-bottom pair of `D × E`.
Isolated so that the order comparison below is `Iff.rfl`: both sides unfold to
the same conjunction of two inequalities in `D` and `E`. -/
def nonBotPairDown (P : NonBotPair (FpImage c.1).carrier (FpImage c.2).carrier) :
    NonBotPair U U :=
  ⟨(P.val.1.val, P.val.2.val),
    ⟨val_ne_bot_of_ne_bot P.2.1, val_ne_bot_of_ne_bot P.2.2⟩⟩

theorem nonBotPairDown_le_iff
    (P Q : NonBotPair (FpImage c.1).carrier (FpImage c.2).carrier) :
    nonBotPairDown c P ≤ nonBotPairDown c Q ↔ P ≤ Q := Iff.rfl

/-- The direction of `im(r ⊗ s) ≅ (im r) ⊗ (im s)` carrying no proof obligation
in its data. -/
noncomputable def smashRangeMap (z : (smashOp (FpImage c.1) (FpImage c.2)).carrier) :
    ↥(Set.range ⇑(smashFamily c)) :=
  WithBot.recBotCoe ⟨⊥, bot_mem_range_smashFamily c⟩
    (fun P => ⟨(↑(nonBotPairDown c P) : Smash U U),
      coe_mem_range_smashFamily c P.val.1.2 P.val.2.2⟩) z

theorem smashRangeMap_le_iff (z w : (smashOp (FpImage c.1) (FpImage c.2)).carrier) :
    smashRangeMap c z ≤ smashRangeMap c w ↔ z ≤ w := by
  induction z using WithBot.recBotCoe with
  | bot =>
    refine ⟨fun _ => bot_le, fun _ => ?_⟩
    show (⊥ : Smash U U) ≤ (smashRangeMap c w).val
    exact bot_le
  | coe P =>
    induction w using WithBot.recBotCoe with
    | bot =>
      constructor
      · intro h
        exact absurd (show (↑(nonBotPairDown c P) : Smash U U) ≤ ⊥ from h)
          (WithBot.not_coe_le_bot _)
      · intro h
        exact absurd h (WithBot.not_coe_le_bot P)
    | coe Q =>
      show (↑(nonBotPairDown c P) : Smash U U) ≤ ↑(nonBotPairDown c Q) ↔
        (↑P : Smash (FpImage c.1).carrier (FpImage c.2).carrier) ≤ ↑Q
      rw [WithBot.coe_le_coe, WithBot.coe_le_coe]
      exact nonBotPairDown_le_iff c P Q

theorem smashRangeMap_surjective : Function.Surjective (smashRangeMap c) := by
  rintro ⟨x, hx⟩
  rcases range_smashFamily_cases c hx with hb | ⟨k, hk, h₁, h₂⟩
  · exact ⟨⊥, Subtype.ext hb.symm⟩
  · refine ⟨(↑(⟨(⟨k.val.1, h₁⟩, ⟨k.val.2, h₂⟩),
      ⟨ne_bot_of_val_ne_bot k.2.1, ne_bot_of_val_ne_bot k.2.2⟩⟩ :
        NonBotPair (FpImage c.1).carrier (FpImage c.2).carrier) :
      Smash (FpImage c.1).carrier (FpImage c.2).carrier), ?_⟩
    exact Subtype.ext hk.symm

/-- **`im(r ⊗ s) ≅ (im r) ⊗ (im s)`.** -/
noncomputable def smashRangeOrderIso :
    ↥(Set.range ⇑(smashFamily c)) ≃o (smashOp (FpImage c.1) (FpImage c.2)).carrier :=
  (RelIso.ofSurjective (OrderEmbedding.ofMapLEIff (smashRangeMap c) (smashRangeMap_le_iff c))
    (smashRangeMap_surjective c)).symm

end SmashRange

/-- **`im(R⊗(r,s))` is a domain**, the obligation `Fp` adds. Through
`smashRangeOrderIso` it reduces to `Domain (im r ⊗ im s)`, which is `smashDomain`
— the closure property proved above precisely for this step. Note that unlike
`→` and `⇸` this does **not** spend `[BoundedComplete U]`: the smash needs only
that both factors are domains. -/
theorem domain_range_smashFamily [Domain U] (c : ↥(Fp U) × ↥(Fp U)) :
    @Domain _ (IsProjection.rangeCompletePartialOrder (isProjection_smashFamily c)) := by
  haveI : Domain (FpImage c.1).carrier := (mem_Fp.mp c.1.2).domain
  haveI : Domain (FpImage c.2).carrier := (mem_Fp.mp c.2.2).domain
  haveI : Domain (smashOp (FpImage c.1) (FpImage c.2)).carrier := smashDomain
  letI : CompletePartialOrder ↥(Set.range ⇑(smashFamily c)) :=
    IsProjection.rangeCompletePartialOrder (isProjection_smashFamily c)
  exact domain_orderIso (smashRangeOrderIso c).symm

/-- **`⊗` is p-representable over any domain that retracts onto its own smash
square** — conjunct 4 of Lemma 28.

r0034 refuted this conjunct at the closure notion with a three-chain
counterexample. The refutation turned on `r ⊥` being allowed to sit strictly
above `⊥`, which is exactly what a closure permits and a projection forbids;
`isProjection_smashMap` is where the difference is spent. So the change of notion
was the whole obstruction, and this theorem is the confirmation.

Measured against `→` and `⇸`, this conjunct carries **one hypothesis fewer**:
`[Domain U]` alone, with no `[BoundedComplete U]`. The reason is that the
function-space conjuncts route their `Domain` obligation through
`Domain (D → E)`, which the development proves only for bounded complete `E`
(Theorem 7), while `Domain (D ⊗ E)` needs nothing beyond the two factors. -/
theorem rep_smash [Domain U]
    {fn : ScottHom U (Smash U U)} {gr : ScottHom (Smash U U) U}
    (hfg : ∀ y, fn (gr y) = y) (hgf : ∀ x, gr (fn x) ≤ x) :
    IsPRepresentable₂ U smashOp :=
  isPRepresentable₂_of_repFamily hfg
    (fun c => isFinitaryProjection_repOf hfg hgf (isProjection_smashFamily c)
      (domain_range_smashFamily c))
    smashFamily_mono isLUB_smashFamily
    fun c => ⟨smashRangeOrderIso c⟩

end SmashMap

end ScottDomains.PRepFun
