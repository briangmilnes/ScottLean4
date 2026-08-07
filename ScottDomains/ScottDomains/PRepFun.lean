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
| 2 | `⇸` | `IsPRepresentable₂ U strictFunOp` | open at this commit |
| 4 | `⊗` | `IsPRepresentable₂ U smashOp` | open; the obstruction is located below |

Nothing is stubbed with `sorry`.

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

## Why `⊗` is open, and where exactly

`⊗`'s conjugating family is `r ⊗ s` on `Smash U U`, whose image is
`Smash (im r) (im s)`, so obligation 4 for `⊗` is

    Domain (Smash D E)   for `D`, `E` domains.

**That closure property is not in this development.** Measured: the file
`ClosureProperties.lean` states Lemma 10 (`BoundedComplete (Smash α β)`,
`lem10_smash`) and Lemma 17 (`IsBifinite (Smash α β)`, `lem17_smash`), and
`grep` over every module finds `IsAlgebraic` instances only for `Set X`,
`ScottHom α β`, `α × β`, `WithBot α` and `IdealCompletion A` — none for `Smash`.
Algebraicity of the smash product is a prerequisite the development skipped
because §4.5 and §6.2 never needed it: bounded completeness and bifiniteness were
each proved directly. So `⊗` is not refuted here and not blocked by the notion —
it is blocked by one missing closure property, and `smashObstruction` below names
it as a `Prop` so that the gap is a checkable statement rather than prose.

The r0037 plan's claim that `⊗` is "no longer refuted" is confirmed: nothing in
this file's development of `⊗` reproduces r0034's three-chain counterexample, and
the projection law `p ⊥ = ⊥` is indeed what removes it. The obstruction that
remains is unrelated to the counterexample.

`⇸` did **not** hit the same wall, and that difference is the round's other
measurement: `Domain (StrictHom D E)` is not in the development either, but it is
*derivable in twenty lines* from what is (`domain_strictHom` below), because the
strict functions are a **downward-closed** sub-cpo of `D → E` — anything below a
strict function is strict — so the compacts of the subtype are literally the
compacts of `D → E` lying below, with no strictification needed. The smash has no
such embedding into a space already known to be algebraic.
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

/-- `ι ∘ F ∘ (x ↦ p x)` is fixed by `(q, p)`, hence lies in `im((q, p))`:
`q (F (p (p x))) = q (F (p x)) = F (p x)`, the first equation by idempotence of
`p` and the second because `F` already takes values in `im(q)`. -/
theorem extendHomP_mem_range (hp : IsProjection p) (hq : IsProjection q)
    (F : ScottHom ↥(Set.range ⇑p) ↥(Set.range ⇑q)) :
    extendHomP hp hq F ∈ Set.range ⇑(compHom p q) := by
  refine Set.mem_range.mpr ⟨extendHomP hp hq F, ScottHom.ext fun x => ?_⟩
  show q ((F ⟨p (p x), _⟩).val) = (F ⟨p x, _⟩).val
  have hidem : (⟨p (p x), Set.mem_range_self (p x)⟩ : ↥(Set.range ⇑p)) =
      ⟨p x, Set.mem_range_self x⟩ := Subtype.ext (hp.idem x)
  rw [hidem]
  exact hq.apply_of_mem_range (F ⟨p x, Set.mem_range_self x⟩).2

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

end ScottDomains.PRepFun
