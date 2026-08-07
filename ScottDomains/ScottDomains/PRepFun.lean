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
`lem17_strictFun : IsBifinite (StrictHom α β)` — but the development has no
`Domain (StrictHom α β)`, and `Fp`'s second conjunct asks for exactly that at the
images. Measured over every module, the `IsAlgebraic` instances present are
`Set X`, `ScottHom α β`, `α × β`, `WithBot α` and `IdealCompletion A`; the strict
function space is not among them.

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

end ScottDomains.PRepFun
