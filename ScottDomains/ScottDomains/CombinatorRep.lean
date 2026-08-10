import ScottDomains.Powerdomain.Universal
import ScottDomains.Lift

/-!
# §7.3, Lemma 28: representability of the type constructors over an abstract carrier

Gunter & Scott, *Semantic Domains*, §7.3, quoted from the source PDF:

> **Lemma 28** The following operators are representable over `U`: `→`, `⇸`, `×`,
> `⊗`, `+`, `⊕`, `()⊥`, `()♯`, `()♭`.

and, three paragraphs earlier, the construction the lemma's proof is:

> To get a representation for `+`, take a pair of continuous functions
> `+⁻ : U → (U + U)`, `+⁺ : (U + U) → U` such that `+⁻ ∘ +⁺ = id` and
> `+⁺ ∘ +⁻ ⊑ id`. Then take `R+(r, s) = +⁺ ∘ (r + s) ∘ +⁻`.

Everything in this file is that one construction, with the pair `(F⁻, F⁺)` taken
as a *hypothesis* on an abstract carrier rather than manufactured at a particular
`U`. `Retracts U V` is that hypothesis, and `isRepresentable_of_retracts` /
`isRepresentable₂_of_retracts` are the construction.

## What the source actually says, measured against the round's plan

Three statements in the plan for this round do not survive a reading of the PDF.
They are recorded here because they change what may be claimed, not as commentary.

1. **Lemma 28 lists nine operators, not seven.** `⇸` (the strict function space)
   and `⊕` (the coalesced sum) are in the list; the plan's seven drop them.

2. **Lemma 28's "representable" means *p-representable*.** §7.3 redefines the
   word two paragraphs before the lemma — "let us say that an operator `F` on
   cpo's is **p-representable** over a cpo `U` if and only if there is a
   continuous function `R_F` which completes the following diagram (up to
   isomorphism)", with `Fp(U)`, the finitary **projections**, on the bottom row,
   and then "since there will be no chance of confusion, let us just use the term
   'representable' for 'p-representable' for the remainder of this section."
   `ScottDomains.IsRepresentable` and `IsRepresentable₂` are the `Fc(U)` notion —
   finitary **closures** — so they do not state Lemma 28 at any `U`.
   `Powerdomain/Universal.lean` (r0031) recorded the same finding.

3. **Lemma 28's `U` is not `P N`.** It is §7.3's domain of ideals over the finite
   non-empty unions of half-open dyadic intervals of `[0, 1)` ordered by superset,
   for which **Theorem 27** supplies a projection `p : U → D` for every bounded
   complete domain `D`. Over `P N` the `+` conjunct is *false*: §7.1 says
   "unfortunately, there is no representation for the operator `F(X) = X + X` over
   `P N`", and §7.3 opens by naming that failure as the reason for building `U`.

The consequence for this file: the abstract interface is stated for closures,
because that is the notion the development's `IsRepresentable` fixes, and the two
places where the closure reading and the projection reading diverge are measured
below rather than papered over (`§ The smash product`).

## The interface, stated once

`Retracts U V` — a Scott-continuous pair `fn : U → V`, `gr : V → U` with
`fn ∘ gr = id` and `gr ∘ fn ⊒ id` — is the **only** property of the carrier any
proof here uses. No algebraicity, no countable basis, no lattice completeness, no
`Domain U`, and no `Nontrivial U`. At `U = P N` the pair is manufactured by
**Theorem 22** whenever `V` is a countably based algebraic *lattice*; at §7.3's
`U` it is manufactured by **Theorem 27** whenever `V` is a bounded complete
*domain*. Which of the two supplies it is exactly the difference between the
operators `P N` represents and the operators `U` represents, and it is invisible
to every proof below.

Per-operator, the required instance of the interface is:

| # | Operator | `V` | interface instance needed |
| - | -------- | --- | ------------------------- |
| 1 | `→` | `ScottHom U U` | `Retracts U (ScottHom U U)` |
| 2 | `×` | `U × U` | `Retracts U (U × U)` |
| 3 | `()⊥` | `WithBot U` | `Retracts U (WithBot U)` |
| 4 | `+` | `CoalescedSum (WithBot U) (WithBot U)` | `Retracts U (U + U)` |
| 5 | `⊗` | `Smash U U` | not sufficient — see below |
| 6 | `()♯` | Smyth powerdomain | operator undefined on `Cpo` |
| 7 | `()♭` | Hoare powerdomain | operator undefined on `Cpo` |
-/

namespace ScottDomains.Combinator

open ScottDomains.PowerdomainRep

universe u

/-! ## The interface -/

/-- **`V` is a retract of `U` in §7's sense**: a Scott-continuous pair
`fn : U → V`, `gr : V → U` with `fn ∘ gr = id` and `gr ∘ fn ⊒ id`.

This is the paper's `(F⁻, F⁺)`, existentially quantified. It is `IsClosurePair`
read as a property of the pair of carriers rather than of a chosen pair of maps,
which is what lets a representability proof be stated over an abstract `U`: the
proof consumes the *existence* of the pair and nothing else about `U`. -/
def Retracts (U V : Type u) [CompletePartialOrder U] [CompletePartialOrder V] : Prop :=
  ∃ (fn : ScottHom U V) (gr : ScottHom V U), IsClosurePair fn gr

/-! ## The representation scheme

`PowerdomainRep.repOf fn gr C = gr ∘ C ∘ fn` and its three lemmas
(`isClosure_repOf`, `repRangeOrderIso`, `scottContinuous_repOf`) are already
stated for an arbitrary `U` and an arbitrary `V`; only the *index* of the
conjugating family is specialized there to `Fc(U) × Fc(U)`. The one new lemma
below re-proves continuity over an arbitrary preordered index, so that the unary
operators (`()⊥`, `()♯`, `()♭`) and the binary ones share a single script. -/

section Generic

variable {U V : Type u} [CompletePartialOrder U] [CompletePartialOrder V]
  {fn : ScottHom U V} {gr : ScottHom V U}

/-- **`p ↦ R(C p)` is continuous**, over an arbitrary preordered index `P`.

This is `PowerdomainRep.scottContinuous_repOf` with `P` in place of
`Fc(U) × Fc(U)`; the script is unchanged, because that proof never inspects the
index beyond its order. `hCmono` supplies the upper-bound half and `hCeval` — the
statement that `C` evaluated at a fixed point of `V` carries least upper bounds of
the index to least upper bounds in `V` — supplies the least half. -/
theorem scottContinuous_repFamily {P : Type*} [Preorder P]
    (hfg : ∀ y, fn (gr y) = y) (hgf : ∀ x, x ≤ gr (fn x))
    {C : P → ScottHom V V} (hCcl : ∀ p, IsClosure (C p))
    (hCmono : ∀ {p q : P}, p ≤ q → C p ≤ C q)
    (hCeval : ∀ {d : Set P}, d.Nonempty → DirectedOn (· ≤ ·) d → ∀ {a : P}, IsLUB d a →
      ∀ y : V, IsLUB ((fun p => C p y) '' d) (C a y)) :
    ScottContinuous (fun p : P =>
      (⟨repOf fn gr (C p), isClosure_repOf hfg hgf (hCcl p)⟩ : ClosurePoset U)) := by
  intro d hne hd a ha
  refine ⟨?_, ?_⟩
  · rintro _ ⟨p, hp, rfl⟩ x
    exact gr.monotone (hCmono (ha.1 hp) (fn x))
  · intro u hu x
    have hE := hCeval hne hd ha (fn x)
    have hEdir : DirectedOn (· ≤ ·) ((fun p : P => C p (fn x)) '' d) := by
      rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩
      obtain ⟨c, hc, hpc, hqc⟩ := hd p hp q hq
      exact ⟨_, ⟨c, hc, rfl⟩, hCmono hpc (fn x), hCmono hqc (fn x)⟩
    refine (gr.scottContinuous (hne.image _) hEdir hE).2 ?_
    rintro _ ⟨_, ⟨p, hp, rfl⟩, rfl⟩
    exact hu ⟨p, hp, rfl⟩ x

end Generic

section Scheme

variable {U V : Type u} [CompletePartialOrder U] [CompletePartialOrder V]

/-- **The representation scheme, unary.** Given the interface `Retracts U V` and a
conjugating family `C : Fc(U) → (V → V)` of closures with
`im(C r) ≅ F(im r)`, the operator `F` is representable over `U` by
`R_F(r) = F⁺ ∘ C r ∘ F⁻`. -/
theorem isRepresentable_of_retracts {F : Cpo.{u} → Cpo.{u}}
    (hUV : Retracts U V)
    (C : ClosurePoset U → ScottHom V V)
    (hCcl : ∀ r, IsClosure (C r))
    (hCmono : ∀ {r s : ClosurePoset U}, r ≤ s → C r ≤ C s)
    (hCeval : ∀ {d : Set (ClosurePoset U)}, d.Nonempty → DirectedOn (· ≤ ·) d →
      ∀ {a : ClosurePoset U}, IsLUB d a → ∀ y : V, IsLUB ((fun r => C r y) '' d) (C a y))
    (hCiso : ∀ r, Nonempty (↥(Set.range ⇑(C r)) ≃o (F r.image).carrier)) :
    IsRepresentable U F := by
  obtain ⟨fn, gr, hfg, hgf⟩ := hUV
  exact ⟨fun r => ⟨repOf fn gr (C r), isClosure_repOf hfg hgf (hCcl r)⟩,
    scottContinuous_repFamily hfg hgf hCcl hCmono hCeval,
    fun r => (hCiso r).map fun e => (PowerdomainRep.repRangeOrderIso hfg (C r)).trans e⟩

/-- **The representation scheme, binary.** The paper's displayed
`R+(r, s) = +⁺ ∘ (r + s) ∘ +⁻`, with `(+⁻, +⁺)` abstracted to `Retracts U V` and
`r + s` abstracted to `C`. -/
theorem isRepresentable₂_of_retracts {F : Cpo.{u} → Cpo.{u} → Cpo.{u}}
    (hUV : Retracts U V)
    (C : ClosurePoset U × ClosurePoset U → ScottHom V V)
    (hCcl : ∀ p, IsClosure (C p))
    (hCmono : ∀ {p q : ClosurePoset U × ClosurePoset U}, p ≤ q → C p ≤ C q)
    (hCeval : ∀ {d : Set (ClosurePoset U × ClosurePoset U)}, d.Nonempty →
      DirectedOn (· ≤ ·) d → ∀ {a : ClosurePoset U × ClosurePoset U}, IsLUB d a →
      ∀ y : V, IsLUB ((fun p => C p y) '' d) (C a y))
    (hCiso : ∀ p, Nonempty (↥(Set.range ⇑(C p)) ≃o (F p.1.image p.2.image).carrier)) :
    IsRepresentable₂ U F := by
  obtain ⟨fn, gr, hfg, hgf⟩ := hUV
  exact ⟨fun p => ⟨repOf fn gr (C p), isClosure_repOf hfg hgf (hCcl p)⟩,
    scottContinuous_repFamily hfg hgf hCcl hCmono hCeval,
    fun p => (hCiso p).map fun e => (PowerdomainRep.repRangeOrderIso hfg (C p)).trans e⟩

end Scheme

/-! ## Least upper bounds in `Fc(U) × Fc(U)`, coordinatewise

Both binary operators need the two coordinate projections of a least upper bound
taken in `Fc(U) × Fc(U)` to be least upper bounds in `U → U`. The step is
`isLUB_prod` to split the product, then `isLUB_val_image_of_isLUB` to leave the
subtype `Fc(U)`; it is written once here and used by `→` and `×`. -/

section Coordinates

variable {U : Type u} [CompletePartialOrder U]

/-- The first coordinates of a directed set are directed. -/
theorem directedOn_fst_val {d : Set (ClosurePoset U × ClosurePoset U)}
    (hd : DirectedOn (· ≤ ·) d) :
    DirectedOn (· ≤ ·) ((fun p : ClosurePoset U × ClosurePoset U => p.1.val) '' d) := by
  rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩
  obtain ⟨c, hc, hpc, hqc⟩ := hd p hp q hq
  exact ⟨c.1.val, ⟨c, hc, rfl⟩, hpc.1, hqc.1⟩

/-- The second coordinates of a directed set are directed. -/
theorem directedOn_snd_val {d : Set (ClosurePoset U × ClosurePoset U)}
    (hd : DirectedOn (· ≤ ·) d) :
    DirectedOn (· ≤ ·) ((fun p : ClosurePoset U × ClosurePoset U => p.2.val) '' d) := by
  rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩
  obtain ⟨c, hc, hpc, hqc⟩ := hd p hp q hq
  exact ⟨c.2.val, ⟨c, hc, rfl⟩, hpc.2, hqc.2⟩

/-- The first coordinate of a least upper bound in `Fc(U) × Fc(U)` is a least
upper bound in `U → U`. -/
theorem isLUB_fst_val {d : Set (ClosurePoset U × ClosurePoset U)} (hne : d.Nonempty)
    (hd : DirectedOn (· ≤ ·) d) {a : ClosurePoset U × ClosurePoset U} (ha : IsLUB d a) :
    IsLUB ((fun p : ClosurePoset U × ClosurePoset U => p.1.val) '' d) a.1.val := by
  have hdfst : DirectedOn (· ≤ ·) (Prod.fst '' d) := by
    rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩
    obtain ⟨c, hc, hpc, hqc⟩ := hd p hp q hq
    exact ⟨c.1, ⟨c, hc, rfl⟩, hpc.1, hqc.1⟩
  have := isLUB_val_image_of_isLUB (hne.image _) hdfst (isLUB_prod.mp ha).1
  rwa [Set.image_image] at this

/-- The second coordinate of a least upper bound in `Fc(U) × Fc(U)` is a least
upper bound in `U → U`. -/
theorem isLUB_snd_val {d : Set (ClosurePoset U × ClosurePoset U)} (hne : d.Nonempty)
    (hd : DirectedOn (· ≤ ·) d) {a : ClosurePoset U × ClosurePoset U} (ha : IsLUB d a) :
    IsLUB ((fun p : ClosurePoset U × ClosurePoset U => p.2.val) '' d) a.2.val := by
  have hdsnd : DirectedOn (· ≤ ·) (Prod.snd '' d) := by
    rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩
    obtain ⟨c, hc, hpc, hqc⟩ := hd p hp q hq
    exact ⟨c.2, ⟨c, hc, rfl⟩, hpc.2, hqc.2⟩
  have := isLUB_val_image_of_isLUB (hne.image _) hdsnd (isLUB_prod.mp ha).2
  rwa [Set.image_image] at this

end Coordinates

/-! ## 1. The function space `→` -/

section Arrow

variable {U : Type u} [CompletePartialOrder U]

/-- The conjugating family for `→`: Gunter & Scott's `(s, r)(f) = s ∘ f ∘ r`. -/
noncomputable def arrowFamily (p : ClosurePoset U × ClosurePoset U) :
    ScottHom (ScottHom U U) (ScottHom U U) :=
  compHom p.1.val p.2.val

theorem isClosure_arrowFamily (p : ClosurePoset U × ClosurePoset U) :
    IsClosure (arrowFamily p) := isClosure_compHom p.1.2 p.2.2

theorem arrowFamily_mono {p q : ClosurePoset U × ClosurePoset U} (h : p ≤ q) :
    arrowFamily p ≤ arrowFamily q := fun f => compHom_mono h.1 h.2 f

theorem isLUB_arrowFamily {d : Set (ClosurePoset U × ClosurePoset U)} (hne : d.Nonempty)
    (hd : DirectedOn (· ≤ ·) d) {a : ClosurePoset U × ClosurePoset U} (ha : IsLUB d a)
    (f : ScottHom U U) :
    IsLUB ((fun p => arrowFamily p f) '' d) (arrowFamily a f) :=
  isLUB_compHom_of_isLUB hne hd (isLUB_fst_val hne hd ha) (isLUB_snd_val hne hd ha) f

/-- **`→` is representable over any carrier that retracts onto its own function
space.** The paper: "the proof that `→` is representable over `U` is almost
identical to the proof we gave above that it is representable over `P N`" — and
the only thing that changes is where the pair `(→⁻, →⁺)` comes from, which is
exactly what `Retracts U (ScottHom U U)` abstracts. `ScottDomains.lemma_23` is this
theorem at `U = P N`, with the pair supplied by Theorem 22. -/
theorem rep_arrow (h : Retracts U (ScottHom U U)) : IsRepresentable₂ U Cpo.funSpace :=
  isRepresentable₂_of_retracts h arrowFamily isClosure_arrowFamily arrowFamily_mono
    isLUB_arrowFamily fun p => ⟨evidentOrderIso p.1.2 p.2.2⟩

end Arrow

/-! ## 2. The product `×` -/

section Product

variable {U : Type u} [CompletePartialOrder U]

/-- The conjugating family for `×`: Gunter & Scott's `(r × s)(x, y) = (r x, s y)`. -/
def prodFamily (p : ClosurePoset U × ClosurePoset U) : ScottHom (U × U) (U × U) :=
  prodMap p.1.val p.2.val

theorem isClosure_prodFamily (p : ClosurePoset U × ClosurePoset U) :
    IsClosure (prodFamily p) := isClosure_prodMap p.1.2 p.2.2

theorem prodFamily_mono {p q : ClosurePoset U × ClosurePoset U} (h : p ≤ q) :
    prodFamily p ≤ prodFamily q := prodMap_mono h.1 h.2

theorem isLUB_prodFamily {d : Set (ClosurePoset U × ClosurePoset U)} (hne : d.Nonempty)
    (hd : DirectedOn (· ≤ ·) d) {a : ClosurePoset U × ClosurePoset U} (ha : IsLUB d a)
    (y : U × U) :
    IsLUB ((fun p => prodFamily p y) '' d) (prodFamily a y) :=
  isLUB_prodMap_of_isLUB hne hd ha y

/-- **`×` is representable over any carrier that retracts onto its own square.**
`PowerdomainRep.isRepresentable_prod` is this theorem at `U = P N`, with the pair
`(×⁻, ×⁺)` supplied by Theorem 22 at `L = P N × P N`. -/
theorem rep_prod (h : Retracts U (U × U)) : IsRepresentable₂ U prodCpo :=
  isRepresentable₂_of_retracts h prodFamily isClosure_prodFamily prodFamily_mono
    isLUB_prodFamily fun p => ⟨prodRangeOrderIso p.1.val p.2.val⟩

end Product

/-! ## 3. The lift `()⊥`

`Lift.lean` makes `WithBot U` a cpo; this section supplies the conjugating family
`r⊥`, which is `r` on the coercions and the identity on the adjoined bottom, and
the isomorphism `im(r⊥) ≅ (im r)⊥`.

Unlike the smash product below, the lift survives the *closure* reading intact.
The reason is measurable: the bottom of `(im r)⊥` is the **adjoined** element, not
`r ⊥`, so no two points of `im(r⊥)` are identified in the target. -/

section Lift

variable {U : Type u} [CompletePartialOrder U]

/-- The lift operator `()⊥` as an operator on cpos. -/
noncomputable def liftOp (D : Cpo.{u}) : Cpo.{u} := ⟨WithBot D.carrier, liftCpo⟩

/-- A least upper bound of a nonempty set is carried to one by the coercion
`U ↪ U⊥`. Nonemptiness is what forces an upper bound of the image to be a
coercion rather than the adjoined bottom. -/
theorem isLUB_coe_image {S : Set U} (hne : S.Nonempty) {w : U} (hw : IsLUB S w) :
    IsLUB ((fun x : U => (↑x : WithBot U)) '' S) (↑w : WithBot U) := by
  obtain ⟨s₀, hs₀⟩ := hne
  refine ⟨?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact WithBot.coe_le_coe.mpr (hw.1 hx)
  · intro u hu
    have h₀ : (↑s₀ : WithBot U) ≤ u := hu ⟨s₀, hs₀, rfl⟩
    induction u using WithBot.recBotCoe with
    | bot => exact absurd h₀ (WithBot.not_coe_le_bot s₀)
    | coe b =>
      refine WithBot.coe_le_coe.mpr (hw.2 fun x hx => ?_)
      exact WithBot.coe_le_coe.mp (hu ⟨x, hx, rfl⟩)

/-- `r⊥`, the underlying function: `r` on the coercions, the identity on the
adjoined bottom. -/
theorem scottContinuous_liftFun (r : ScottHom U U) :
    ScottContinuous (WithBot.map ⇑r) := by
  intro d hne hd z hz
  by_cases hb : (liftBase d).Nonempty
  · obtain ⟨a₀, ha₀⟩ := hb
    have hdb : DirectedOn (· ≤ ·) (liftBase d) := directedOn_liftBase hd
    have hz₀ : (↑a₀ : WithBot U) ≤ z := hz.1 (coe_mem_of_mem_liftBase ha₀)
    induction z using WithBot.recBotCoe with
    | bot => exact absurd hz₀ (WithBot.not_coe_le_bot a₀)
    | coe w =>
      have hw : IsLUB (liftBase d) w := by
        refine ⟨fun x hx => WithBot.coe_le_coe.mp (hz.1 (coe_mem_of_mem_liftBase hx)), ?_⟩
        intro b hb'
        refine WithBot.coe_le_coe.mp (hz.2 fun x hx => ?_)
        induction x using WithBot.recBotCoe with
        | bot => exact bot_le
        | coe c => exact WithBot.coe_le_coe.mpr (hb' hx)
      have hrw : IsLUB (⇑r '' liftBase d) (r w) := r.scottContinuous ⟨a₀, ha₀⟩ hdb hw
      have hcoe := isLUB_coe_image (S := ⇑r '' liftBase d) ⟨r a₀, ⟨a₀, ha₀, rfl⟩⟩ hrw
      refine ⟨?_, ?_⟩
      · rintro _ ⟨x, hx, rfl⟩
        induction x using WithBot.recBotCoe with
        | bot => simp
        | coe c =>
          have : c ∈ liftBase d := hx
          simpa using WithBot.coe_le_coe.mpr (r.monotone (hw.1 this))
      · intro u hu
        refine hcoe.2 ?_
        rintro _ ⟨_, ⟨c, hc, rfl⟩, rfl⟩
        have := hu ⟨(↑c : WithBot U), coe_mem_of_mem_liftBase hc, rfl⟩
        simpa using this
  · have hbot : ∀ x ∈ d, x = (⊥ : WithBot U) := by
      intro x hx
      induction x using WithBot.recBotCoe with
      | bot => rfl
      | coe c => exact absurd ⟨c, hx⟩ hb
    obtain ⟨x₀, hx₀⟩ := hne
    have hzbot : z = (⊥ : WithBot U) :=
      le_antisymm (hz.2 fun x hx => le_of_eq (hbot x hx)) bot_le
    subst hzbot
    refine ⟨?_, fun u _ => ?_⟩
    · rintro _ ⟨x, hx, rfl⟩
      rw [hbot x hx]
    · simp

/-- `r⊥ : U⊥ → U⊥`, the conjugating family for `()⊥`. -/
noncomputable def liftMap (r : ScottHom U U) : ScottHom (WithBot U) (WithBot U) :=
  ⟨WithBot.map ⇑r, scottContinuous_liftFun r⟩

@[simp] theorem liftMap_bot (r : ScottHom U U) : liftMap r ⊥ = ⊥ := rfl

@[simp] theorem liftMap_coe (r : ScottHom U U) (x : U) :
    liftMap r (↑x : WithBot U) = ↑(r x) := rfl

/-- `r⊥` is a closure whenever `r` is: both laws hold on the coercions by the
corresponding law for `r`, and hold trivially at the adjoined bottom. -/
theorem isClosure_liftMap {r : ScottHom U U} (hr : IsClosure r) : IsClosure (liftMap r) := by
  constructor
  · intro z
    induction z using WithBot.recBotCoe with
    | bot => rfl
    | coe a => simp [hr.idem]
  · intro z
    induction z using WithBot.recBotCoe with
    | bot => exact bot_le
    | coe a => simpa using WithBot.coe_le_coe.mpr (hr.le_apply a)

theorem liftMap_mono {r s : ScottHom U U} (h : r ≤ s) : liftMap r ≤ liftMap s := by
  intro z
  induction z using WithBot.recBotCoe with
  | bot => exact le_rfl
  | coe a => simpa using WithBot.coe_le_coe.mpr (h a)

/-- The conjugating family for `()⊥`, indexed by `Fc(U)`. -/
noncomputable def liftFamily (r : ClosurePoset U) : ScottHom (WithBot U) (WithBot U) :=
  liftMap r.val

theorem isClosure_liftFamily (r : ClosurePoset U) : IsClosure (liftFamily r) :=
  isClosure_liftMap r.2

theorem liftFamily_mono {r s : ClosurePoset U} (h : r ≤ s) : liftFamily r ≤ liftFamily s :=
  liftMap_mono h

theorem isLUB_liftFamily {d : Set (ClosurePoset U)} (hne : d.Nonempty)
    (hd : DirectedOn (· ≤ ·) d) {a : ClosurePoset U} (ha : IsLUB d a) (y : WithBot U) :
    IsLUB ((fun r => liftFamily r y) '' d) (liftFamily a y) := by
  induction y using WithBot.recBotCoe with
  | bot =>
    refine ⟨?_, fun u _ => ?_⟩
    · rintro _ ⟨r, _, rfl⟩
      exact le_rfl
    · exact bot_le
  | coe x =>
    have hdv : DirectedOn (· ≤ ·) ((fun c : ClosurePoset U => c.val) '' d) := by
      rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩
      obtain ⟨c, hc, hpc, hqc⟩ := hd p hp q hq
      exact ⟨c.val, ⟨c, hc, rfl⟩, hpc, hqc⟩
    have hval := isLUB_val_image_of_isLUB hne hd ha
    have heval := ScottHom.isLUB_eval_image_of_isLUB hdv hval x
    rw [Set.image_image] at heval
    have hcoe := isLUB_coe_image (S := (fun c : ClosurePoset U => c.val x) '' d)
      (hne.image _) heval
    rw [Set.image_image] at hcoe
    exact hcoe

/-! ### `im(r⊥) ≅ (im r)⊥` -/

/-- `↑` lands in `im(r⊥)` exactly on `im(r)`, and the adjoined bottom is `r⊥(⊥)`. -/
theorem liftRange_mem (r : ClosurePoset U) (z : WithBot ↥(Set.range ⇑r.val)) :
    WithBot.map Subtype.val z ∈ Set.range ⇑(liftFamily r) := by
  induction z using WithBot.recBotCoe with
  | bot => exact ⟨⊥, rfl⟩
  | coe a =>
    obtain ⟨x, hx⟩ := a.2
    exact ⟨(↑x : WithBot U), by simp [liftFamily, hx]⟩

/-- The forward map of `im(r⊥) ≅ (im r)⊥`, in the direction that carries no proof
obligation inside the data: `(im r)⊥ → im(r⊥)`. -/
noncomputable def liftRangeMap (r : ClosurePoset U) (z : WithBot ↥(Set.range ⇑r.val)) :
    ↥(Set.range ⇑(liftFamily r)) :=
  ⟨WithBot.map Subtype.val z, liftRange_mem r z⟩

theorem liftRangeMap_le_iff (r : ClosurePoset U) (z w : WithBot ↥(Set.range ⇑r.val)) :
    liftRangeMap r z ≤ liftRangeMap r w ↔ z ≤ w := by
  induction z using WithBot.recBotCoe with
  | bot => simp [liftRangeMap]
  | coe a =>
    induction w using WithBot.recBotCoe with
    | bot =>
      constructor
      · intro h
        simp only [liftRangeMap, Subtype.mk_le_mk, WithBot.map_coe, WithBot.map_bot] at h
        exact absurd h (WithBot.not_coe_le_bot a.val)
      · intro h
        exact absurd h (WithBot.not_coe_le_bot a)
    | coe b => simp [liftRangeMap, Subtype.coe_le_coe]

theorem liftRangeMap_surjective (r : ClosurePoset U) :
    Function.Surjective (liftRangeMap r) := by
  rintro ⟨z, w, rfl⟩
  induction w using WithBot.recBotCoe with
  | bot => exact ⟨⊥, rfl⟩
  | coe x =>
    refine ⟨(↑(⟨r.val x, Set.mem_range_self x⟩ : ↥(Set.range ⇑r.val)) : WithBot _), ?_⟩
    exact Subtype.ext rfl

/-- **`im(r⊥) ≅ (im r)⊥`.** -/
noncomputable def liftRangeOrderIso (r : ClosurePoset U) :
    ↥(Set.range ⇑(liftFamily r)) ≃o (liftOp r.image).carrier :=
  (RelIso.ofSurjective (OrderEmbedding.ofMapLEIff (liftRangeMap r) (liftRangeMap_le_iff r))
    (liftRangeMap_surjective r)).symm

/-- **`()⊥` is representable over any carrier that retracts onto its own lift.** -/
theorem rep_lift (h : Retracts U (WithBot U)) : IsRepresentable U liftOp :=
  isRepresentable_of_retracts h liftFamily isClosure_liftFamily liftFamily_mono
    isLUB_liftFamily fun r => ⟨liftRangeOrderIso r⟩

end Lift

/-! ## 4–7. The four operators that are *not* proved here, and exactly why

Three of the four are blocked by mathematics, not by effort. Each is stated with
the obstruction and with the work that would remove it, so the gap is visible
rather than shipped silently.

### `⊗` (smash) and `⊕` (coalesced sum): the closure reading is **false**

The paper's recipe for `⊗` is its own §4.3 definition of the functorial action,
`f ⊗ g = smash ∘ (f × g) ∘ unsmash`, conjugated by a retraction
`U ⇄ (U ⊗ U)`. That action does **not** satisfy `im(r ⊗ s) ≅ im(r) ⊗ im(s)` when
`r` and `s` range over *closures*, and here is a counterexample — a hand
computation, not Lean-checked.

Let `U` be the three-element chain `⊥ ⊏ p ⊏ q`, and let `r = s` be the map
`⊥ ↦ p`, `p ↦ p`, `q ↦ q`. It is a closure: idempotent, and inflationary because
every point is below its image. Then

* `im(r) = {p, q}`, a two-element cpo whose bottom is `p`;
* `im(r) ⊗ im(s)` adjoins a bottom to the pairs of *non-bottom* elements, of which
  there is one, `(q, q)`; so the target has **2** elements;
* `Smash U U` has the four pairs drawn from `{p, q}` plus the adjoined bottom;
  `C(r,s)` sends the adjoined bottom to `smash(r ⊥, s ⊥) = ⟨(p, p)⟩` and each
  `⟨(x, y)⟩` to `⟨(r x, s y)⟩`, so `im(C(r,s))` is all four pairs — **4** elements.

Two is not four. The mechanism is general: `im(r)`'s bottom is `r ⊥`, which a
closure need not send to the ambient `⊥`, and `x = r ⊥` is then a non-bottom point
of `U` that the target collapses and the source does not. The identical
computation refutes the coalesced sum `⊕` (target `{⊥, inl q, inr q}`, 3 elements;
`im(C(r,s))` all four injections plus the bottom, 5 elements).

Under the *projection* reading — `Fp(U)`, which is what §7.3's Lemma 28 actually
uses — the obstruction disappears: a projection satisfies `p ⊑ id`, hence
`p ⊥ = ⊥`, so `im(p)`'s bottom *is* the ambient bottom and no point is collapsed.
This is a precise reason why the paper states Lemma 28 for `Fp(U)` and not for
`Fc(U)`, beyond the reason it gives (that `P N` cannot represent `+`).

### `+` (separated sum): the scheme applies; the functorial action is missing

`+` is *not* refuted. §4.4 defines `D + E` as `D⊥ ⊕ E⊥`, so its bottom is
**adjoined**, exactly as in `()⊥` above, and the collapse that kills `⊗` and `⊕`
does not occur: `im(r⊥ ⊕ s⊥) ≅ (im r)⊥ ⊕ (im s)⊥ = im(r) + im(s)` for closures
`r, s`. The carrier `CoalescedSum (WithBot U) (WithBot U)` already has its cpo
structure (`CoalescedSum.lean`), so no new construction is needed.

What is missing is the functorial action `r + s` on that carrier together with its
Scott continuity, which has to be proved against `CoalescedSum.sumSup` — the four
lemmas `isLUB_leftParts_of_isLUB`, `isLUB_rightParts_of_isLUB`,
`isLUB_image_sumInl`, `isLUB_image_sumInr` are the intended instruments. With that
in hand `rep_sepSum` is `isRepresentable₂_of_retracts` applied exactly as
`rep_prod` is, under `Retracts U (CoalescedSum (WithBot U) (WithBot U))`.

### `()♯` (Smyth) and `()♭` (Hoare): the operator is not defined on `Cpo`

These are blocked one level earlier than the proof. `Powerdomain/Smyth.lean` and
`Powerdomain/Hoare.lean` define the powerdomain of `D` as
`IdealCompletion (Pf ↥(compacts D))` — the ideal completion of the finite
non-empty subsets of `K(D)` — which requires `[Domain D]`, algebraicity with a
countable basis. `IsRepresentable` quantifies over `r : Fc(U)` and needs
`F (im r)`, and `im r` for a closure on a bare cpo carries no `Domain` instance
(`Skeleton/Section6.lean`'s `lemma_19` gives it a `CompletePartialOrder` and nothing
more). So `()♯` and `()♭` are not functions `Cpo → Cpo` in this development and
`IsRepresentable U ()♯` does not typecheck.

Removing this needs one of: a definition of the two powerdomains for arbitrary
cpos (Smyth: the Scott-closed filters; Hoare: the non-empty Scott-closed subsets),
or a version of `IsRepresentable` restricted to closures whose image is a domain —
which is the paper's own `Fc(D)`, whose second conjunct ("`im(r)` is a domain")
`ClosurePoset` deliberately drops, as `UniversalDomain.lean` records. The second
route is the smaller one and is the one §7.3 takes, since Theorem 27's projections
land in **bounded complete domains**. -/

end ScottDomains.Combinator
