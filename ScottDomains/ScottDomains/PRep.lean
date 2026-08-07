import ScottDomains.PRepresentable
import ScottDomains.CombinatorRep
import ScottDomains.Dyadic
import ScottDomains.ClosureProperties
import ScottDomains.Powerdomain.Smyth
import ScottDomains.Powerdomain.Hoare

/-!
# §7.3, Lemma 28: the nine operators, p-representable over `Fp(U)`

Gunter & Scott, *Semantic Domains*, §7.3. The statement, transcribed from the
rendered page rather than from `pdftotext`:

> **Lemma 28** The following operators are representable over `U`:
> `→`, `⇸`, `×`, `⊗`, `+`, `⊕`, `(·)⊥`, `(·)♯`, `(·)♭`.

and, two paragraphs earlier, the redefinition that fixes what *representable*
means for the rest of the section:

> Let us say that an operator `F` on cpo's is **p-representable** over a cpo `U`
> if and only if there is a continuous function `R_F` which completes the
> following diagram (up to isomorphism) … `Fp(U) --R_F--> Fp(U)` …
> Since there will be no chance of confusion, let us just use the term
> "representable" for "p-representable" for the remainder of this section.

## What the source says, measured against this round's plan

The r0036 plan for this stream gives Lemma 28's list as
`→, ×, ⊗, ⊕, +, ()⊥, ()♮, ()♯, ()♭`. **That list is wrong in two places**, and
the correction is not a matter of reading: page 42 of the PDF was rendered at
600 dpi and read as an image, because the file's Type 3 bitmap fonts carry no
usable `ToUnicode` map and `pdftotext` drops or substitutes every operator glyph
in the line (`♮`/`♯`/`♭` extract as `\`/`]`/`[`, `→` and `⇸` both extract as `!`,
and `×`/`⊗`/`⊕` extract as nothing at all).

1. **`(·)♮` is not in Lemma 28.** The convex (Plotkin) powerdomain appears only
   in **Lemma 30**, over §7.4's bifinite `V`, and §7.4 opens by saying why:
   "The convex powerdomain `(·)♮` cannot be representable over `U` because it does
   not preserve bounded completeness." Adding `(·)♮` to Lemma 28 states something
   the paper explicitly denies.
2. **`⇸` is in Lemma 28** and the plan drops it. The glyph is drawn `∘→`, the
   strict continuous function space of §4.2, `StrictHom`.

The two lemmas read, from the rendered pages:

| # | Lemma | Section | Carrier | Operators |
| - | ----- | ------- | ------- | --------- |
| 1 | 28 | §7.3 | `U`, the dyadic-interval domain | `→ ⇸ × ⊗ + ⊕ (·)⊥ (·)♯ (·)♭` — nine |
| 2 | 30 | §7.4 | `V`, the bifinite universal domain | the same nine plus `(·)♮` — ten |

`ScottDomains.Combinator`'s module docstring (r0034) already recorded the correct
nine and the fact that "representable" here means *p*-representable.
`ScottDomains.BifiniteUniversal`'s docstring, in the same round, recorded the
opposite — "Lemma 28 … is the `Fc` notion" — and that sentence is refuted by the
paper's own "for the remainder of this section", since Lemma 28 stands four
paragraphs *after* the redefinition and inside the same subsection. This file
takes the source's reading: **Lemma 28 is `Fp(U)`.**

## The two obligations `Fp` adds that `Fc` does not

`ClosurePoset U` is `{r // IsClosure r}` — two equations and nothing else.
`↥(Fp U)` is `{p // IsFinitaryProjection p}`, and

    IsFinitaryProjection p ↔ ∃ hp : IsProjection p, Domain ↥(Set.range p)

carries a second component: **`im(p)` must be a domain**, algebraic with a
countable basis. So a representing map at the projection notion owes, for every
`p`, a `Domain` structure on `im(R p)` that the closure notion never asked for.
This is why r0034's `rep_arrow`, `rep_prod` and `rep_lift` do not transfer as
written: each produces `⟨repOf fn gr (C r), isClosure_repOf …⟩`, and the
projection analogue must produce `⟨repOf fn gr (C p), ⟨isProjection_repOf …,
_⟩⟩` where the hole is a `Domain` instance. `PRepresentable.isProjection_repOf`
(r0034) supplies the first component and nothing supplies the second.

The second obligation is continuity of `R : Fp(U) → Fp(U)`, which needs least
upper bounds in the subtype `↥(Fp U)` to be pointwise. The closure case has
`isLUB_val_image_of_isLUB`, resting on `isClosure_sSup`; the projection case
needs the directed supremum of finitary projections to be a finitary projection,
whose `Domain` half is again the new content. `isProjection_sSup_of_directed`
below discharges the *projection* half, which is the part that is true with no
hypothesis on `U` at all.

## What is corrected here about `(·)♯` and `(·)♭`

`ScottDomains.Combinator`'s docstring records the Smyth and Hoare conjuncts as
blocked because "the operator is not defined on `Cpo`" — the powerdomains being
`IdealCompletion (Pf K(D))`, which the file reads as needing `[Domain D]`.
**Measured, that is not where the `Domain` hypothesis is spent.** The *type*
`IdealCompletion (Pf ↥(compacts D))` and its `CompletePartialOrder` instance need
only `[Preorder A]` and `[OrderBot A]` of the base preorder
(`IdealCompletion.lean:232, 324`), both of which `[CompletePartialOrder D]`
already supplies. `[Domain D]` is spent exactly once, on `Countable A`, and only
to make the *result* a domain (`IdealCompletion.instDomain`, line 443).

So `(·)♯` and `(·)♭` **are** functions `Cpo → Cpo`, and both conjuncts of
Lemma 28 are statable. `smythOp` and `hoareOp` below are those functions, and
`smythOp_eq` / `hoareOp_eq` check by `rfl` that they agree with
`Smyth.Powerdomain` and `Hoare.Powerdomain` wherever the latter are defined.

## The nine conjuncts, and where each stands

| # | Operator | Conjunct of `Lemma28` | Status in this file |
| - | -------- | --------------------- | ------------------- |
| 1 | `→`  | `IsPRepresentable₂ U funOp` | open — hypothesis of `lemma28_of` |
| 2 | `⇸`  | `IsPRepresentable₂ U strictFunOp` | open — hypothesis of `lemma28_of` |
| 3 | `×`  | `IsPRepresentable₂ U prodOp` | open — hypothesis of `lemma28_of` |
| 4 | `⊗`  | `IsPRepresentable₂ U smashOp` | open — hypothesis of `lemma28_of` |
| 5 | `+`  | `IsPRepresentable₂ U sepSumOp` | open — hypothesis of `lemma28_of` |
| 6 | `⊕`  | `IsPRepresentable₂ U coalSumOp` | open — hypothesis of `lemma28_of` |
| 7 | `(·)⊥` | `IsPRepresentable U liftOp` | open — hypothesis of `lemma28_of` |
| 8 | `(·)♯` | `IsPRepresentable U smythOp` | open — hypothesis of `lemma28_of` |
| 9 | `(·)♭` | `IsPRepresentable U hoareOp` | open — hypothesis of `lemma28_of` |

No conjunct is stubbed with `sorry`. `lemma28_of` takes each unproved conjunct as
a named hypothesis, so the count nine is checked by the kernel — the anonymous
constructor must supply exactly nine components — and the file never asserts more
than it proves.
-/

namespace ScottDomains.PRep

open ScottDomains ScottDomains.BifiniteUniversal

universe u

/-! ## The nine operators, as operators on cpos

Gunter & Scott's "operator on cpo's" is a function `Cpo → Cpo` (unary) or
`Cpo → Cpo → Cpo` (binary); `Cpo` bundles the carrier with its structure so that
`≅` is `≃o` between carriers. Each of the nine is the §4 construction of the same
name, wrapped with the `CompletePartialOrder` instance the development already
proves for it. -/

section Operators

variable {D E : Cpo.{u}}

/-- **1. `→`**, the continuous function space, `ScottHom D E`. This is
`Cpo.funSpace` under the name the operator list gives it. -/
noncomputable def funOp (D E : Cpo.{u}) : Cpo.{u} := Cpo.funSpace D E

/-- **2. `⇸`**, the *strict* continuous function space of §4.2: the continuous
maps sending `⊥` to `⊥`. This is the conjunct the r0036 plan's list drops. -/
noncomputable def strictFunOp (D E : Cpo.{u}) : Cpo.{u} :=
  ⟨StrictHom D.carrier E.carrier, strictHomCpo⟩

/-- **3. `×`**, the cartesian product with the componentwise order. -/
def prodOp (D E : Cpo.{u}) : Cpo.{u} := PowerdomainRep.prodCpo D E

/-- **4. `⊗`**, the smash product of §4.3: pairs of non-bottom elements with a
single adjoined bottom. -/
noncomputable def smashOp (D E : Cpo.{u}) : Cpo.{u} :=
  ⟨Smash D.carrier E.carrier, smashCpo⟩

/-- **5. `+`**, the separated sum of §4.4, which the paper *defines* as
`D + E = D⊥ ⊕ E⊥` — so its bottom is adjoined rather than shared. -/
noncomputable def sepSumOp (D E : Cpo.{u}) : Cpo.{u} :=
  ⟨ClosureProperties.SeparatedSum D.carrier E.carrier, sumCpo⟩

/-- **6. `⊕`**, the coalesced sum of §4.4: the two carriers glued at a common
bottom. -/
noncomputable def coalSumOp (D E : Cpo.{u}) : Cpo.{u} :=
  ⟨CoalescedSum D.carrier E.carrier, sumCpo⟩

/-- **7. `(·)⊥`**, lifting: one fresh bottom below a copy of `D`. -/
noncomputable def liftOp (D : Cpo.{u}) : Cpo.{u} := ⟨WithBot D.carrier, liftCpo⟩

/-- **8. `(·)♯`**, the Smyth (upper) powerdomain, the ideal completion of
`⟨Pf(K(D)), ⊑♯⟩`. Definable at a bare cpo: `Smyth.Powerdomain` itself takes only
`[CompletePartialOrder D]`. -/
noncomputable def smythOp (D : Cpo.{u}) : Cpo.{u} :=
  ⟨Smyth.Powerdomain D.carrier, inferInstance⟩

/-- **9. `(·)♭`**, the Hoare (lower) powerdomain, the ideal completion of
`⟨Pf(K(D)), ⊑♭⟩`.

Written out as `IdealCompletion (Hoare.Pf ↥(compacts D))` rather than as
`Hoare.Powerdomain D`, because the latter's `variable` block carries a `[Domain
D]` that Lean auto-includes even though the definition does not use it — the
countability it provides is spent on `IdealCompletion.instDomain`, not on the
type. `hoareOp_eq` records that the two agree where both are defined. -/
noncomputable def hoareOp (D : Cpo.{u}) : Cpo.{u} :=
  ⟨IdealCompletion (Hoare.Pf ↥(compacts D.carrier)), inferInstance⟩

/-- `(·)♯` on a *domain* is `Smyth.Powerdomain`, definitionally. -/
theorem smythOp_eq (D : Cpo.{u}) : (smythOp D).carrier = Smyth.Powerdomain D.carrier := rfl

/-- `(·)♭` on a *domain* is `Hoare.Powerdomain`, definitionally — which is the
measurement behind the docstring's claim that the operator is defined on `Cpo`. -/
theorem hoareOp_eq (D : Cpo.{u}) [Domain D.carrier] :
    (hoareOp D).carrier = Hoare.Powerdomain D.carrier := rfl

end Operators

/-! ## Lemma 28, as one nine-fold conjunction

Stated as a `def … : Prop` rather than a theorem, so that the count of conjuncts
is a property of a single definition the kernel elaborates, and every later
result about Lemma 28 names *this* proposition instead of restating the list.
Two earlier rounds of this development lost the count to prose drifting from the
files; a conjunction cannot drift. -/

/-- **Lemma 28** (Gunter & Scott, §7.3): all nine operators are p-representable
over `U`, at `Fp(U)`.

The six binary conjuncts come first in the paper's own order — `→`, `⇸`, `×`,
`⊗`, `+`, `⊕` — then the three unary ones, `(·)⊥`, `(·)♯`, `(·)♭`. `(·)♮` is
absent because the paper's §7.4 says it cannot be representable over `U`. -/
def Lemma28 (U : Type u) [CompletePartialOrder U] : Prop :=
  IsPRepresentable₂ U funOp ∧
  IsPRepresentable₂ U strictFunOp ∧
  IsPRepresentable₂ U prodOp ∧
  IsPRepresentable₂ U smashOp ∧
  IsPRepresentable₂ U sepSumOp ∧
  IsPRepresentable₂ U coalSumOp ∧
  IsPRepresentable U liftOp ∧
  IsPRepresentable U smythOp ∧
  IsPRepresentable U hoareOp

/-- **Lemma 28 from its nine conjuncts.** Every conjunct still open is a named
hypothesis here; the anonymous constructor forces the count to be exactly nine,
so the arity of this theorem *is* the kernel's check on the operator list. As a
conjunct is proved, its hypothesis is deleted and its proof substituted. -/
theorem lemma28_of {U : Type u} [CompletePartialOrder U]
    (h_arrow : IsPRepresentable₂ U funOp)
    (h_strictArrow : IsPRepresentable₂ U strictFunOp)
    (h_prod : IsPRepresentable₂ U prodOp)
    (h_smash : IsPRepresentable₂ U smashOp)
    (h_sepSum : IsPRepresentable₂ U sepSumOp)
    (h_coalSum : IsPRepresentable₂ U coalSumOp)
    (h_lift : IsPRepresentable U liftOp)
    (h_smyth : IsPRepresentable U smythOp)
    (h_hoare : IsPRepresentable U hoareOp) :
    Lemma28 U :=
  ⟨h_arrow, h_strictArrow, h_prod, h_smash, h_sepSum, h_coalSum, h_lift, h_smyth, h_hoare⟩

/-- Lemma 28 is a statement about §7.3's `U`, the ideal completion of the finite
non-empty unions of half-open dyadic intervals of `[0, 1)` ordered by superset —
not about `P N`, over which §7.1 says `X ↦ X + X` has no representation at all.
This abbreviation fixes the carrier so the instantiation cannot drift. -/
abbrev Lemma28AtU : Prop := Lemma28 Dyadic.U

/-! ## Suprema of projections, and least upper bounds in `Fp(U)`

The closure notion's `isClosure_sSup` and `isLUB_val_image_of_isLUB` are what let
`Fc(U)`-indexed continuity proofs be written against the pointwise order. This
section is their projection counterpart, and it separates cleanly into the half
that is free and the half that is not: the pointwise supremum of a directed set
of *projections* is always a projection (`isProjection_sSup`, no hypothesis on
`α` at all), whereas the supremum being **finitary** — `im` a domain — is extra
content, so `isLUB_val_image_of_isLUB_fp` takes it as a hypothesis rather than
pretending it is free. -/

section ProjectionSups

open ScottHom

variable {α : Type u} [CompletePartialOrder α]

/-- **The pointwise supremum of a nonempty directed set of projections is a
projection.**

The counterpart of `isClosure_sSup`, and the inequality runs the other way at
every step. `p ⊑ id` is immediate from the least-upper-bound property. For
idempotence only `⨆d ⊑ (⨆d) ∘ (⨆d)` needs an argument: each `r ∈ d` satisfies
`r x = r (r x)`, and `r x ⊑ (⨆d) x` pushes through `r`'s monotonicity to give
`r x ⊑ r ((⨆d) x) ⊑ (⨆d) ((⨆d) x)`. Note this needs no directedness beyond what
makes the pointwise supremum continuous — unlike the closure case, no element of
`d` above a given pair is chosen. -/
theorem isProjection_sSup {d : Set (ScottHom α α)}
    (hd : DirectedOn (· ≤ ·) d) (hp : ∀ p ∈ d, IsProjection p) :
    IsProjection (sSup d) := by
  have hsup : ∀ x : α, IsLUB ((fun f : ScottHom α α => f x) '' d) ((sSup d) x) := fun x => by
    rw [ScottHom.coe_sSup_of_directed hd x]
    exact (ScottHom.directedOn_eval_image hd x).isLUB_sSup
  have hle : ∀ x : α, (sSup d) x ≤ x := fun x =>
    (hsup x).2 (by rintro _ ⟨r, hr, rfl⟩; exact (hp r hr).le x)
  refine ⟨fun x => le_antisymm (hle _) ?_, hle⟩
  refine (hsup x).2 ?_
  rintro _ ⟨r, hr, rfl⟩
  calc r x = r (r x) := ((hp r hr).idem x).symm
    _ ≤ r ((sSup d) x) := r.monotone ((hsup x).1 ⟨r, hr, rfl⟩)
    _ ≤ (sSup d) ((sSup d) x) := (hsup ((sSup d) x)).1 ⟨r, hr, rfl⟩

/-- **A larger projection fixes a smaller one's image.** `q y ⊑ y` from `q ⊑ id`,
and `y = p y = p (p y) ⊑ q (p y) = q y` from `p ⊑ q`. Used to see the images of a
directed family of projections nest inside the image of their supremum. -/
theorem apply_eq_of_mem_range_of_le {p q : ScottHom α α} (hp : IsProjection p)
    (hq : IsProjection q) (hpq : p ≤ q) {y : α} (hy : y ∈ Set.range ⇑p) : q y = y := by
  refine le_antisymm (hq.le y) ?_
  calc y = p y := (hp.apply_of_mem_range hy).symm
    _ ≤ q y := hpq y

theorem range_subset_of_le {p q : ScottHom α α} (hp : IsProjection p)
    (hq : IsProjection q) (hpq : p ≤ q) : Set.range ⇑p ⊆ Set.range ⇑q := by
  rintro y hy
  exact ⟨y, apply_eq_of_mem_range_of_le hp hq hpq hy⟩

/-- **`im(p)` is bounded complete whenever `D` is.** A set of the image bounded
inside the image is bounded in `D`, so it has an ambient least upper bound;
applying `p` lands it back in the image without moving it past any bound, because
`p` fixes the image and is monotone.

This is one of the two structural facts a representability proof at the
projection notion needs and the closure notion does not: `Fp`'s second conjunct
demands a `Domain` on `im(R p)`, and the function-space conjunct's route to that
`Domain` runs through `Domain (D → E)`, whose Mathlib-side hypothesis set
includes `BoundedComplete E`. -/
theorem boundedComplete_range [BoundedComplete α] {p : ScottHom α α}
    (hp : IsProjection p) :
    @BoundedComplete _ (IsProjection.rangeCompletePartialOrder hp) := by
  letI : CompletePartialOrder ↥(Set.range ⇑p) := IsProjection.rangeCompletePartialOrder hp
  refine ⟨fun s hs => ?_⟩
  obtain ⟨u, hu⟩ := hs
  have hbdd : BddAbove (Subtype.val '' s) :=
    ⟨u.val, by rintro _ ⟨a, ha, rfl⟩; exact hu ha⟩
  have hlub := isLUB_sSup_of_bddAbove hbdd
  constructor
  · intro a ha
    show a.val ≤ p (sSup (Subtype.val '' s))
    calc a.val = p a.val := (hp.apply_of_mem_range a.2).symm
      _ ≤ p (sSup (Subtype.val '' s)) := p.monotone (hlub.1 ⟨a, ha, rfl⟩)
  · intro v hv
    show p (sSup (Subtype.val '' s)) ≤ v.val
    calc p (sSup (Subtype.val '' s))
        ≤ p v.val := p.monotone (hlub.2 (by rintro _ ⟨a, ha, rfl⟩; exact hv ha))
      _ = v.val := hp.apply_of_mem_range v.2

/-- **`K(im p)` is countable whenever `K(D)` is.** By Lemma 5's first sentence
(`IsProjection.isCompactElement_iff`) the compacts of the image are exactly the
image points compact in `D`, so the set injects into `K(D)`. The closure
counterpart is `IsClosure.countable_compacts_range`, which has to work harder —
it factors `K(im r)` through `r '' K(D)` — because a closure does not fix its
image pointwise in the way the compactness criterion needs. -/
theorem countable_compacts_range [Domain α] {p : ScottHom α α} (hp : IsProjection p) :
    (compacts ↥(Set.range ⇑p)).Countable := by
  have hsub : compacts ↥(Set.range ⇑p) ⊆ Subtype.val ⁻¹' compacts α :=
    fun _ hc => hp.isCompactElement_iff.mp hc
  exact Set.Countable.mono hsub
    ((Domain.countable_compacts (α := α)).preimage Subtype.val_injective)

/-- **Least upper bounds in `Fp(D)` are pointwise**, given that the pointwise one
stays inside `Fp(D)`.

The script is `isLUB_val_image_of_isLUB`'s, with `isClosure_sSup` replaced by the
hypothesis `hfin`. Stating `hfin` as a hypothesis rather than proving it is the
honest form: for closures the corresponding fact is a theorem with no side
condition, while for projections the *finitary* half — `im(⨆d)` a domain — is
genuinely extra content, and nothing in this development supplies it. -/
theorem isLUB_val_image_of_isLUB_fp {d : Set ↥(Fp α)}
    (hd : DirectedOn (· ≤ ·) d)
    (hfin : IsFinitaryProjection (sSup ((fun q : ↥(Fp α) => q.val) '' d)))
    {a : ↥(Fp α)} (ha : IsLUB d a) :
    IsLUB ((fun q : ↥(Fp α) => q.val) '' d) a.val := by
  have hedir : DirectedOn (· ≤ ·) ((fun q : ↥(Fp α) => q.val) '' d) := by
    rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩
    obtain ⟨c, hc, h₁, h₂⟩ := hd p hp q hq
    exact ⟨c.val, ⟨c, hc, rfl⟩, h₁, h₂⟩
  have hub : (⟨_, hfin⟩ : ↥(Fp α)) ∈ upperBounds d :=
    fun c hc => hedir.le_sSup ⟨c, hc, rfl⟩
  have heq : a.val = sSup ((fun q : ↥(Fp α) => q.val) '' d) :=
    le_antisymm (ha.2 hub) (hedir.sSup_le (by rintro _ ⟨c, hc, rfl⟩; exact ha.1 hc))
  rw [heq]
  exact hedir.isLUB_sSup

end ProjectionSups

/-! ## Transporting `Domain` along an order isomorphism

`Fp`'s second conjunct is a `Domain` on `im(R p)`, and the only handle on
`im(R p)` any representability proof has is `repRangeOrderIso : im(R C) ≃o im(C)`.
So the obligation is only usable once `Domain` is known to transport along `≃o`,
which it does: `IsCompactElement`, `compacts`, `compactsBelow`, `DirectedOn` and
`IsLUB` are all defined from `≤` alone, so an order isomorphism carries each to
its counterpart. Nothing here depends on the two `CompletePartialOrder`
structures agreeing on `sSup` — only on their orders, which is what `≃o` relates. -/

section Transport

variable {A B : Type*} [PartialOrder A] [PartialOrder B]

theorem directedOn_orderIso_image (e : A ≃o B) {s : Set A} (hs : DirectedOn (· ≤ ·) s) :
    DirectedOn (· ≤ ·) (e '' s) := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  obtain ⟨c, hc, hac, hbc⟩ := hs a ha b hb
  exact ⟨e c, ⟨c, hc, rfl⟩, e.monotone hac, e.monotone hbc⟩

theorem isLUB_orderIso_image (e : A ≃o B) {s : Set A} {u : A} (hu : IsLUB s u) :
    IsLUB (e '' s) (e u) := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩
    exact e.monotone (hu.1 ha)
  · intro v hv
    have h : u ≤ e.symm v := hu.2 fun a ha => by
      simpa using e.symm.monotone (hv ⟨a, ha, rfl⟩)
    simpa using e.monotone h

/-- Compactness is order-theoretic, so an order isomorphism preserves it. -/
theorem isCompactElement_orderIso (e : A ≃o B) {k : A} (hk : IsCompactElement k) :
    IsCompactElement (e k) := by
  intro s u hne hd hlub hle
  obtain ⟨z, hz, hkz⟩ := hk (⇑e.symm '' s) (e.symm u) (hne.image _)
    (directedOn_orderIso_image e.symm hd) (isLUB_orderIso_image e.symm hlub)
    (by simpa using e.symm.monotone hle)
  obtain ⟨w, hw, rfl⟩ := hz
  exact ⟨w, hw, by simpa using e.monotone hkz⟩

theorem compacts_orderIso (e : A ≃o B) : compacts B = ⇑e '' compacts A := by
  ext y
  constructor
  · intro hy
    exact ⟨e.symm y, isCompactElement_orderIso e.symm hy, e.apply_symm_apply y⟩
  · rintro ⟨k, hk, rfl⟩
    exact isCompactElement_orderIso e hk

theorem compactsBelow_orderIso (e : A ≃o B) (x : A) :
    compactsBelow (e x) = ⇑e '' compactsBelow x := by
  ext y
  constructor
  · rintro ⟨hy, hyx⟩
    exact ⟨e.symm y, ⟨isCompactElement_orderIso e.symm hy, by simpa using e.symm.monotone hyx⟩,
      e.apply_symm_apply y⟩
  · rintro ⟨k, ⟨hk, hkx⟩, rfl⟩
    exact ⟨isCompactElement_orderIso e hk, e.monotone hkx⟩

variable {A B : Type*} [CompletePartialOrder A] [CompletePartialOrder B]

/-- **Algebraicity transports along `≃o`.** -/
theorem isAlgebraic_orderIso (e : A ≃o B) [IsAlgebraic A] : IsAlgebraic B where
  directedOn_compactsBelow y := by
    have h := directedOn_orderIso_image e (IsAlgebraic.directedOn_compactsBelow (α := A) (e.symm y))
    rwa [← compactsBelow_orderIso e (e.symm y), e.apply_symm_apply] at h
  isLUB_compactsBelow y := by
    have h := isLUB_orderIso_image e (IsAlgebraic.isLUB_compactsBelow (α := A) (e.symm y))
    rwa [← compactsBelow_orderIso e (e.symm y), e.apply_symm_apply] at h

/-- **`Domain` transports along `≃o`**: algebraicity by `isAlgebraic_orderIso`,
and the countable basis because `K(B)` is the image of `K(A)`. -/
theorem domain_orderIso (e : A ≃o B) [Domain A] : Domain B where
  __ := isAlgebraic_orderIso e
  countable_compacts := by
    rw [compacts_orderIso e]
    exact (Domain.countable_compacts (α := A)).image _

end Transport

/-! ## The representation scheme at a projection

`R(C) = F⁺ ∘ C ∘ F⁻` for a pair `F⁻ : U → V`, `F⁺ : V → U` with
`F⁻ ∘ F⁺ = id` and `F⁺ ∘ F⁻ ⊑ id` — the paper's own recipe, quoted at `+` in
§7.3 and at `(·)♮` in §7.4. Three of the four obligations are already discharged
elsewhere and none of them mentions closures:

| # | Obligation | Discharged by |
| - | ---------- | ------------- |
| 1 | `R(C) = gr ∘ C ∘ fn` as a map | `PowerdomainRep.repOf` |
| 2 | `im(R C) ≅ im C` | `PowerdomainRep.repRangeOrderIso` |
| 3 | `R(C)` is a projection when `C` is | `BifiniteUniversal.isProjection_repOf` |
| 4 | `im(R C)` is a **domain** | nothing — hypothesis `hCfin` below |

Obligation 4 is the whole difference from the closure notion, where the
corresponding subtype `ClosurePoset U` asks only for two equations. -/

section Scheme

open PowerdomainRep ScottHom

variable {U V : Type u} [CompletePartialOrder U] [CompletePartialOrder V]
variable {fn : ScottHom U V} {gr : ScottHom V U}

/-- **`R(C)` is a *finitary* projection when `C` is, given that `im(C)` is a
domain.** This is obligation 4 reduced to a statement about the conjugating
family alone: `isProjection_repOf` supplies the equations, and the `Domain`
travels backwards along `repRangeOrderIso`.

The reduction is what makes the remaining per-operator work nameable. For `→`,
`im(C(p,q)) ≅ im(p) → im(q)`, so the outstanding fact is `Domain (D → E)` for
`D`, `E` the images — which `FunctionSpaceCountable.lean` proves under
`[Domain D] [Domain E] [BoundedComplete E]`, the first two of which
`IsFinitaryProjection` hands over and the third of which is
`boundedComplete_range`. -/
theorem isFinitaryProjection_repOf (hfg : ∀ y, fn (gr y) = y) (hgf : ∀ x, gr (fn x) ≤ x)
    {C : ScottHom V V} (hC : IsProjection C)
    (hdom : @Domain _ (IsProjection.rangeCompletePartialOrder hC)) :
    IsFinitaryProjection (repOf fn gr C) := by
  refine ⟨BifiniteUniversal.isProjection_repOf hfg hgf hC, ?_⟩
  letI : CompletePartialOrder ↥(Set.range ⇑C) := IsProjection.rangeCompletePartialOrder hC
  letI : CompletePartialOrder ↥(Set.range ⇑(repOf fn gr C)) :=
    IsProjection.rangeCompletePartialOrder (BifiniteUniversal.isProjection_repOf hfg hgf hC)
  haveI : Domain ↥(Set.range ⇑C) := hdom
  exact domain_orderIso (PowerdomainRep.repRangeOrderIso hfg C).symm

/-! ### Why r0034's three proofs do not transfer

`Combinator.rep_arrow`, `rep_prod` and `rep_lift` are stated under
`Combinator.Retracts U V`, which is `∃ fn gr, IsClosurePair fn gr` — and
`IsClosurePair fn gr` is `fn ∘ gr = id` together with **`id ⊑ gr ∘ fn`**. The
projection scheme needs the same first equation and the *opposite* second
inequality, `gr ∘ fn ⊑ id`, because that is what makes `gr ∘ C ∘ fn ⊑ id`.

These are not two routes to one hypothesis. Holding both forces
`gr ∘ fn = id` by antisymmetry, and then `fn` and `gr` are mutually inverse order
isomorphisms: `U ≅ V`. At `V = ScottHom U U` that is `U ≅ (U → U)`, at
`V = U × U` it is `U ≅ U × U`, at `V = WithBot U` it is `U ≅ U⊥` — the last of
which is false for every `U` with a compact bottom. So the closure-side
hypothesis is not merely proved differently at the projection notion; outside
the degenerate case where the two carriers are isomorphic, it is a different and
incompatible assumption. -/

/-- **The closure pair and the projection pair coincide only on an isomorphism.**
Antisymmetry, applied pointwise to `id ⊑ gr ∘ fn` and `gr ∘ fn ⊑ id`. -/
theorem gr_fn_eq_of_both (hgf_c : ∀ x, x ≤ gr (fn x)) (hgf_p : ∀ x, gr (fn x) ≤ x) (x : U) :
    gr (fn x) = x :=
  le_antisymm (hgf_p x) (hgf_c x)

/-- **A carrier satisfying both readings of the retraction hypothesis is
isomorphic to the retract.** The order isomorphism whose existence
`gr_fn_eq_of_both` forces — so an operator's conjunct can be proved from
r0034's `Retracts U V` *and* the projection scheme only when `V ≅ U`. -/
def orderIsoOfBothPairs (hfg : ∀ y, fn (gr y) = y)
    (hgf_c : ∀ x, x ≤ gr (fn x)) (hgf_p : ∀ x, gr (fn x) ≤ x) : U ≃o V :=
  Equiv.toOrderIso
    { toFun := ⇑fn, invFun := ⇑gr
      left_inv := gr_fn_eq_of_both hgf_c hgf_p
      right_inv := hfg }
    fn.monotone gr.monotone

/-- **`p ↦ R(C p)` is continuous into `Fp(U)`**, over an arbitrary preordered
index `P`.

This is `Combinator.scottContinuous_repFamily` with `Fp(U)` in place of `Fc(U)`,
and the script is unchanged. That it *is* unchanged is the measurement worth
recording: the closure proof of continuity never inspects the target subtype
beyond its pointwise order, so replacing closures by projections there costs
nothing. The cost is all in `hCfin`, which is what puts the family in `Fp(U)` in
the first place. -/
theorem scottContinuous_repFamilyFp {P : Type*} [Preorder P]
    {C : P → ScottHom V V}
    (hCfin : ∀ p, IsFinitaryProjection (repOf fn gr (C p)))
    (hCmono : ∀ {p q : P}, p ≤ q → C p ≤ C q)
    (hCeval : ∀ {d : Set P}, d.Nonempty → DirectedOn (· ≤ ·) d → ∀ {a : P}, IsLUB d a →
      ∀ y : V, IsLUB ((fun p => C p y) '' d) (C a y)) :
    ScottContinuous (fun p : P => (⟨repOf fn gr (C p), hCfin p⟩ : ↥(Fp U))) := by
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

/-- **The representation scheme at a projection, unary.** -/
theorem isPRepresentable_of_repFamily {F : Cpo.{u} → Cpo.{u}}
    (hfg : ∀ y, fn (gr y) = y)
    {C : ↥(Fp U) → ScottHom V V}
    (hCfin : ∀ p, IsFinitaryProjection (repOf fn gr (C p)))
    (hCmono : ∀ {p q : ↥(Fp U)}, p ≤ q → C p ≤ C q)
    (hCeval : ∀ {d : Set ↥(Fp U)}, d.Nonempty → DirectedOn (· ≤ ·) d →
      ∀ {a : ↥(Fp U)}, IsLUB d a → ∀ y : V, IsLUB ((fun p => C p y) '' d) (C a y))
    (hCiso : ∀ p, Nonempty (↥(Set.range ⇑(C p)) ≃o (F (FpImage p)).carrier)) :
    IsPRepresentable U F :=
  ⟨fun p => ⟨repOf fn gr (C p), hCfin p⟩,
    scottContinuous_repFamilyFp hCfin hCmono hCeval,
    fun p => (hCiso p).map fun e => (PowerdomainRep.repRangeOrderIso hfg (C p)).trans e⟩

/-- **The representation scheme at a projection, binary** — the paper's displayed
`R₊(r, s) = Ψ₊ ∘ (r + s) ∘ Φ₊`, with `(Φ₊, Ψ₊)` abstracted to the pair
`(fn, gr)`. -/
theorem isPRepresentable₂_of_repFamily {F : Cpo.{u} → Cpo.{u} → Cpo.{u}}
    (hfg : ∀ y, fn (gr y) = y)
    {C : ↥(Fp U) × ↥(Fp U) → ScottHom V V}
    (hCfin : ∀ q, IsFinitaryProjection (repOf fn gr (C q)))
    (hCmono : ∀ {q q' : ↥(Fp U) × ↥(Fp U)}, q ≤ q' → C q ≤ C q')
    (hCeval : ∀ {d : Set (↥(Fp U) × ↥(Fp U))}, d.Nonempty → DirectedOn (· ≤ ·) d →
      ∀ {a : ↥(Fp U) × ↥(Fp U)}, IsLUB d a → ∀ y : V, IsLUB ((fun q => C q y) '' d) (C a y))
    (hCiso : ∀ q, Nonempty (↥(Set.range ⇑(C q)) ≃o (F (FpImage q.1) (FpImage q.2)).carrier)) :
    IsPRepresentable₂ U F :=
  ⟨fun q => ⟨repOf fn gr (C q), hCfin q⟩,
    scottContinuous_repFamilyFp hCfin hCmono hCeval,
    fun q => (hCiso q).map fun e => (PowerdomainRep.repRangeOrderIso hfg (C q)).trans e⟩

end Scheme

end ScottDomains.PRep
