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

### The reading above is confirmed — do not re-derive it

The nine-operator list in the table is **settled**, by three independent reads of
the page image, made in two rounds by three agents that did not share a worktree:

| # | Round | Reader | Method | Finding |
| - | ----- | ------ | ------ | ------- |
| 1 | r0036 | agent4 | page 42 at 600 dpi | `→ ⇸ × ⊗ + ⊕ (·)⊥ (·)♯ (·)♭`; corrected the then-current list from seven |
| 2 | r0037 | agent4 | page 42 at 600 dpi, re-read from scratch | the same nine; reported **no correction**, the first stream in three rounds to do so |
| 3 | r0037 | agent3 | pages 41–43 at 200 dpi | the same nine; `PRep.Lemma28` confirmed correct as written |

A fourth read settles the notion rather than the list: r0037's agent5, reading
page 43 for Lemma 30, found that **Lemma 30 spells out "p-representable" where
Lemma 28 says only "representable"**, and that its carrier is printed **V** in
bold. That is independent evidence for the "remainder of this section" argument
above — both lemmas are about `Fp`, and the abbreviation in Lemma 28 is exactly
what §7.3 announced.

So the operator list and the notion are no longer open questions. Re-rendering
the page to check them has zero expected yield; spend the effort on the two
conjuncts that remain. What *did* keep changing across rounds was the derived
prose about these conjuncts — see the `(·)♯`/`(·)♭` section above, and the
staleness note in `ScottDomains.Lemma28AtU` — so a claim about *status* deserves
re-checking against the files in a way that a claim about the printed list no
longer does.

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
| 1 | `→`  | `IsPRepresentable₂ U funOp` | open |
| 2 | `⇸`  | `IsPRepresentable₂ U strictFunOp` | open |
| 3 | `×`  | `IsPRepresentable₂ U prodOp` | **proved** — `rep_prod`, given the pair and `[Domain U]` |
| 4 | `⊗`  | `IsPRepresentable₂ U smashOp` | open |
| 5 | `+`  | `IsPRepresentable₂ U sepSumOp` | open |
| 6 | `⊕`  | `IsPRepresentable₂ U coalSumOp` | open |
| 7 | `(·)⊥` | `IsPRepresentable U liftOp` | **proved** — `rep_lift`, given the pair and `[Domain U]` |
| 8 | `(·)♯` | `IsPRepresentable U smythOp` | open |
| 9 | `(·)♭` | `IsPRepresentable U hoareOp` | open |

Both proved conjuncts are conditional on the paper's own retraction pair for the
operator, exactly as `Combinator.rep_arrow`, `rep_prod` and `rep_lift` are at the
closure notion. At §7.3's `U` the pair is what **Theorem 27** supplies.

**Correction (r0037).** An earlier revision of this paragraph said the pair was
unavailable at `U`, because `Dyadic.thm27` carried the hypothesis
`IsNormallyRepresented ↥(compacts D)` and nothing discharged it. That was true
when it was written and is **false**: `Atomless.isNormallyRepresented_compacts`
discharges the hypothesis for every bounded complete domain, so `Atomless.thm27`
is Theorem 27 with no hypothesis at all — proved in the same round as this file,
by an agent that could not see this one. The instantiation is therefore not
blocked. `ScottDomains.PRepSum` performs it: `PRepSum.pairAtU` transposes
`Atomless.thm27` into the `(fn, gr)` shape used below, and `PRepSum.repProdAtU`
and `PRepSum.repLiftAtU` are conjuncts 3 and 7 over `Dyadic.U` with no
hypothesis. What remains open for `Lemma28AtU` is the other seven conjuncts, and
`PRepSum.lemma28AtU_of` takes exactly those.

No conjunct is stubbed with `sorry`. `lemma28_of` takes each conjunct as a named
hypothesis, so the count nine is checked by the kernel — the anonymous
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
absent because the paper's §7.4 says it cannot be representable over `U`.

**Its universal closure is REFUTED (r0045).**
`ScottDomains.R45.Agent2.not_forall_lemma28 : ¬ ∀ (U : Type) (inst :
CompletePartialOrder U), @Lemma28 U inst` is the kernel-checked refutation, and
`R45.Agent2.not_forall_lemma28_bcd` shows it stays false after adding `[Domain
U]` and `[BoundedComplete U]`, so no instance binder from `Domain.lean` closes
it. `Flat Empty` is the counterexample. The missing content is universality of
`U` (`R45.Agent2.UniversalForBCD`), which is a property of §7.3's carrier and not
a typeclass; `Lemma28AtU`, the instantiation at `Dyadic.U`, is the statement that
is not refuted.

The `def` is kept because eight declarations cite it and because the paper's
sentence — read over §7.3's own `U` — is not the refuted one. The r0046 detector
reads the refutation out of the environment and no longer counts this as an open
claim. -/
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
theorem lemma_28_of {U : Type u} [CompletePartialOrder U]
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

alias lemma28_of := lemma_28_of

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

/-! ### The supremum of a directed family of *finitary* projections

`isLUB_val_image_of_isLUB_fp` above takes finitarity of the pointwise supremum as
a hypothesis. This subsection discharges it over a domain. It is the keystone of
the whole notion change: every conjunct of Lemma 28 needs continuity of its
representing map, continuity needs least upper bounds in `Fp(U)` to be pointwise,
and that needs exactly this.

The proof runs on two observations about a directed family `d` of projections
with pointwise supremum `P`:

1. `im(p) ⊆ im(P)` for each `p ∈ d` (`range_subset_of_le`), and
2. conversely every **compact** point of `im(P)` already lies in some `im(p)` —
   because `k = P k = ⨆_{p ∈ d} p k` is a directed supremum and compactness of
   `k` pushes it below a single `p k`, which `p ⊑ id` then forces to equal `k`.

Together these say `K(im P) = ⋃_{p ∈ d} K(im p)` as subsets of `K(D)`, and each
`K(im p)` is the basis of a domain by finitarity of `p`. Algebraicity of `im(P)`
follows by transporting each computation into one `im(p)` chosen large enough. -/

/-- **A compact point of `im(⨆d)` lies in `im(p)` for some `p ∈ d`.** Compactness
of `k` applied to the directed set `{p k | p ∈ d}`, whose least upper bound is
`P k = k`, produces one `p` with `k ⊑ p k`; `p ⊑ id` supplies the converse. -/
theorem exists_mem_range_of_isCompactElement {d : Set (ScottHom α α)} (hne : d.Nonempty)
    (hd : DirectedOn (· ≤ ·) d) (hp : ∀ p ∈ d, IsProjection p)
    {k : α} (hk : IsCompactElement k) (hkP : k ∈ Set.range ⇑(sSup d)) :
    ∃ p ∈ d, k ∈ Set.range ⇑p := by
  have hsup : ∀ x : α, IsLUB ((fun f : ScottHom α α => f x) '' d) ((sSup d) x) := fun x => by
    rw [ScottHom.coe_sSup_of_directed hd x]
    exact (ScottHom.directedOn_eval_image hd x).isLUB_sSup
  have hPk : (sSup d) k = k := (isProjection_sSup hd hp).apply_of_mem_range hkP
  obtain ⟨_, ⟨p, hpd, rfl⟩, hkz⟩ :=
    hk ((fun f : ScottHom α α => f k) '' d) ((sSup d) k) (hne.image _)
      (ScottHom.directedOn_eval_image hd k) (hsup k) (le_of_eq hPk.symm)
  exact ⟨p, hpd, ⟨k, le_antisymm ((hp p hpd).le k) hkz⟩⟩

/-- **The pointwise supremum of a nonempty directed set of finitary projections on
a domain is a finitary projection.**

`isProjection_sSup` gives the equations. For the `Domain` on `im(P)`:

* *directedness of the compact approximants* — two compacts below `x ∈ im(P)`
  land in `im(p₁)` and `im(p₂)` by `exists_mem_range_of_isCompactElement`, hence
  both in `im(p₃)` for a `p₃ ∈ d` above the pair; `im(p₃)` is algebraic, so its
  compacts below `p₃ x` are directed, and the bound it returns is compact in `D`
  (Lemma 5) and below `x` because `p₃ ⊑ id`;
* *`x` is the supremum of its compact approximants* — `x = ⨆_{p ∈ d} p x`, and
  each `p x` is the supremum in `im(p)` of *its* compacts, all of which are
  compact approximants of `x` in `im(P)`;
* *countability* — `countable_compacts_range`.

`IsProjection.isCompactElement_iff` (Lemma 5's first sentence, which needs only
that the map is a projection) is what lets compactness be moved between `D`,
`im(p)` and `im(P)` at every step. -/
theorem isFinitaryProjection_sSup [Domain α] {d : Set (ScottHom α α)} (hne : d.Nonempty)
    (hd : DirectedOn (· ≤ ·) d) (hfp : ∀ p ∈ d, IsFinitaryProjection p) :
    IsFinitaryProjection (sSup d) := by
  have hp : ∀ p ∈ d, IsProjection p := fun p hpd => (hfp p hpd).isProjection
  have hP : IsProjection (sSup d) := isProjection_sSup hd hp
  have hsup : ∀ x : α, IsLUB ((fun f : ScottHom α α => f x) '' d) ((sSup d) x) := fun x => by
    rw [ScottHom.coe_sSup_of_directed hd x]
    exact (ScottHom.directedOn_eval_image hd x).isLUB_sSup
  have hle : ∀ p ∈ d, p ≤ sSup d := fun p hpd x => (hsup x).1 ⟨p, hpd, rfl⟩
  -- Every point of `im(p)` is a point of `im(⨆d)`.
  have hrange : ∀ p ∈ d, Set.range ⇑p ⊆ Set.range ⇑(sSup d) := fun p hpd =>
    range_subset_of_le (hp p hpd) hP (hle p hpd)
  letI : CompletePartialOrder ↥(Set.range ⇑(sSup d)) := hP.rangeCompletePartialOrder
  -- A point of `α` compact, in `im(p)` and below `x` gives a compact approximant of `x`.
  have hmk : ∀ (x : ↥(Set.range ⇑(sSup d))) (c : α) (hcr : c ∈ Set.range ⇑(sSup d)),
      IsCompactElement c → c ≤ x.val →
      (⟨c, hcr⟩ : ↥(Set.range ⇑(sSup d))) ∈ compactsBelow x :=
    fun _ _ _ hc hcx => ⟨hP.isCompactElement_iff.mpr hc, hcx⟩
  refine ⟨hP, ?_⟩
  refine { toIsAlgebraic := ⟨?_, ?_⟩, countable_compacts := countable_compacts_range hP }
  · -- directedness of `compactsBelow x` in `im(⨆d)`
    intro x k₁ hk₁ k₂ hk₂
    have hc₁ : IsCompactElement k₁.val := hP.isCompactElement_iff.mp hk₁.1
    have hc₂ : IsCompactElement k₂.val := hP.isCompactElement_iff.mp hk₂.1
    obtain ⟨p₁, hp₁d, hm₁⟩ := exists_mem_range_of_isCompactElement hne hd hp hc₁ k₁.2
    obtain ⟨p₂, hp₂d, hm₂⟩ := exists_mem_range_of_isCompactElement hne hd hp hc₂ k₂.2
    obtain ⟨p, hpd, h₁p, h₂p⟩ := hd p₁ hp₁d p₂ hp₂d
    have hpp : IsProjection p := hp p hpd
    have hin₁ : k₁.val ∈ Set.range ⇑p := range_subset_of_le (hp p₁ hp₁d) hpp h₁p hm₁
    have hin₂ : k₂.val ∈ Set.range ⇑p := range_subset_of_le (hp p₂ hp₂d) hpp h₂p hm₂
    letI : CompletePartialOrder ↥(Set.range ⇑p) := hpp.rangeCompletePartialOrder
    haveI : Domain ↥(Set.range ⇑p) := (hfp p hpd).domain
    set X : ↥(Set.range ⇑p) := ⟨p x.val, Set.mem_range_self _⟩ with hX
    have hK₁ : (⟨k₁.val, hin₁⟩ : ↥(Set.range ⇑p)) ∈ compactsBelow X :=
      ⟨hpp.isCompactElement_iff.mpr hc₁,
        show k₁.val ≤ p x.val from
          (hpp.apply_of_mem_range hin₁).symm.trans_le (p.monotone hk₁.2)⟩
    have hK₂ : (⟨k₂.val, hin₂⟩ : ↥(Set.range ⇑p)) ∈ compactsBelow X :=
      ⟨hpp.isCompactElement_iff.mpr hc₂,
        show k₂.val ≤ p x.val from
          (hpp.apply_of_mem_range hin₂).symm.trans_le (p.monotone hk₂.2)⟩
    obtain ⟨K, ⟨hKc, hKX⟩, hK₁K, hK₂K⟩ :=
      IsAlgebraic.directedOn_compactsBelow X _ hK₁ _ hK₂
    have hKcα : IsCompactElement K.val := hpp.isCompactElement_iff.mp hKc
    have hKr : K.val ∈ Set.range ⇑(sSup d) := hrange p hpd K.2
    refine ⟨⟨K.val, hKr⟩, hmk x K.val hKr hKcα ((show K.val ≤ p x.val from hKX).trans (hpp.le _)),
      hK₁K, hK₂K⟩
  · -- `x` is the least upper bound of its compact approximants in `im(⨆d)`
    intro x
    refine ⟨fun k hk => hk.2, ?_⟩
    intro u hu
    show x.val ≤ u.val
    have hfix : (sSup d) x.val = x.val := hP.apply_of_mem_range x.2
    refine (le_of_eq hfix.symm).trans ((hsup x.val).2 ?_)
    rintro _ ⟨p, hpd, rfl⟩
    have hpp : IsProjection p := hp p hpd
    letI : CompletePartialOrder ↥(Set.range ⇑p) := hpp.rangeCompletePartialOrder
    haveI : Domain ↥(Set.range ⇑p) := (hfp p hpd).domain
    set Y : ↥(Set.range ⇑p) := ⟨p x.val, Set.mem_range_self _⟩ with hY
    have hYlub : IsLUB (Subtype.val '' compactsBelow Y) (p x.val) :=
      hpp.isLUB_val_image (IsAlgebraic.isLUB_compactsBelow Y)
    refine hYlub.2 ?_
    rintro _ ⟨K, hK, rfl⟩
    have hKcα : IsCompactElement K.val := hpp.isCompactElement_iff.mp hK.1
    have hKr : K.val ∈ Set.range ⇑(sSup d) := hrange p hpd K.2
    have hKx : K.val ≤ x.val := (show K.val ≤ p x.val from hK.2).trans (hpp.le _)
    exact hu (hmk x K.val hKr hKcα hKx)

/-- **Least upper bounds in `Fp(D)` are pointwise, over a domain.**
`isLUB_val_image_of_isLUB_fp` with its hypothesis discharged by
`isFinitaryProjection_sSup`. This is the form the per-operator continuity proofs
consume, and the projection counterpart of `isLUB_val_image_of_isLUB`. -/
theorem isLUB_val_image_of_isLUB_fp' [Domain α] {d : Set ↥(Fp α)} (hne : d.Nonempty)
    (hd : DirectedOn (· ≤ ·) d) {a : ↥(Fp α)} (ha : IsLUB d a) :
    IsLUB ((fun q : ↥(Fp α) => q.val) '' d) a.val :=
  isLUB_val_image_of_isLUB_fp hd
    (isFinitaryProjection_sSup (hne.image _)
      (by
        rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩
        obtain ⟨c, hc, h₁, h₂⟩ := hd p hp q hq
        exact ⟨c.val, ⟨c, hc, rfl⟩, h₁, h₂⟩)
      (by rintro _ ⟨p, _, rfl⟩; exact mem_Fp.mp p.2))
    ha

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

/-! ## Conjunct 7: `(·)⊥` is p-representable

r0034's `Combinator.rep_lift` proves this at the *closure* notion. Re-proved here
at the projection notion, and the measurement of what transferred is:

| # | Ingredient | r0034 version | Here |
| - | ---------- | ------------- | ---- |
| 1 | conjugating family `r⊥` | `Combinator.liftMap` | reused unchanged |
| 2 | its Scott continuity | `Combinator.scottContinuous_liftFun` | reused unchanged |
| 3 | monotonicity in `r` | `Combinator.liftMap_mono` | reused unchanged |
| 4 | the two equations on `r⊥` | `isClosure_liftMap` | **re-proved** as `isProjection_liftMap`; the inequality reverses |
| 5 | `im(r⊥) ≅ (im r)⊥` | `liftRangeOrderIso`, indexed by `Fc(U)` | **re-derived** at a bare `ScottHom`, since the index type changes |
| 6 | `im(R(r⊥))` a domain | not required | **new** — `domain_range_liftMap` |
| 7 | the index least upper bound | `isLUB_val_image_of_isLUB` | `isLUB_val_image_of_isLUB_fp'`, which costs `isFinitaryProjection_sSup` |
| 8 | the pair hypothesis | `Retracts U (WithBot U)`, i.e. `id ⊑ gr ∘ fn` | **incompatible** — `gr ∘ fn ⊑ id` here, and `gr_fn_eq_of_both` shows holding both forces `U ≅ U⊥` |

So rows 1–3 transfer verbatim, rows 4, 5 and 7 are re-proved, row 6 is new work
the closure notion never had, and row 8 is a different hypothesis. "The proof
transfers" is false; "the construction transfers, the proof obligations do not"
is the measurement. -/

section LiftConjunct

open ScottHom

variable {U : Type u} [CompletePartialOrder U]

/-- `r⊥` is a projection whenever `r` is. Both laws hold on the coercions by the
corresponding law for `r` and trivially at the adjoined bottom. The companion of
`Combinator.isClosure_liftMap`, with `r x ⊑ x` in place of `x ⊑ r x`. -/
theorem isProjection_liftMap {r : ScottHom U U} (hr : IsProjection r) :
    IsProjection (Combinator.liftMap r) := by
  constructor
  · intro z
    induction z using WithBot.recBotCoe with
    | bot => rfl
    | coe a => simp [hr.idem]
  · intro z
    induction z using WithBot.recBotCoe with
    | bot => exact le_rfl
    | coe a => simpa using WithBot.coe_le_coe.mpr (hr.le a)

/-! ### `im(r⊥) ≅ (im r)⊥` at a bare `ScottHom`

`Combinator`'s version of this isomorphism is indexed by `ClosurePoset U`, so it
cannot be applied at an element of `Fp(U)`. The four lemmas are re-derived here
against `r : ScottHom U U`, which is all any of them ever used. -/

theorem liftRange_mem (r : ScottHom U U) (z : WithBot ↥(Set.range ⇑r)) :
    WithBot.map Subtype.val z ∈ Set.range ⇑(Combinator.liftMap r) := by
  induction z using WithBot.recBotCoe with
  | bot => exact ⟨⊥, rfl⟩
  | coe a =>
    obtain ⟨x, hx⟩ := a.2
    exact ⟨(↑x : WithBot U), by simp [hx]⟩

/-- The direction of `im(r⊥) ≅ (im r)⊥` carrying no proof obligation in its data. -/
noncomputable def liftRangeMap (r : ScottHom U U) (z : WithBot ↥(Set.range ⇑r)) :
    ↥(Set.range ⇑(Combinator.liftMap r)) :=
  ⟨WithBot.map Subtype.val z, liftRange_mem r z⟩

theorem liftRangeMap_le_iff (r : ScottHom U U) (z w : WithBot ↥(Set.range ⇑r)) :
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

theorem liftRangeMap_surjective (r : ScottHom U U) :
    Function.Surjective (liftRangeMap r) := by
  rintro ⟨z, w, rfl⟩
  induction w using WithBot.recBotCoe with
  | bot => exact ⟨⊥, rfl⟩
  | coe x =>
    refine ⟨(↑(⟨r x, Set.mem_range_self x⟩ : ↥(Set.range ⇑r)) : WithBot _), ?_⟩
    exact Subtype.ext rfl

/-- **`im(r⊥) ≅ (im r)⊥`**, for any continuous `r`. -/
noncomputable def liftRangeOrderIso (r : ScottHom U U) :
    ↥(Set.range ⇑(Combinator.liftMap r)) ≃o WithBot ↥(Set.range ⇑r) :=
  (RelIso.ofSurjective (OrderEmbedding.ofMapLEIff (liftRangeMap r) (liftRangeMap_le_iff r))
    (liftRangeMap_surjective r)).symm

/-- **`im(r⊥)` is a domain when `im(r)` is** — the obligation `Fp` adds and `Fc`
does not. Through `liftRangeOrderIso` it reduces to `Domain (D⊥)` for `D` a
domain, which is `ClosureProperties.liftDomain`. -/
theorem domain_range_liftMap {r : ScottHom U U} (hr : IsProjection r)
    (hdr : @Domain _ (IsProjection.rangeCompletePartialOrder hr)) :
    @Domain _ (IsProjection.rangeCompletePartialOrder (isProjection_liftMap hr)) := by
  letI : CompletePartialOrder ↥(Set.range ⇑r) := IsProjection.rangeCompletePartialOrder hr
  haveI : Domain ↥(Set.range ⇑r) := hdr
  letI : CompletePartialOrder (WithBot ↥(Set.range ⇑r)) := liftCpo
  haveI : Domain (WithBot ↥(Set.range ⇑r)) := ClosureProperties.liftDomain
  letI : CompletePartialOrder ↥(Set.range ⇑(Combinator.liftMap r)) :=
    IsProjection.rangeCompletePartialOrder (isProjection_liftMap hr)
  exact domain_orderIso (liftRangeOrderIso r).symm

/-! ### The family, indexed by `Fp(U)` -/

/-- The conjugating family for `(·)⊥`, indexed by `Fp(U)` rather than `Fc(U)`. -/
noncomputable def liftFamily (p : ↥(Fp U)) : ScottHom (WithBot U) (WithBot U) :=
  Combinator.liftMap p.val

theorem isProjection_liftFamily (p : ↥(Fp U)) : IsProjection (liftFamily p) :=
  isProjection_liftMap (mem_Fp.mp p.2).isProjection

theorem liftFamily_mono {p q : ↥(Fp U)} (h : p ≤ q) : liftFamily p ≤ liftFamily q :=
  Combinator.liftMap_mono h

/-- Pointwise Scott continuity of the family in its `Fp(U)` index. This is where
`isFinitaryProjection_sSup` is spent: the closure version of this lemma calls
`isLUB_val_image_of_isLUB`, which is free, and the projection version calls
`isLUB_val_image_of_isLUB_fp'`, which is not. -/
theorem isLUB_liftFamily [Domain U] {d : Set ↥(Fp U)} (hne : d.Nonempty)
    (hd : DirectedOn (· ≤ ·) d) {a : ↥(Fp U)} (ha : IsLUB d a) (y : WithBot U) :
    IsLUB ((fun p => liftFamily p y) '' d) (liftFamily a y) := by
  induction y using WithBot.recBotCoe with
  | bot =>
    refine ⟨?_, fun u _ => ?_⟩
    · rintro _ ⟨r, _, rfl⟩
      exact le_rfl
    · exact bot_le
  | coe x =>
    have hdv : DirectedOn (· ≤ ·) ((fun c : ↥(Fp U) => c.val) '' d) := by
      rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩
      obtain ⟨c, hc, hpc, hqc⟩ := hd p hp q hq
      exact ⟨c.val, ⟨c, hc, rfl⟩, hpc, hqc⟩
    have hval := isLUB_val_image_of_isLUB_fp' hne hd ha
    have heval := ScottHom.isLUB_eval_image_of_isLUB hdv hval x
    rw [Set.image_image] at heval
    have hcoe := Combinator.isLUB_coe_image (S := (fun c : ↥(Fp U) => c.val x) '' d)
      (hne.image _) heval
    rw [Set.image_image] at hcoe
    exact hcoe

/-- **`(·)⊥` is p-representable over any domain that retracts onto its own lift**
— conjunct 7 of Lemma 28, at the notion §7.3 actually uses.

The hypothesis is the paper's own pair, `Φ⊥ ∘ Ψ⊥ = id` and `Ψ⊥ ∘ Φ⊥ ⊑ id`, and
the second inequality points the *opposite* way from `Combinator.Retracts`, which
is what `rep_lift` assumes. At §7.3's `U` the pair is what Theorem 27 supplies —
unconditionally, via `Atomless.thm27` — so `PRepSum.repLiftAtU` is this theorem
with the hypothesis discharged. -/
theorem rep_lift [Domain U] {fn : ScottHom U (WithBot U)} {gr : ScottHom (WithBot U) U}
    (hfg : ∀ y, fn (gr y) = y) (hgf : ∀ x, gr (fn x) ≤ x) :
    IsPRepresentable U liftOp :=
  isPRepresentable_of_repFamily hfg
    (fun p => isFinitaryProjection_repOf hfg hgf (isProjection_liftFamily p)
      (domain_range_liftMap (mem_Fp.mp p.2).isProjection (mem_Fp.mp p.2).domain))
    liftFamily_mono isLUB_liftFamily
    fun p => ⟨liftRangeOrderIso p.val⟩

end LiftConjunct

/-! ## Conjunct 3: `×` is p-representable

Cheaper than `(·)⊥` at the projection notion, because
`PowerdomainRep.prodRangeOrderIso` is already stated at a bare `ScottHom` pair —
it needs no property of `r` and `s` at all, the range of `r × s` being the
rectangle `im(r) × im(s)` — so nothing has to be re-derived for the change of
index. What is re-proved is the same three items as for the lift: the two
equations (`isProjection_prodMap`), the `Domain` on the image
(`domain_range_prodMap`, new to `Fp`), and the index least upper bound
(`isLUB_prodFamily`, which spends `isFinitaryProjection_sSup`). -/

section ProdConjunct

open ScottHom PowerdomainRep

variable {U : Type u} [CompletePartialOrder U]

/-- `r × s` is a projection when `r` and `s` are: both laws hold coordinatewise,
exactly as for closures with the inequality reversed. -/
theorem isProjection_prodMap {r s : ScottHom U U} (hr : IsProjection r) (hs : IsProjection s) :
    IsProjection (prodMap r s) := by
  refine ⟨fun p => ?_, fun p => ⟨hr.le p.1, hs.le p.2⟩⟩
  show (r (r p.1), s (s p.2)) = (r p.1, s p.2)
  rw [hr.idem, hs.idem]

/-- **`im(r × s)` is a domain when `im(r)` and `im(s)` are.** Through
`prodRangeOrderIso` this is `PowerdomainRep.domain_prod`. -/
theorem domain_range_prodMap {r s : ScottHom U U} (hr : IsProjection r) (hs : IsProjection s)
    (hdr : @Domain _ (IsProjection.rangeCompletePartialOrder hr))
    (hds : @Domain _ (IsProjection.rangeCompletePartialOrder hs)) :
    @Domain _ (IsProjection.rangeCompletePartialOrder (isProjection_prodMap hr hs)) := by
  letI : CompletePartialOrder ↥(Set.range ⇑r) := IsProjection.rangeCompletePartialOrder hr
  letI : CompletePartialOrder ↥(Set.range ⇑s) := IsProjection.rangeCompletePartialOrder hs
  haveI : Domain ↥(Set.range ⇑r) := hdr
  haveI : Domain ↥(Set.range ⇑s) := hds
  haveI : Domain (↥(Set.range ⇑r) × ↥(Set.range ⇑s)) := domain_prod
  letI : CompletePartialOrder ↥(Set.range ⇑(prodMap r s)) :=
    IsProjection.rangeCompletePartialOrder (isProjection_prodMap hr hs)
  exact domain_orderIso (prodRangeOrderIso r s).symm

/-- The conjugating family for `×`, indexed by `Fp(U) × Fp(U)`. -/
def prodFamily (q : ↥(Fp U) × ↥(Fp U)) : ScottHom (U × U) (U × U) :=
  prodMap q.1.val q.2.val

theorem isProjection_prodFamily (q : ↥(Fp U) × ↥(Fp U)) : IsProjection (prodFamily q) :=
  isProjection_prodMap (mem_Fp.mp q.1.2).isProjection (mem_Fp.mp q.2.2).isProjection

theorem prodFamily_mono {q q' : ↥(Fp U) × ↥(Fp U)} (h : q ≤ q') :
    prodFamily q ≤ prodFamily q' := prodMap_mono h.1 h.2

/-- The `Fp` counterpart of `isLUB_prodMap_of_isLUB`. `isLUB_prod` splits the
goal into two independent coordinates; each is then
`isLUB_val_image_of_isLUB_fp'` followed by `ScottHom.isLUB_eval_image_of_isLUB`. -/
theorem isLUB_prodFamily [Domain U] {d : Set (↥(Fp U) × ↥(Fp U))}
    (hne : d.Nonempty) (hd : DirectedOn (· ≤ ·) d) {a : ↥(Fp U) × ↥(Fp U)}
    (ha : IsLUB d a) (y : U × U) :
    IsLUB ((fun q => prodFamily q y) '' d) (prodFamily a y) := by
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
  refine isLUB_prod.mpr ⟨?_, ?_⟩
  · have := ScottHom.isLUB_eval_image_of_isLUB hd₁ h₁ y.1
    rw [Set.image_image] at this
    simpa [prodFamily, Set.image_image] using this
  · have := ScottHom.isLUB_eval_image_of_isLUB hd₂ h₂ y.2
    rw [Set.image_image] at this
    simpa [prodFamily, Set.image_image] using this

/-- **`×` is p-representable over any domain that retracts onto its own square** —
conjunct 3 of Lemma 28, at the notion §7.3 uses.

`Combinator.rep_prod` is the same statement at the closure notion, under
`Retracts U (U × U)`; the pair hypothesis here points the other way, and
`gr_fn_eq_of_both` shows the two are simultaneously satisfiable only when
`U ≅ U × U`. -/
theorem rep_prod [Domain U] {fn : ScottHom U (U × U)} {gr : ScottHom (U × U) U}
    (hfg : ∀ y, fn (gr y) = y) (hgf : ∀ x, gr (fn x) ≤ x) :
    IsPRepresentable₂ U prodOp :=
  isPRepresentable₂_of_repFamily hfg
    (fun q => isFinitaryProjection_repOf hfg hgf (isProjection_prodFamily q)
      (domain_range_prodMap _ _ (mem_Fp.mp q.1.2).domain (mem_Fp.mp q.2.2).domain))
    prodFamily_mono isLUB_prodFamily
    fun q => ⟨prodRangeOrderIso q.1.val q.2.val⟩

end ProdConjunct

end ScottDomains.PRep
