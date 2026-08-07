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

end ScottDomains.PRep
