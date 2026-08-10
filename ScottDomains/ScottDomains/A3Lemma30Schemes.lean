import ScottDomains.A3Thm29
import ScottDomains.A4PowerdomainRep

/-!
# r0046, agent3: Lemma 30's missing representation schemes

r0045's agent3 measured `LemThirty.Lemma30AtV` as short **three `PRep` schemes** —
`(·)♯`, `(·)♭` and `(·)♮` — and routed them to another stream. Measured again on
this branch, after r0045 merged:

| # | Conjunct | Retraction pair over `V` | `PRep` scheme | Where the scheme is |
| -- | -------- | ------------------------ | ------------- | ------------------- |
| 8 | `(·)♯` | `LemThirty.retracts_smyth` | **exists** | `R45.Agent4.rep_smyth` |
| 9 | `(·)♭` | `LemThirty.retracts_hoare` | **exists** | `R45.Agent4.rep_hoare` |
| 10 | `(·)♮` | `LemThirty.retracts_plotkin` | **absent** | built here |

So **the count was three when the r0045 report was written and one when this round
opened**: r0045's agent4 discharged `SmythImageIso`, `SmythFamilyLUB`,
`HoareImageIso` and `HoareFamilyLUB` in the same round, which turned
`PowerdomainMap.Rep.rep_smyth_of` and `rep_hoare_of` into two-hypothesis theorems
taking only the retraction pair. The two streams did not read each other; this
module is the composition check.

## The one that was genuinely missing, and why it was cheap

`(·)♮` had **no** representation-side declaration anywhere in the tree — grep for
`plotkinFamily`, `PlotkinImageIso`, `PlotkinFamilyLUB`, `rep_plotkin` returned
zero hits. What it *did* have is the whole functor half:
`PowerdomainMap.plotkin`, `plotkin_id`, `plotkin_comp`, `scottContinuous_plotkin`,
`isProjection_plotkin` and `foldMono_plotkin`, at exact parity with the nine Smyth
and nine Hoare declarations of `PowerdomainMap.lean`.

That is the whole reason this module is short. r0045's agent4 wrote its two
engines generically:

* `nonempty_orderIso_range_of_section` is pure order theory — a monotone
  section-retraction pair, no powerdomain in the statement.
* `isLUB_mapFamily` is generic in the pre-order `A` presenting `Pf(K(U))`, with
  the ordering entering through the single argument `hmono`.

`Plotkin.FinCompacts U` satisfies every binder of the second — `Preorder`
(`Powerdomain/Plotkin.lean:146`), `OrderBot` (`:223`), and
`ContinuousAlgebra.instFinSetsPlotkin` — and `foldMono_plotkin` is the `hmono` it
asks for. So `plotkinFamilyLUB` is one line and `plotkinImageIso` is
`smythImageIso` with `plotkin` for `smyth`. **No Egli–Milner-specific reasoning
appears below**; it was all spent inside `foldMono_plotkin`, which is r0041's.

## `(·)♮` over `V`, not over `U` — the paper says so

§7.4's opening sentence, quoted at `LemThirty.lean:166`: "The convex powerdomain
`(·)♮` cannot be representable over `U` because it does not preserve bounded
completeness." That is why `(·)♮` is Lemma 30's tenth conjunct and not one of
Lemma 28's nine, and it is why there is no `repPlotkinAtU` here to match
`Rep.repSmythAtU`. `Flat.not_boundedComplete_plotkin_TT` is the development's
kernel-checked witness for the paper's sentence, and
`Powerdomain/BoundedComplete.lean` correspondingly proves Lemma 13 for `(·)♯` and
`(·)♭` and not for `(·)♮`.

Over `V` the retraction pair is `LemThirty.retracts_plotkin`, which takes
`Thm29SecondAtDomains` — open, and implied by `Thm29Normal`.

## What this leaves

`lemma30AtV_of_thm29Normal_of_arrows` proves `Lemma30AtV` from `Thm29Normal`
together with conjuncts 1 and 2 — arity 3, against `LemThirty.lemma30_of`'s arity
10. Eight of the ten conjuncts now follow from `Thm29Normal` alone
(`eight_conjuncts_of_thm29Normal`); r0045 had five.

The two that do not are `→` and `⇸`, and they are blocked for a reason this
development has already measured rather than for a missing scheme:
`R45.Agent3.not_boundedComplete_V` proves `Thm29SecondAtDomains → ¬ BoundedComplete
V`, while `PRepFun.rep_arrow` and `PRepFun.rep_strictArrow` — the only routes to
those two conjuncts here — both carry `[BoundedComplete U]`. So conjuncts 1 and 2
are unreachable *in this development* for as long as Theorem 29's second sentence
is assumed, and that is a defect of the route to `Domain (D → E)`, not of
Lemma 30.
-/

namespace ScottDomains.R46.Agent3

open ScottDomains ScottDomains.BifiniteUniversal ScottDomains.PRep
open ScottDomains.PowerdomainMap ScottDomains.PowerdomainMap.Rep
open ScottDomains.Colimit ScottDomains.LemThirty
open ScottHom

universe u

/-! ## 1. The conjugating family for `(·)♮`

Token-for-token `PowerdomainMap.Rep.smythFamily` and its three companions, with
`plotkin` for `smyth`. Stated here rather than in `PowerdomainMapRep.lean` because
the operator `plotkinOp` lives in `LemThirty`, which that file does not import. -/

section Family

variable {U : Type u} [CompletePartialOrder U] [Domain U]

/-- The conjugating family for `(·)♮`: `p ↦ p♮`, the action of `p` on the convex
powerdomain. -/
noncomputable def plotkinFamily (p : ↥(Fp U)) :
    ScottHom (Plotkin.Powerdomain U) (Plotkin.Powerdomain U) :=
  ⟨PowerdomainMap.plotkin ⇑p.val,
    PowerdomainMap.scottContinuous_plotkin p.val.scottContinuous⟩

@[simp] theorem plotkinFamily_apply (p : ↥(Fp U)) (I : Plotkin.Powerdomain U) :
    plotkinFamily p I = PowerdomainMap.plotkin ⇑p.val I := rfl

/-- **`p♮` is a projection when `p` is** — from the two functor laws. -/
theorem isProjection_plotkinFamily (p : ↥(Fp U)) : IsProjection (plotkinFamily p) :=
  PowerdomainMap.isProjection_plotkin p.val.scottContinuous
    (mem_Fp.mp p.2).isProjection.idem (mem_Fp.mp p.2).isProjection.le

/-- **The family is monotone in its `Fp(U)` index** — `map_le_map`. -/
theorem plotkinFamily_mono {p q : ↥(Fp U)} (h : p ≤ q) :
    plotkinFamily p ≤ plotkinFamily q :=
  fun I => PowerdomainMap.map_le_map (fun x => h x)
    (PowerdomainMap.foldMono_plotkin p.val.scottContinuous)
    (PowerdomainMap.foldMono_plotkin q.val.scottContinuous) I

/-! ## 2. The two obligations, discharged rather than stated

`PowerdomainMapRep.lean` records the Smyth and Hoare versions of these as
`def … : Prop` because at the time nothing proved them. Both are theorems now
(`R45.Agent4.smythImageIso` and friends), so the Plotkin versions are stated
directly as theorems — no new proposition is added to the project's list of
claims. -/

/-- **`im(p♮) ≅ (im p)♮`** for every finitary projection `p`, with no hypotheses
beyond the instance binders.

`R45.Agent4.smythImageIso` with `plotkin_comp` / `plotkin_id` /
`scottContinuous_plotkin` substituted. The content is
`R45.Agent4.nonempty_orderIso_range_of_section`, which mentions no powerdomain:
the corestriction `x ↦ p x` and the inclusion form a monotone section-retraction
pair, the functor laws carry that to `(·)♮`, and `im(p♮) = im(ι♮)` follows. -/
theorem plotkinImageIso (p : ↥(Fp U)) :
    Nonempty (↥(Set.range ⇑(plotkinFamily p)) ≃o (plotkinOp (FpImage p)).carrier) := by
  have hfp : IsFinitaryProjection p.val := mem_Fp.mp p.2
  have hproj : IsProjection p.val := hfp.isProjection
  letI : CompletePartialOrder ↥(Set.range ⇑p.val) :=
    IsProjection.rangeCompletePartialOrder hproj
  haveI : Domain ↥(Set.range ⇑p.val) := hfp.domain
  have hci : ScottContinuous (Subtype.val : ↥(Set.range ⇑p.val) → U) :=
    PRepFun.scottContinuous_val hproj
  have hcr : ScottContinuous
      (fun x : U => (⟨p.val x, Set.mem_range_self x⟩ : ↥(Set.range ⇑p.val))) :=
    PRepFun.scottContinuous_corestrict p.val
  have hri : ∀ x : ↥(Set.range ⇑p.val),
      (⟨p.val (Subtype.val x), Set.mem_range_self _⟩ : ↥(Set.range ⇑p.val)) = x :=
    fun x => Subtype.ext (hproj.apply_of_mem_range x.2)
  have hsec := PowerdomainMap.plotkin_comp hci hcr
  rw [show (fun x : U => (⟨p.val x, Set.mem_range_self x⟩ : ↥(Set.range ⇑p.val)))
        ∘ (Subtype.val : ↥(Set.range ⇑p.val) → U) = id from funext hri,
    PowerdomainMap.plotkin_id] at hsec
  have hcomp := PowerdomainMap.plotkin_comp hcr hci
  exact R45.Agent4.nonempty_orderIso_range_of_section
    (PowerdomainMap.scottContinuous_plotkin hci).monotone
    (PowerdomainMap.scottContinuous_plotkin hcr).monotone
    (fun X => congrFun hsec.symm X) (fun y => congrFun hcomp y)

/-- **`p ↦ p♮` preserves directed suprema of `Fp(U)`, pointwise.**

One line: `R45.Agent4.isLUB_mapFamily` is already generic in the pre-order
presenting `Pf(K(U))`, and its single ordering-specific input is `hmono`, which
`PowerdomainMap.foldMono_plotkin` supplies. `Plotkin.FinCompacts U` meets the
three binders — `Preorder`, `OrderBot`, `FinSets ↥(compacts U)`. -/
theorem plotkinFamilyLUB {d : Set ↥(Fp U)} (hne : d.Nonempty)
    (hd : DirectedOn (· ≤ ·) d) {a : ↥(Fp U)} (ha : IsLUB d a)
    (y : Plotkin.Powerdomain U) :
    IsLUB ((fun p => plotkinFamily p y) '' d) (plotkinFamily a y) :=
  R45.Agent4.isLUB_mapFamily (A := Plotkin.FinCompacts U)
    (fun p => PowerdomainMap.foldMono_plotkin p.val.scottContinuous) hne hd ha y

/-- `im(p♮)` is a domain: `Domain ((im p)♮)` is Theorem 11 at the domain `im p`
(`LemThirty.domain_plotkinOp`), transported along `plotkinImageIso`. -/
theorem domain_range_plotkinFamily (p : ↥(Fp U)) :
    @Domain _ (IsProjection.rangeCompletePartialOrder (isProjection_plotkinFamily p)) := by
  haveI : Domain (FpImage p).carrier := (mem_Fp.mp p.2).domain
  haveI : Domain (plotkinOp (FpImage p)).carrier := LemThirty.domain_plotkinOp (FpImage p)
  letI : CompletePartialOrder ↥(Set.range ⇑(plotkinFamily p)) :=
    IsProjection.rangeCompletePartialOrder (isProjection_plotkinFamily p)
  exact domain_orderIso (plotkinImageIso p).some.symm

/-- **`(·)♮` is p-representable over any `U` admitting the retraction pair** —
Lemma 30's tenth scheme, the one the development did not have.

Arity 2, matching `R45.Agent4.rep_smyth` and `rep_hoare`: only the pair is a
hypothesis, both obligations being theorems above. -/
theorem rep_plotkin {fn : ScottHom U (Plotkin.Powerdomain U)}
    {gr : ScottHom (Plotkin.Powerdomain U) U}
    (hfg : ∀ y, fn (gr y) = y) (hgf : ∀ x, gr (fn x) ≤ x) :
    IsPRepresentable U plotkinOp :=
  isPRepresentable_of_repFamily hfg
    (fun p => isFinitaryProjection_repOf hfg hgf (isProjection_plotkinFamily p)
      (domain_range_plotkinFamily p))
    plotkinFamily_mono plotkinFamilyLUB plotkinImageIso

end Family

/-! ## 3. The three powerdomain conjuncts at `V` -/

/-- **Conjunct 8 of Lemma 30: `(·)♯` is p-representable over `V`.**
`R45.Agent4.rep_smyth` at `U := V`, with `LemThirty.retracts_smyth`'s pair. -/
theorem repSmythAtV (h : Thm29SecondAtDomains) : IsPRepresentable V PRep.smythOp := by
  obtain ⟨_gr, _fn, hfg, hgf⟩ := LemThirty.retracts_smyth h
  exact R45.Agent4.rep_smyth hfg hgf

/-- **Conjunct 9 of Lemma 30: `(·)♭` is p-representable over `V`.** -/
theorem repHoareAtV (h : Thm29SecondAtDomains) : IsPRepresentable V PRep.hoareOp := by
  obtain ⟨_gr, _fn, hfg, hgf⟩ := LemThirty.retracts_hoare h
  exact R45.Agent4.rep_hoare hfg hgf

/-- **Conjunct 10 of Lemma 30: `(·)♮` is p-representable over `V`** — the conjunct
§7.4 exists for, and the one no scheme reached before this module. -/
theorem repPlotkinAtV (h : Thm29SecondAtDomains) : IsPRepresentable V plotkinOp := by
  obtain ⟨_gr, _fn, hfg, hgf⟩ := LemThirty.retracts_plotkin h
  exact rep_plotkin hfg hgf

/-! ## 4. Eight of Lemma 30's ten conjuncts from `Thm29Normal` alone -/

/-- **Eight conjuncts of Lemma 30 follow from `Thm29Normal`.**

`R45.Agent3.five_conjuncts_of_thm29Normal` had five — `×`, `⊗`, `+`, `⊕`, `(·)⊥`.
The three powerdomain conjuncts join them: two because r0045's agent4 discharged
the Smyth and Hoare obligations, one because `rep_plotkin` above is new.

The hypothesis is `Thm29Normal` itself, with no instance binder added; the
retraction pairs come through `thm29SecondAtDomains_of_thm29Normal`, which is
proved. -/
theorem eight_conjuncts_of_thm29Normal (h : Thm29Normal) :
    IsPRepresentable₂ V PRep.prodOp ∧
    IsPRepresentable₂ V PRep.smashOp ∧
    IsPRepresentable₂ V PRep.sepSumOp ∧
    IsPRepresentable₂ V PRep.coalSumOp ∧
    IsPRepresentable V PRep.liftOp ∧
    IsPRepresentable V PRep.smythOp ∧
    IsPRepresentable V PRep.hoareOp ∧
    IsPRepresentable V plotkinOp :=
  let h' := LemThirty.thm29SecondAtDomains_of_thm29Normal h
  ⟨LemThirty.rep_prod_V h', R45.Agent3.rep_smash_V h', R45.Agent3.rep_sepSum_V h',
    R45.Agent3.rep_coalSum_V h', LemThirty.rep_lift_V h', repSmythAtV h', repHoareAtV h',
    repPlotkinAtV h'⟩

/-- **`Lemma30AtV` from `Thm29Normal` and its two arrow conjuncts.**

Arity 3, against `LemThirty.lemma30_of`'s arity 10 and r0045's implicit arity 6.
The two remaining hypotheses are conjuncts 1 and 2, `→` and `⇸`, and
`R45.Agent3.not_boundedComplete_V` is why they cannot be supplied here: it proves
`Thm29SecondAtDomains → ¬ BoundedComplete V`, and `PRepFun.rep_arrow` and
`PRepFun.rep_strictArrow` are this development's only routes to those conjuncts,
both under `[BoundedComplete U]`.

So `Lemma30AtV` is now **open at exactly two named obstructions** — [Gun87]'s
`Thm29Normal`, and the development's own bounded-completeness route to
`Domain (D → E)`. Neither is a missing representation scheme; that gap is closed. -/
theorem lemma_30_atV_of_thm29Normal_of_arrows (h : Thm29Normal)
    (h_arrow : IsPRepresentable₂ V PRep.funOp)
    (h_strictArrow : IsPRepresentable₂ V PRep.strictFunOp) :
    LemThirty.Lemma30AtV :=
  let hs := eight_conjuncts_of_thm29Normal h
  ⟨h_arrow, h_strictArrow, hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1, hs.2.2.2.2.1,
    hs.2.2.2.2.2.1, hs.2.2.2.2.2.2.1, hs.2.2.2.2.2.2.2⟩

alias lemma30AtV_of_thm29Normal_of_arrows := lemma_30_atV_of_thm29Normal_of_arrows

end ScottDomains.R46.Agent3
