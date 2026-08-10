import ScottDomains.PowerdomainMap
import ScottDomains.PRepSum
import ScottDomains.Lemma28AtU
import ScottDomains.Powerdomain.BoundedComplete

/-!
# Lemma 28's `(·)♯` and `(·)♭`, reduced to two named obligations each

Gunter & Scott, *Semantic Domains*, §7.3, Lemma 28, conjuncts 8 and 9:
`(·)♯` and `(·)♭` are p-representable over `U`.

`Lemma28AtU.lemma_28_atU_of'` has arity 2 — `h_smyth` and `h_hoare` — and its
docstring records why:

> `smythOp` and `hoareOp` are definable on `Cpo` (r0036). Measured by grep in
> r0037: the development defines **no action of a map on either powerdomain**, so
> there is no `r ↦ r♯` from which to build the conjugating family.

`ScottDomains.PowerdomainMap` supplies that action. This module spends it, and
measures exactly how much of each conjunct it closes.

## What the representation scheme asks for, and where each item now stands

`PRep.isPRepresentable_of_repFamily` takes five inputs. Measured against `(·)♯`:

| # | Input | Status after this round |
| - | ----- | ----------------------- |
| 1 | a conjugating family `C : Fp(U) → ScottHom (U♯) (U♯)` | **supplied** — `smythFamily p = (p.val)♯` |
| 2 | `C p` is a projection | **proved** — `PowerdomainMap.isProjection_smyth`, from the functor laws |
| 3 | `C` is monotone in `p` | **proved** — `PowerdomainMap.map_le_map` |
| 4 | the retraction pair `(fn, gr)` at `U` | **discharged** — `PRepSum.pairAtU` applies, since `U♯` is a domain (Theorem 11) and bounded complete (Lemma 13, `instBoundedCompleteSmyth`) |
| 5 | `im(C p) ≅ (im p)♯`, and the index least upper bound | **open** — the two obligations below |

Rows 1–4 were *all* unavailable before this round: row 1 did not exist, rows 2
and 3 are statements about an object that did not exist, and row 4 could not be
posed because `U♯` had never been exhibited as a bounded complete domain in this
argument. So the conjunct moves from *no formulation at all* to *two named
propositions*, which is the unit of value r0040's finding calls for.

## The two that remain, and what they are

`SmythImageIso` — **`im(p♯) ≅ (im p)♯`**. This is the statement that the upper
powerdomain commutes with the image of a finitary projection, and it is a real
theorem about the functor, not a bookkeeping step: `K(im p)` is *not* `p(K(U))`,
and `PowerdomainCompacts` proves that `p(K(D)) ⊆ K(D)` fails outright, so the
identification of the two sides cannot be made by transporting a basis.

**Both obligations are now discharged, and the route this paragraph predicted was
not the one taken.** The sentence continued "…it has to go through
`IsProjection.isCompactElement_iff` (Lemma 5), which characterises `K(im p)`
intrinsically." That necessity claim is false. `R45.Agent4.smythImageIso` and
`R45.Agent4.hoareImageIso` (`A4PowerdomainRep.lean:256,283`) conclude the two
image isomorphisms and neither proof mentions `K(im p)` at all: factor
`p = ι ∘ π` through its image, apply the functor laws `map_id` / `map_comp`, and
`map ι` is a section whose range is `im(map p)` — a statement about two monotone
maps between two preorders, with no domain theory in it.

Measured in r0046 by `scripts/a5-r46-deps.lean`, which computes the transitive
constant closure of each proof term in the built `.olean`:
`ScottHom.IsProjection.isCompactElement_iff` is **absent** from
`deps(smythImageIso)` (2777 constants) and from `deps(hoareImageIso)` (2772). The
same probe reports `USES` for `nonempty_orderIso_range_of_section`, the route the
proofs do take, so the negative answers are not an artifact of the instrument.

Two r0045 agents (agent2 and agent4) reached the same conclusion independently
before it was measured. The sentence is kept above rather than deleted because it
records what the development believed when `PowerdomainMap` was written, and that
belief is what made the conjunct look harder than it was.

`SmythFamilyLUB` — **local continuity of the action**: `p ↦ p♯` preserves
directed suprema pointwise. `map f I = ⨆ {fold ({|f k|})ₖ∈u | u ∈ I}`, so this is
an interchange of two suprema, with the inner one a finite `⋓`-fold; joint
continuity of `⋓` (`ContinuousAlgebra.isLUB_op_image`) is what would drive it.

Neither is stubbed with `sorry`: each is a `def … : Prop`, and `rep_smyth_of`
takes them as hypotheses, so the kernel checks that exactly two are outstanding.

## The `♭` case is the same file twice

Everything above holds verbatim for the Hoare powerdomain, with
`instBoundedCompleteHoare` in place of `instBoundedCompleteSmyth` — and that
instance is *cheaper*, needing only `[Domain α]` where the Smyth one needs
`[BoundedComplete α]`. Both are available at `Dyadic.U`.
-/

namespace ScottDomains.PowerdomainMap.Rep

open ScottDomains ScottDomains.BifiniteUniversal ScottDomains.PRep
open ScottHom

universe u

/-! ## 1. `(·)♯` -/

section Smyth

variable {U : Type u} [CompletePartialOrder U] [Domain U]

/-- The conjugating family for `(·)♯`: `p ↦ p♯`, the action of `p` on the upper
powerdomain. This is the object r0037 measured as absent. -/
noncomputable def smythFamily (p : ↥(Fp U)) :
    ScottHom (Smyth.Powerdomain U) (Smyth.Powerdomain U) :=
  ⟨PowerdomainMap.smyth ⇑p.val, PowerdomainMap.scottContinuous_smyth p.val.scottContinuous⟩

@[simp] theorem smythFamily_apply (p : ↥(Fp U)) (I : Smyth.Powerdomain U) :
    smythFamily p I = PowerdomainMap.smyth ⇑p.val I := rfl

/-- **`p♯` is a projection when `p` is** — from the two functor laws, with no
appeal to compact elements. -/
theorem isProjection_smythFamily (p : ↥(Fp U)) : IsProjection (smythFamily p) :=
  PowerdomainMap.isProjection_smyth p.val.scottContinuous
    (mem_Fp.mp p.2).isProjection.idem (mem_Fp.mp p.2).isProjection.le

/-- **The family is monotone in its `Fp(U)` index** — `map_le_map`. -/
theorem smythFamily_mono {p q : ↥(Fp U)} (h : p ≤ q) : smythFamily p ≤ smythFamily q :=
  fun I => PowerdomainMap.map_le_map (fun x => h x)
    (PowerdomainMap.foldMono_smyth p.val.scottContinuous)
    (PowerdomainMap.foldMono_smyth q.val.scottContinuous) I

/-- **Obligation 1 for `(·)♯`**: the upper powerdomain commutes with the image of
a finitary projection, `im(p♯) ≅ (im p)♯`. -/
def SmythImageIso (U : Type u) [CompletePartialOrder U] [Domain U] : Prop :=
  ∀ p : ↥(Fp U),
    Nonempty (↥(Set.range ⇑(smythFamily p)) ≃o (smythOp (FpImage p)).carrier)

/-- **Obligation 2 for `(·)♯`**: `p ↦ p♯` is pointwise Scott continuous in its
`Fp(U)` index. -/
def SmythFamilyLUB (U : Type u) [CompletePartialOrder U] [Domain U] : Prop :=
  ∀ {d : Set ↥(Fp U)}, d.Nonempty → DirectedOn (· ≤ ·) d → ∀ {a : ↥(Fp U)}, IsLUB d a →
    ∀ y : Smyth.Powerdomain U, IsLUB ((fun p => smythFamily p y) '' d) (smythFamily a y)

/-- `im(p♯)` is a domain, given obligation 1: transport `Domain ((im p)♯)`, which
is Theorem 11 at the domain `im p`, along the isomorphism. -/
theorem domain_range_smythFamily (hiso : SmythImageIso U) (p : ↥(Fp U)) :
    @Domain _ (IsProjection.rangeCompletePartialOrder (isProjection_smythFamily p)) := by
  haveI : Domain (FpImage p).carrier := (mem_Fp.mp p.2).domain
  haveI : Domain (smythOp (FpImage p)).carrier := Smyth.instDomain
  letI : CompletePartialOrder ↥(Set.range ⇑(smythFamily p)) :=
    IsProjection.rangeCompletePartialOrder (isProjection_smythFamily p)
  exact domain_orderIso (hiso p).some.symm

/-- **`(·)♯` is p-representable from the two obligations, given the pair.** -/
theorem rep_smyth_of (hiso : SmythImageIso U) (hlub : SmythFamilyLUB U)
    {fn : ScottHom U (Smyth.Powerdomain U)} {gr : ScottHom (Smyth.Powerdomain U) U}
    (hfg : ∀ y, fn (gr y) = y) (hgf : ∀ x, gr (fn x) ≤ x) :
    IsPRepresentable U smythOp :=
  isPRepresentable_of_repFamily hfg
    (fun p => isFinitaryProjection_repOf hfg hgf (isProjection_smythFamily p)
      (domain_range_smythFamily hiso p))
    smythFamily_mono hlub hiso

end Smyth

/-! ## 2. `(·)♭` -/

section Hoare

variable {U : Type u} [CompletePartialOrder U] [Domain U]

/-- The conjugating family for `(·)♭`: `p ↦ p♭`. -/
noncomputable def hoareFamily (p : ↥(Fp U)) :
    ScottHom (IdealCompletion (Hoare.Pf ↥(compacts U)))
      (IdealCompletion (Hoare.Pf ↥(compacts U))) :=
  ⟨PowerdomainMap.hoare ⇑p.val, PowerdomainMap.scottContinuous_hoare p.val.scottContinuous⟩

@[simp] theorem hoareFamily_apply (p : ↥(Fp U))
    (I : IdealCompletion (Hoare.Pf ↥(compacts U))) :
    hoareFamily p I = PowerdomainMap.hoare ⇑p.val I := rfl

theorem isProjection_hoareFamily (p : ↥(Fp U)) : IsProjection (hoareFamily p) :=
  PowerdomainMap.isProjection_hoare p.val.scottContinuous
    (mem_Fp.mp p.2).isProjection.idem (mem_Fp.mp p.2).isProjection.le

theorem hoareFamily_mono {p q : ↥(Fp U)} (h : p ≤ q) : hoareFamily p ≤ hoareFamily q :=
  fun I => PowerdomainMap.map_le_map (fun x => h x)
    (PowerdomainMap.foldMono_hoare p.val.scottContinuous)
    (PowerdomainMap.foldMono_hoare q.val.scottContinuous) I

/-- **Obligation 1 for `(·)♭`**: `im(p♭) ≅ (im p)♭`. -/
def HoareImageIso (U : Type u) [CompletePartialOrder U] [Domain U] : Prop :=
  ∀ p : ↥(Fp U),
    Nonempty (↥(Set.range ⇑(hoareFamily p)) ≃o (hoareOp (FpImage p)).carrier)

/-- **Obligation 2 for `(·)♭`**: `p ↦ p♭` is pointwise Scott continuous. -/
def HoareFamilyLUB (U : Type u) [CompletePartialOrder U] [Domain U] : Prop :=
  ∀ {d : Set ↥(Fp U)}, d.Nonempty → DirectedOn (· ≤ ·) d → ∀ {a : ↥(Fp U)}, IsLUB d a →
    ∀ y : IdealCompletion (Hoare.Pf ↥(compacts U)),
      IsLUB ((fun p => hoareFamily p y) '' d) (hoareFamily a y)

theorem domain_range_hoareFamily (hiso : HoareImageIso U) (p : ↥(Fp U)) :
    @Domain _ (IsProjection.rangeCompletePartialOrder (isProjection_hoareFamily p)) := by
  haveI : Domain (FpImage p).carrier := (mem_Fp.mp p.2).domain
  haveI : Domain (hoareOp (FpImage p)).carrier := IdealCompletion.instDomain
  letI : CompletePartialOrder ↥(Set.range ⇑(hoareFamily p)) :=
    IsProjection.rangeCompletePartialOrder (isProjection_hoareFamily p)
  exact domain_orderIso (hiso p).some.symm

/-- **`(·)♭` is p-representable from the two obligations, given the pair.** -/
theorem rep_hoare_of (hiso : HoareImageIso U) (hlub : HoareFamilyLUB U)
    {fn : ScottHom U (IdealCompletion (Hoare.Pf ↥(compacts U)))}
    {gr : ScottHom (IdealCompletion (Hoare.Pf ↥(compacts U))) U}
    (hfg : ∀ y, fn (gr y) = y) (hgf : ∀ x, gr (fn x) ≤ x) :
    IsPRepresentable U hoareOp :=
  isPRepresentable_of_repFamily hfg
    (fun p => isFinitaryProjection_repOf hfg hgf (isProjection_hoareFamily p)
      (domain_range_hoareFamily hiso p))
    hoareFamily_mono hlub hiso

end Hoare

/-! ## 3. At the paper's `U`: the retraction pair is discharged

Theorem 27 supplies the pair for any bounded complete domain, and both
powerdomains of `Dyadic.U` are one:

| # | carrier | `Domain` | `BoundedComplete` |
| - | ------- | -------- | ----------------- |
| 1 | `U♯` | Theorem 11, `Smyth.instDomain` | **Lemma 13**, `instBoundedCompleteSmyth`, spending `BoundedComplete Dyadic.U` |
| 2 | `U♭` | Theorem 11, `Hoare.theorem_11_hoare` | **Lemma 13**, `instBoundedCompleteHoare`, which needs only `[Domain α]` |

So the hypothesis count at `U` is **two, not three** — the same reduction
`PRepSum.pairAtU` performs for `×` and `(·)⊥`. This is the second place Lemma 13
is spent by Lemma 28, after Lemma 10's role in `⇸` and `⊗`. -/

section AtU

/-- **`(·)♯` at `U`, from its two obligations alone.** -/
theorem repSmythAtU (hiso : SmythImageIso Dyadic.U) (hlub : SmythFamilyLUB Dyadic.U) :
    IsPRepresentable Dyadic.U smythOp := by
  haveI : Domain (Smyth.Powerdomain Dyadic.U) := Smyth.instDomain
  haveI : BoundedComplete (Smyth.Powerdomain Dyadic.U) :=
    PowerdomainBC.instBoundedCompleteSmyth Dyadic.U
  obtain ⟨_fn, _gr, hfg, hgf⟩ := PRepSum.pairAtU (Smyth.Powerdomain Dyadic.U)
  exact rep_smyth_of hiso hlub hfg hgf

/-- **`(·)♭` at `U`, from its two obligations alone.** -/
theorem repHoareAtU (hiso : HoareImageIso Dyadic.U) (hlub : HoareFamilyLUB Dyadic.U) :
    IsPRepresentable Dyadic.U hoareOp := by
  haveI : Domain (IdealCompletion (Hoare.Pf ↥(compacts Dyadic.U))) :=
    IdealCompletion.instDomain
  haveI : BoundedComplete (IdealCompletion (Hoare.Pf ↥(compacts Dyadic.U))) :=
    PowerdomainBC.instBoundedCompleteHoare Dyadic.U
  obtain ⟨_fn, _gr, hfg, hgf⟩ :=
    PRepSum.pairAtU (IdealCompletion (Hoare.Pf ↥(compacts Dyadic.U)))
  exact rep_hoare_of hiso hlub hfg hgf

/-- **Lemma 28 over `U` from four propositions about the powerdomain action.**

The arity is the measurement, as everywhere in this development: 9 for
`PRep.lemma_28_of`, 5 for `PRepSum.lemma_28_atU_of`, 2 for
`Lemma28AtU.lemma_28_atU_of'`, and 4 here — but the four are no longer about
p-representability at all. They are two facts about `(·)♯` and two about `(·)♭`,
each an ordinary statement about a functor, and neither mentions `Fp(U)`'s
retraction pair, which is now discharged. -/
theorem lemma_28_atU_of'' (hisoSmyth : SmythImageIso Dyadic.U)
    (hlubSmyth : SmythFamilyLUB Dyadic.U) (hisoHoare : HoareImageIso Dyadic.U)
    (hlubHoare : HoareFamilyLUB Dyadic.U) :
    PRep.Lemma28AtU :=
  Lemma28AtU.lemma_28_atU_of' (repSmythAtU hisoSmyth hlubSmyth)
    (repHoareAtU hisoHoare hlubHoare)

end AtU

end ScottDomains.PowerdomainMap.Rep

/- Axiom audit, by `scripts/axioms.sh` (run, then recorded here so the build emits
no `info` lines). None depends on `sorryAx`; the four obligations are hypotheses,
not holes.

  …Rep.isProjection_smythFamily [propext, Classical.choice, Quot.sound]
  …Rep.smythFamily_mono         [propext, Classical.choice, Quot.sound]
  …Rep.rep_smyth_of             [propext, Classical.choice, Quot.sound]
  …Rep.rep_hoare_of             [propext, Classical.choice, Quot.sound]
  …Rep.repSmythAtU              [propext, Classical.choice, Quot.sound]
  …Rep.repHoareAtU              [propext, Classical.choice, Quot.sound]
  …Rep.lemma_28_atU_of''          [propext, Classical.choice, Quot.sound] -/
