import ScottDomains.PowerdomainMapRep
import ScottDomains.PRepFun

/-!
# r0045, agent4: the four powerdomain-map representability obligations

`ScottDomains.PowerdomainMap.Rep` states four `Prop`-valued `def`s and proves no
theorem whose conclusion is any of them:

| # | Claim | Content |
| - | ----- | ------- |
| 1 | `SmythImageIso` | `im(p♯) ≅ (im p)♯` for every `p ∈ Fp(U)` |
| 2 | `SmythFamilyLUB` | `p ↦ p♯` preserves directed suprema, pointwise in `U♯` |
| 3 | `HoareImageIso` | `im(p♭) ≅ (im p)♭` |
| 4 | `HoareFamilyLUB` | `p ↦ p♭` preserves directed suprema, pointwise in `U♭` |

This module discharges all four, at every `U` with `[CompletePartialOrder U]
[Domain U]` and with no further hypothesis. The Smyth and Hoare arguments are
**the same argument twice**: every lemma below is generic in the pre-order `A`
presenting `Pf(K(D))`, and the two powerdomains enter only through the single
obligation `hmono : Monotone (foldGen (unitComp f))`, discharged by
`PowerdomainMap.foldMono_smyth` and `PowerdomainMap.foldMono_hoare`.

## 1. The image isomorphism is not about powerdomains at all

`PowerdomainMapRep.lean`'s docstring says the identification `im(p♯) ≅ (im p)♯`
"has to go through `IsProjection.isCompactElement_iff` (Lemma 5), which
characterises `K(im p)` intrinsically". **That is not the cheapest route and this
module does not take it.** `K(im p)` is never mentioned.

Write `ι : im(p) → U` for the inclusion and `π : U → im(p)` for the
corestriction `x ↦ p x`. Then `π ∘ ι = id` and `ι ∘ π = p` — a section-retraction
pair, both legs Scott continuous (`PRepFun.scottContinuous_val`,
`PRepFun.scottContinuous_corestrict`). Apply the functor: `map` is a functor
(`PowerdomainMap.map_id`, `PowerdomainMap.map_comp`), so

    map π ∘ map ι = map (π ∘ ι) = map id = id,      map ι ∘ map π = map p.

The first equation makes `map ι` a section, hence injective and order-reflecting;
the second makes `im(map p) = im(map ι)`. So `im(p♯) ≅ (im p)♯` reduces to
`nonempty_orderIso_range_of_section`, a statement about two monotone maps between
two preorders with **no domain theory in it whatever**. The functor laws are the
entire content, and they were proved in r0041.

## 2. The family LUB is fold-continuity plus one interchange

`p♯ y = ⨆ {foldGen (·)♯ u | u ∈ y}`, so preserving a directed supremum in `p`
is an interchange of two suprema. It factors into three steps:

1. least upper bounds in `Fp(U)` are pointwise (`isLUB_val_image_of_isLUB_fp'`,
   which is where `[Domain U]` and `isFinitaryProjection_sSup` are spent), and
   `{|·|}` is continuous (`ContinuousAlgebra.scottContinuous_unit`), giving the
   claim one compact element at a time;
2. `isLUB_fold` lifts that from one compact to the finite fold
   `{|p k₁|} ⋓ ⋯ ⋓ {|p kₙ|}`, by induction on the finite set. The step is
   `isLUB_op_of_isLUB`: joint continuity of `⋓` gives the least upper bound over
   the *product* index `d × d` (`ContinuousAlgebra.isLUB_op_image`), and
   directedness of `d` plus monotonicity of both factors makes the diagonal
   cofinal in the product;
3. `isLUB_idealExtend` in both directions moves between the fold and the ideal
   extension, with `PowerdomainMap.map_le_map` supplying the upper-bound half.

Step 2 is where the two suprema are actually interchanged, and it costs exactly
the joint (not separate) continuity of `⋓` that `ContinuousAlgebra.Binop`
demands.

## 3. Smyth and Hoare are dual here, and the docstring defect is elsewhere

r0044's agent8 recorded that `FlatPowerdomain.smyth_natBot_orderIso`'s docstring
claims a directed-supremum clause its statement lacks. That is a defect in a
*concrete calculation at `N⊥`* and it does not touch these four: none of the
four proofs below reads the flat case, and the asymmetry it reports does not
appear at this level of generality. Measured here: the Smyth proof and the Hoare
proof differ in **one token each** — `foldMono_smyth` versus `foldMono_hoare`,
and `Smyth.Basis U` versus `Hoare.Pf ↥(compacts U)` as the presentation `A`. The
theory instances `IsUpper`/`IsLower` are consumed only inside those two lemmas,
which r0041 already proved.
-/

namespace ScottDomains.R45.Agent4

open ScottDomains ScottDomains.BifiniteUniversal ScottDomains.PRep
open ScottDomains.ContinuousAlgebra ScottDomains.IdealCompletion
open ScottDomains.PowerdomainMap ScottDomains.PowerdomainMap.Rep
open ScottHom

universe u

/-! ## 1. A section-retraction pair identifies `im(i ∘ r)` with the section's source

Pure order theory: no cpo, no continuity, no algebra. `i` and `r` are monotone,
`r ∘ i = id`, and `c` is *any* map agreeing with `i ∘ r`. -/

section OrderIso

/-- **`im(i ∘ r) ≅ X` for a monotone section-retraction pair `r ∘ i = id`.**

`i` is injective and order-reflecting because `r` undoes it; its image is all of
`im(i ∘ r)` because `i x = (i ∘ r) (i x)` in one direction and
`(i ∘ r) y = i (r y)` in the other. -/
theorem nonempty_orderIso_range_of_section {X Y : Type*} [PartialOrder X] [Preorder Y]
    {i : X → Y} {r : Y → X} {c : Y → Y} (hi : Monotone i) (hr : Monotone r)
    (hri : ∀ x, r (i x) = x) (hc : ∀ y, c y = i (r y)) :
    Nonempty (↥(Set.range c) ≃o X) := by
  have hmem : ∀ x : X, i x ∈ Set.range c := fun x => ⟨i x, by rw [hc, hri]⟩
  have hle : ∀ x y : X,
      (⟨i x, hmem x⟩ : ↥(Set.range c)) ≤ ⟨i y, hmem y⟩ ↔ x ≤ y := by
    intro x y
    refine ⟨fun h => ?_, fun h => hi h⟩
    have h' := hr (show i x ≤ i y from h)
    rwa [hri, hri] at h'
  have hsurj : Function.Surjective
      (fun x : X => (⟨i x, hmem x⟩ : ↥(Set.range c))) := by
    rintro ⟨_, y, rfl⟩
    exact ⟨r y, Subtype.ext (hc y).symm⟩
  exact ⟨(RelIso.ofSurjective
    (OrderEmbedding.ofMapLEIff (fun x : X => (⟨i x, hmem x⟩ : ↥(Set.range c))) hle)
    hsurj).symm⟩

end OrderIso

/-! ## 2. Two suprema along one directed index

`isLUB_op_image` gives the least upper bound of `⋓` over the *product* of two
index sets. When both families are monotone in one directed index, the diagonal
is cofinal in that product, which is what turns joint continuity of `⋓` into
continuity along a single directed family. -/

section Diagonal

variable {E : Type u} [CompletePartialOrder E] [Binop E]
variable {ι : Type*} [Preorder ι]

/-- **`⋓` of two monotone families is the supremum along the diagonal.** Joint
continuity gives the supremum over `d ×ˢ d`; directedness of `d` sends any
off-diagonal pair `(p, q)` below a diagonal one `(c, c)`. -/
theorem isLUB_op_of_isLUB {d : Set ι} (hne : d.Nonempty) (hd : DirectedOn (· ≤ ·) d)
    {G H : ι → E} (hG : Monotone G) (hH : Monotone H) {a : ι}
    (hGa : IsLUB (G '' d) (G a)) (hHa : IsLUB (H '' d) (H a)) :
    IsLUB ((fun p => G p ⋓ H p) '' d) (G a ⋓ H a) := by
  refine ⟨?_, fun z hz => ?_⟩
  · rintro _ ⟨p, hp, rfl⟩
    exact op_mono (hGa.1 ⟨p, hp, rfl⟩) (hHa.1 ⟨p, hp, rfl⟩)
  · have hdG : DirectedOn (· ≤ ·) (G '' d) := by
      rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩
      obtain ⟨c, hc, hpc, hqc⟩ := hd p hp q hq
      exact ⟨G c, ⟨c, hc, rfl⟩, hG hpc, hG hqc⟩
    have hdH : DirectedOn (· ≤ ·) (H '' d) := by
      rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩
      obtain ⟨c, hc, hpc, hqc⟩ := hd p hp q hq
      exact ⟨H c, ⟨c, hc, rfl⟩, hH hpc, hH hqc⟩
    refine (isLUB_op_image (hne.image G) (hne.image H) hdG hdH hGa hHa).2 ?_
    rintro _ ⟨⟨_, _⟩, ⟨⟨p, hp, rfl⟩, ⟨q, hq, rfl⟩⟩, rfl⟩
    obtain ⟨c, hc, hpc, hqc⟩ := hd p hp q hq
    exact le_trans (op_mono (hG hpc) (hH hqc)) (hz ⟨c, hc, rfl⟩)

variable [IsSemilattice E]

/-- **The fold `f x₁ ⋓ ⋯ ⋓ f xₙ` preserves a directed supremum in its function
argument.** Induction over the non-empty finite set, with `isLUB_op_of_isLUB` at
the step and monotonicity of the tail fold from `fold_le_fold`. -/
theorem isLUB_fold {K : Type u} {d : Set ι} (hne : d.Nonempty) (hd : DirectedOn (· ≤ ·) d)
    {F : ι → K → E} (hFmono : ∀ {p q : ι}, p ≤ q → ∀ k, F p k ≤ F q k)
    {a : ι} (hFlub : ∀ k, IsLUB ((fun p => F p k) '' d) (F a k))
    {w : Finset K} (hw : w.Nonempty) :
    IsLUB ((fun p => fold w hw (F p)) '' d) (fold w hw (F a)) := by
  induction hw using Finset.Nonempty.cons_induction with
  | singleton k => simpa using hFlub k
  | cons k s hks hs ih =>
      have e : ∀ p : ι, fold (Finset.cons k s hks) (Finset.cons_nonempty hks) (F p)
          = F p k ⋓ fold s hs (F p) := fun p => fold_cons hks hs (F p)
      simp only [e]
      exact isLUB_op_of_isLUB hne hd (fun _ _ h => hFmono h k)
        (fun _ _ h => fold_le_fold hs fun j _ => hFmono h j) (hFlub k) ih

end Diagonal

/-! ## 3. The family LUB, generically in the presentation `A` -/

section FamilyLUB

variable {U : Type u} [CompletePartialOrder U] [Domain U]

/-- **`p ↦ p♮` preserves directed suprema of `Fp(U)`, pointwise.** Generic in the
pre-order `A` presenting `Pf(K(U))`, so one proof serves `(·)♯` and `(·)♭` both;
the single powerdomain-specific input is `hmono`. -/
theorem isLUB_mapFamily {A : Type u} [Preorder A] [OrderBot A] [FinSets ↥(compacts U) A]
    (hmono : ∀ p : ↥(Fp U), Monotone (foldGen (A := A) (unitComp (B := A) ⇑p.val)))
    {d : Set ↥(Fp U)} (hne : d.Nonempty) (hd : DirectedOn (· ≤ ·) d)
    {a : ↥(Fp U)} (ha : IsLUB d a) (y : IdealCompletion A) :
    IsLUB ((fun p : ↥(Fp U) => PowerdomainMap.map (A := A) (B := A) ⇑p.val y) '' d)
      (PowerdomainMap.map (A := A) (B := A) ⇑a.val y) := by
  -- Step 1: least upper bounds in `Fp(U)` are pointwise, and `{|·|}` is continuous.
  have hval : IsLUB ((fun q : ↥(Fp U) => q.val) '' d) a.val :=
    isLUB_val_image_of_isLUB_fp' hne hd ha
  have hdv : DirectedOn (· ≤ ·) ((fun q : ↥(Fp U) => q.val) '' d) := by
    rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩
    obtain ⟨c, hc, h₁, h₂⟩ := hd p hp q hq
    exact ⟨c.val, ⟨c, hc, rfl⟩, h₁, h₂⟩
  have hunit : ∀ k : ↥(compacts U),
      IsLUB ((fun p : ↥(Fp U) => (unit (p.val (k : U)) : IdealCompletion A)) '' d)
        (unit (a.val (k : U))) := by
    intro k
    have heval := ScottHom.isLUB_eval_image_of_isLUB hdv hval (k : U)
    rw [Set.image_image] at heval
    have hdev : DirectedOn (· ≤ ·) ((fun q : ↥(Fp U) => q.val (k : U)) '' d) := by
      rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩
      obtain ⟨c, hc, h₁, h₂⟩ := hd p hp q hq
      exact ⟨c.val (k : U), ⟨c, hc, rfl⟩, h₁ _, h₂ _⟩
    have hu := scottContinuous_unit (A := A) (hne.image _) hdev heval
    rwa [Set.image_image] at hu
  -- Step 2: lift from one compact element to the finite fold.
  have hfold : ∀ u : A,
      IsLUB ((fun p : ↥(Fp U) => foldGen (A := A) (unitComp (B := A) ⇑p.val) u) '' d)
        (foldGen (A := A) (unitComp (B := A) ⇑a.val) u) := by
    intro u
    exact isLUB_fold (E := IdealCompletion A) (K := ↥(compacts U)) hne hd
      (F := fun (p : ↥(Fp U)) (k : ↥(compacts U)) => (unit (p.val (k : U)) : IdealCompletion A))
      (fun {_ _} h k => monotone_unit (h (k : U))) hunit (toFinset_nonempty u)
  -- Step 3: move between the fold and the ideal extension.
  refine ⟨?_, fun z hz => ?_⟩
  · rintro _ ⟨p, hp, rfl⟩
    exact PowerdomainMap.map_le_map (fun x => ha.1 hp x) (hmono p) (hmono a) y
  · rw [PowerdomainMap.map_apply]
    refine (isLUB_idealExtend (hmono a) y).2 ?_
    rintro _ ⟨u, hu, rfl⟩
    refine (hfold u).2 ?_
    rintro _ ⟨p, hp, rfl⟩
    exact le_trans ((isLUB_idealExtend (hmono p) y).1 ⟨u, hu, rfl⟩) (hz ⟨p, hp, rfl⟩)

/-- **Claim 2 discharged**: `PowerdomainMap.Rep.SmythFamilyLUB`, no hypotheses
beyond the instance binders `[CompletePartialOrder U] [Domain U]`. -/
theorem smythFamilyLUB : SmythFamilyLUB U := by
  intro d hne hd a ha y
  exact isLUB_mapFamily (A := Smyth.Basis U)
    (fun p => PowerdomainMap.foldMono_smyth p.val.scottContinuous) hne hd ha y

/-- **Claim 4 discharged**: `PowerdomainMap.Rep.HoareFamilyLUB`. The same proof
with `foldMono_hoare` for `foldMono_smyth`. -/
theorem hoareFamilyLUB : HoareFamilyLUB U := by
  intro d hne hd a ha y
  exact isLUB_mapFamily (A := Hoare.Pf ↥(compacts U))
    (fun p => PowerdomainMap.foldMono_hoare p.val.scottContinuous) hne hd ha y

end FamilyLUB

/-! ## 4. The image isomorphisms -/

section ImageIso

variable {U : Type u} [CompletePartialOrder U] [Domain U]

/-- **Claim 1 discharged**: `PowerdomainMap.Rep.SmythImageIso`, `im(p♯) ≅ (im p)♯`
for every finitary projection `p`, with no hypotheses beyond the instance
binders. -/
theorem smythImageIso : SmythImageIso U := by
  intro p
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
  have hsec := PowerdomainMap.smyth_comp hci hcr
  rw [show (fun x : U => (⟨p.val x, Set.mem_range_self x⟩ : ↥(Set.range ⇑p.val)))
        ∘ (Subtype.val : ↥(Set.range ⇑p.val) → U) = id from funext hri,
    PowerdomainMap.smyth_id] at hsec
  have hcomp := PowerdomainMap.smyth_comp hcr hci
  refine nonempty_orderIso_range_of_section
    (PowerdomainMap.scottContinuous_smyth hci).monotone
    (PowerdomainMap.scottContinuous_smyth hcr).monotone
    (fun X => congrFun hsec.symm X) (fun y => congrFun hcomp y)

/-- **Claim 3 discharged**: `PowerdomainMap.Rep.HoareImageIso`, `im(p♭) ≅ (im p)♭`.
Token-for-token the Smyth proof with `hoare` for `smyth`. -/
theorem hoareImageIso : HoareImageIso U := by
  intro p
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
  have hsec := PowerdomainMap.hoare_comp hci hcr
  rw [show (fun x : U => (⟨p.val x, Set.mem_range_self x⟩ : ↥(Set.range ⇑p.val)))
        ∘ (Subtype.val : ↥(Set.range ⇑p.val) → U) = id from funext hri,
    PowerdomainMap.hoare_id] at hsec
  have hcomp := PowerdomainMap.hoare_comp hcr hci
  refine nonempty_orderIso_range_of_section
    (PowerdomainMap.scottContinuous_hoare hci).monotone
    (PowerdomainMap.scottContinuous_hoare hcr).monotone
    (fun X => congrFun hsec.symm X) (fun y => congrFun hcomp y)

end ImageIso

/-! ## 5. What the four discharge downstream

`PowerdomainMapRep.lean` states five consumers of the four obligations. With the
four now theorems, each loses those hypotheses; the versions below are the
consumers with the obligations substituted, so the arity drop is kernel-checked
rather than asserted. `lemma_28_atU_of''` had arity 4 and reaches arity 0. -/

section Consumers

variable {U : Type u} [CompletePartialOrder U] [Domain U]

/-- `PowerdomainMapRep.rep_smyth_of` with both obligations discharged: `(·)♯` is
p-representable over any `U` admitting the retraction pair. Arity 4 → 2. -/
theorem rep_smyth {fn : ScottHom U (Smyth.Powerdomain U)}
    {gr : ScottHom (Smyth.Powerdomain U) U}
    (hfg : ∀ y, fn (gr y) = y) (hgf : ∀ x, gr (fn x) ≤ x) :
    IsPRepresentable U smythOp :=
  Rep.rep_smyth_of smythImageIso smythFamilyLUB hfg hgf

/-- `PowerdomainMapRep.rep_hoare_of` with both obligations discharged. -/
theorem rep_hoare {fn : ScottHom U (IdealCompletion (Hoare.Pf ↥(compacts U)))}
    {gr : ScottHom (IdealCompletion (Hoare.Pf ↥(compacts U))) U}
    (hfg : ∀ y, fn (gr y) = y) (hgf : ∀ x, gr (fn x) ≤ x) :
    IsPRepresentable U hoareOp :=
  Rep.rep_hoare_of hoareImageIso hoareFamilyLUB hfg hgf

/-- **`(·)♯` is p-representable over §7.3's `U`, unconditionally.** Conjunct 8 of
Lemma 28. `repSmythAtU` had arity 2; this has arity 0. -/
theorem repSmythAtU : IsPRepresentable Dyadic.U smythOp :=
  Rep.repSmythAtU smythImageIso smythFamilyLUB

/-- **`(·)♭` is p-representable over `U`, unconditionally.** Conjunct 9. -/
theorem repHoareAtU : IsPRepresentable Dyadic.U hoareOp :=
  Rep.repHoareAtU hoareImageIso hoareFamilyLUB

/-- **The `(·)♯` and `(·)♭` conjuncts of Lemma 28 over `U`, with no hypotheses.**
`lemma_28_atU_of''` had arity 4; the four are now theorems. -/
theorem lemma_28_atU : PRep.Lemma28AtU :=
  Rep.lemma_28_atU_of'' smythImageIso smythFamilyLUB hoareImageIso hoareFamilyLUB

end Consumers

end ScottDomains.R45.Agent4
