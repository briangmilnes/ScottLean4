import ScottDomains.SFP
import ScottDomains.A4RepArrow
import ScottDomains.A3Lemma30Schemes

/-!
# `FpImagesBifinite`: bifinite domains are closed under projections

r0047's agent4 reduced conjuncts 1 and 2 of `Lemma30.Lemma30AtV` to exactly one
proposition,

> `R47.Agent4.FpImagesBifinite U` — every finitary-projection image of `U` is
> bifinite,

and recorded it as an open item with two named obstructions:

1. transporting a normal subposet along `p` fails, because `p a ≤ x` does not
   give `a ≤ x`;
2. the "directed family of finite-image maps below the identity" argument needs
   those maps idempotent, and `q ∘ p_i ∘ q` is not.

**Obstruction 1 is real and is avoided; obstruction 2 is real and is removed by
iterating.** Both are re-derived below rather than assumed.

## The argument

Fix a projection `p : D → D` and write `G = p ∘ p_N` for a finite normal
`N ◁ K(D)`. Then `G` is Scott continuous, `G ⊑ id`, and `im(G) ⊆ p(N)` is finite
— but `G ∘ G ≠ G`, which is agent4's obstruction 2 exactly. The repair is that a
**monotone deflation with finite image reaches a fixed point along its own
orbit**: `x ⊒ G x ⊒ G² x ⊒ ⋯` is antitone and, from index 1 on, confined to the
finite `im(G)`, so it cannot be strictly antitone; some `Gᵏ⁺¹x` is fixed by `G`.
That is `exists_iterate_fixed`, and it is the whole content of this file — a
twelve-line proof, and no idempotence is assumed anywhere. **Obstruction 2 is
therefore overstated**: the argument never needs the finite-image maps to be
idempotent, only that each has a fixed point below the point being approximated,
and a finite image forces that along the orbit.

With it, put `M = {y | G y = y}`. Three facts follow with no further input:

* `M ⊆ im(G)`, so `M` is **finite**;
* every `y ∈ M` is **compact**, by `im(G)`'s finiteness and `y = G y ⊑ G u = G a`
  for the greatest element `G a` of the directed `G '' s` — the argument of
  `SFP.isCompactElement_of_mem_range_of_finite`, restated because `G` is not a
  projection and that lemma asks for one;
* `M` is **normal** in `K(im p)`, because the orbit fixed point `c ⊑ x` produced
  by `exists_iterate_fixed` dominates every `y ∈ M` with `y ⊑ x`: `y = Gᵏ⁺¹ y ⊑
  Gᵏ⁺¹ x = c`. Normality is proved *directly at the fixed-point set*, never by
  transporting `N` along `p` — which is how obstruction 1 is avoided rather than
  met.

Finally `G` fixes each member of `u` for `N ⊇ u`, so `u ⊆ M`, and `M ⊆ im(G) ⊆
im(p)` puts `M` inside the subtype. `p` enters only through `p (p x) = p x` and
`p x ⊑ x`; **`im(p)` being a domain is never used**, so the theorem below is
stated for an arbitrary projection and `FpImagesBifinite` is the corollary.

## What this closes

`fpImagesBifinite_of_isBifinite` discharges `FpImagesBifinite U` for every
algebraic bifinite `U`, `fpImagesBifinite_V` instantiates it at `Colimit.V`
through `Colimit.isBifinite_V`, and `rep_fun_V_of_thm29Second` /
`rep_strictFun_V_of_thm29Second` drop the hypothesis from r0047's `rep_fun_V` and
`rep_strictFun_V`. Conjuncts 1 and 2 of `Lemma30AtV` now follow from
`Lemma30.Theorem29SecondAtDomains` alone, with no bounded-completeness binder and
no added instance binder.
-/

namespace ScottDomains.R49.Agent6

open ScottDomains ScottHom BifiniteUniversal

universe u

section Deflation

variable {α : Type u} [PartialOrder α] {G : α → α}

/-- Every iterate of a deflation is a deflation: `Gⁿ x ⊑ x`. -/
theorem iterate_le_self (hle : ∀ y, G y ≤ y) (n : ℕ) (x : α) : G^[n] x ≤ x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact (hle _).trans ih

/-- Every iterate of a monotone map is monotone. -/
theorem monotone_iterate (hmono : Monotone G) (n : ℕ) : Monotone G^[n] := by
  induction n with
  | zero => simpa using monotone_id
  | succ n ih =>
    intro a b hab
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact hmono (ih hab)

/-- **The idempotence agent4's obstruction 2 says `q ∘ pᵢ ∘ q` lacks, recovered
along the orbit.** A monotone `G ⊑ id` with finite image reaches, from any `x`, an
iterate `Gᵏ⁺¹x` that `G` fixes.

The sequence `k ↦ Gᵏ⁺¹x` is antitone and lands in `im(G)`. Were no term fixed, each
step would be strict, the sequence would be strictly antitone hence injective, and
its range would be an infinite subset of the finite `im(G)`. No idempotence is
assumed: this *produces* the fixed point that the naive argument assumes. -/
theorem exists_iterate_fixed (hle : ∀ y, G y ≤ y) (hfin : (Set.range G).Finite) (x : α) :
    ∃ k : ℕ, G (G^[k + 1] x) = G^[k + 1] x := by
  by_contra hcon
  have hne : ∀ k : ℕ, G (G^[k + 1] x) ≠ G^[k + 1] x := fun k hk => hcon ⟨k, hk⟩
  have hstep : ∀ k : ℕ, G^[k + 1 + 1] x < G^[k + 1] x := by
    intro k
    rw [Function.iterate_succ_apply' G (k + 1) x]
    exact lt_of_le_of_ne (hle _) (hne k)
  have hinj : Function.Injective fun k : ℕ => G^[k + 1] x :=
    (strictAnti_nat_of_succ_lt hstep).injective
  have hsub : (Set.range fun k : ℕ => G^[k + 1] x) ⊆ Set.range G := by
    rintro _ ⟨k, rfl⟩
    exact ⟨G^[k] x, (Function.iterate_succ_apply' G k x).symm⟩
  exact Set.infinite_range_of_injective hinj (hfin.subset hsub)

/-- **The greatest `G`-fixed point below `x`.** `exists_iterate_fixed` supplies a
fixed `c = Gᵏ⁺¹x ⊑ x`, and any fixed `y ⊑ x` satisfies `y = Gᵏ⁺¹ y ⊑ Gᵏ⁺¹ x = c`.
This is the upper bound that makes the fixed-point set a normal subposet. -/
theorem exists_fixed_le (hmono : Monotone G) (hle : ∀ y, G y ≤ y)
    (hfin : (Set.range G).Finite) (x : α) :
    ∃ c, G c = c ∧ c ≤ x ∧ c ∈ Set.range G ∧ ∀ y, G y = y → y ≤ x → y ≤ c := by
  obtain ⟨k, hk⟩ := exists_iterate_fixed hle hfin x
  refine ⟨G^[k + 1] x, hk, iterate_le_self hle _ x, ⟨G^[k] x, ?_⟩, ?_⟩
  · exact (Function.iterate_succ_apply' G k x).symm
  · intro y hy hyx
    calc y = G^[k + 1] y := (Function.iterate_fixed hy (k + 1)).symm
      _ ≤ G^[k + 1] x := monotone_iterate hmono _ hyx

end Deflation

section Projection

variable {α : Type u} [CompletePartialOrder α] [IsAlgebraic α]

/-- **Bifiniteness is inherited by the image of a projection.** Plotkin's closure
of the bifinite domains under projections, at the level of bases.

Only `p (p x) = p x` and `p x ⊑ x` are used — `im(p)` being a domain is never
needed, so this is stated for a bare `IsProjection` and specializes to `Fp α`
below. -/
theorem isBifinite_range_of_isProjection (hb : IsBifinite α) {p : ScottHom α α}
    (hp : IsProjection p) :
    @IsBifinite _ (IsProjection.rangeCompletePartialOrder hp) := by
  letI : CompletePartialOrder ↥(Set.range ⇑p) := IsProjection.rangeCompletePartialOrder hp
  intro u hufin husub
  -- Push `u` into `K(α)` (Lemma 5's first sentence) and expand it to a finite normal `N`.
  obtain ⟨N, hNfin, hN, hNsub⟩ :=
    hb (Subtype.val '' u) (hufin.image _) (by
      rintro _ ⟨y, hy, rfl⟩
      exact hp.isCompactElement_iff.mp (husub hy))
  -- `G = p ∘ p_N`: continuous, below the identity, finite image, **not** idempotent.
  set G : ScottHom α α :=
    ⟨⇑p ∘ normalFun N, ScottContinuous.comp (scottContinuous_normalFun hN) p.scottContinuous⟩
  have hGapp : ∀ x, G x = p (normalFun N x) := fun _ => rfl
  have hGle : ∀ x, G x ≤ x := fun x => (hp.le _).trans (normalFun_le hN x)
  have hnfN : ∀ x, normalFun N x ∈ N := by
    intro x
    have hrangeN : Set.range (normalFun N) = N := by
      have h := SFP.range_normalHom_of_finite hN hNfin
      rwa [coe_normalHom] at h
    have hmem : normalFun N x ∈ Set.range (normalFun N) := Set.mem_range_self x
    rwa [hrangeN] at hmem
  have hGrp : Set.range ⇑G ⊆ Set.range ⇑p := by
    rintro _ ⟨x, rfl⟩
    exact ⟨normalFun N x, (hGapp x).symm⟩
  have hGfin : (Set.range ⇑G).Finite := by
    refine (hNfin.image ⇑p).subset ?_
    rintro _ ⟨x, rfl⟩
    exact ⟨normalFun N x, hnfN x, (hGapp x).symm⟩
  -- The fixed-point set of `G`.
  have hMfin : {y : α | G y = y}.Finite := hGfin.subset fun y hy => ⟨y, hy⟩
  have hMcompact : ∀ y : α, G y = y → IsCompactElement y := by
    intro y hy s v hne hs hlub hyv
    have hdir : DirectedOn (· ≤ ·) (⇑G '' s) := by
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      obtain ⟨c, hc, hac, hbc⟩ := hs a ha b hb
      exact ⟨G c, ⟨c, hc, rfl⟩, G.monotone hac, G.monotone hbc⟩
    have hsubr : ⇑G '' s ⊆ Set.range ⇑G := by
      rintro _ ⟨a, _, rfl⟩
      exact Set.mem_range_self a
    obtain ⟨_, ⟨a, ha, rfl⟩, hmlub⟩ :=
      SFP.exists_mem_isLUB_of_finite (hGfin.subset hsubr) (hne.image _) hdir
    refine ⟨a, ha, ?_⟩
    calc y = G y := hy.symm
      _ ≤ G v := G.monotone hyv
      _ = G a := (G.scottContinuous hne hs hlub).unique hmlub
      _ ≤ a := hGle a
  -- Transport the fixed-point set into `im(p)`.
  refine ⟨Subtype.val ⁻¹' {y : α | G y = y},
    Set.Finite.preimage Subtype.val_injective.injOn hMfin, ⟨?_, ?_⟩, ?_⟩
  · exact fun y hy => hp.isCompactElement_iff.mpr (hMcompact y.val hy)
  · intro x _
    obtain ⟨c, hcfix, hcx, hcr, hcmax⟩ :=
      exists_fixed_le (G := ⇑G) G.monotone hGle hGfin x.val
    refine ⟨⟨⟨c, hGrp hcr⟩, hcfix, hcx⟩, ?_⟩
    rintro a ⟨hafix, hax⟩ b ⟨hbfix, hbx⟩
    exact ⟨⟨c, hGrp hcr⟩, ⟨hcfix, hcx⟩, hcmax a.val hafix hax, hcmax b.val hbfix hbx⟩
  · intro y hy
    show G y.val = y.val
    rw [hGapp, normalFun_of_mem hN (hNsub ⟨y, hy, rfl⟩), hp.apply_of_mem_range y.2]

/-- **`FpImagesBifinite U`, discharged.** Every finitary-projection image of an
algebraic bifinite `U` is bifinite. The `Fp U` membership supplies a projection
and a `Domain` on the image; only the projection is used. -/
theorem fpImagesBifinite_of_isBifinite {U : Type u} [CompletePartialOrder U]
    [IsAlgebraic U] (hb : IsBifinite U) : R47.Agent4.FpImagesBifinite U :=
  fun p => isBifinite_range_of_isProjection hb (mem_Fp.mp p.2).isProjection

/-- **The added `[IsAlgebraic U]` binder costs nothing downstream.** Every
consumer of `FpImagesBifinite` — `R47.Agent4.rep_arrow_of_fpImagesBifinite`,
`rep_strictArrow_of_fpImagesBifinite`,
`domain_range_strictArrowFamily_of_bifinite` — already carries `[Domain U]`,
which extends `IsAlgebraic U`. Recorded as a theorem rather than as prose so the
claim is checkable.

The binder is spent in exactly one place: `scottContinuous_normalFun`, where
`NormalProjection.lean`'s docstring already names algebraicity as "the only place
the argument needs `D` to be algebraic". -/
theorem fpImagesBifinite_at_domain {U : Type u} [CompletePartialOrder U] [Domain U]
    (hb : IsBifinite U) : R47.Agent4.FpImagesBifinite U :=
  fpImagesBifinite_of_isBifinite hb

end Projection

/-! ### At `V` -/

open Colimit Lemma30

/-- **`FpImagesBifinite V`**, unconditionally: `Colimit.isBifinite_V` supplies the
hypothesis and `Colimit.domain_V` the algebraicity. -/
theorem fpImagesBifinite_V : R47.Agent4.FpImagesBifinite V :=
  fpImagesBifinite_of_isBifinite isBifinite_V

/-- **Conjunct 1 of Lemma 30 at `V`, from Theorem 29's second sentence alone.**
r0047's `R47.Agent4.rep_fun_V` with its second hypothesis discharged. No instance
binder is added and no bounded-completeness binder appears. -/
theorem rep_fun_V_of_thm29Second (h : Theorem29SecondAtDomains) :
    IsPRepresentable₂ V PRep.funOp :=
  R47.Agent4.rep_fun_V h fpImagesBifinite_V

/-- **Conjunct 2 of Lemma 30 at `V`, from the same single hypothesis.** -/
theorem rep_strictFun_V_of_thm29Second (h : Theorem29SecondAtDomains) :
    IsPRepresentable₂ V PRep.strictFunOp :=
  R47.Agent4.rep_strictFun_V h fpImagesBifinite_V

/-- **`Lemma30AtV` from `Theorem29Normal` alone — arity 3 down to arity 1.**

r0046's `R46.Agent3.lemma_30_atV_of_thm29Normal_of_arrows` still had to be handed
conjuncts 1 and 2 because `PRepFun.rep_arrow` was this development's only route to
them and it ran through `[BoundedComplete U]`, which
`R45.Agent3.not_boundedComplete_V` refutes under the very hypothesis in play.
r0047 replaced that route at the cost of `FpImagesBifinite V`; the two theorems
above pay that cost, so both conjuncts are now supplied here.

`Lemma30.Lemma30AtV` is therefore open at **exactly one** named proposition,
`Lemma30.Theorem29Normal`. The development's own bounded-completeness obstruction,
the second of the two r0046 recorded, is gone. -/
theorem lemma_30_atV_of_thm29Normal (h : Theorem29Normal) : Lemma30.Lemma30AtV :=
  let h' := theorem_29_secondAtDomains_of_thm29Normal h
  R46.Agent3.lemma_30_atV_of_thm29Normal_of_arrows h
    (rep_fun_V_of_thm29Second h') (rep_strictFun_V_of_thm29Second h')

end ScottDomains.R49.Agent6
