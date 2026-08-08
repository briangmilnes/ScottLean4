import ScottDomains.FinitaryProjectionPoset
-- `PowerdomainRep.repOf` and `repRangeOrderIso`: the conjugation scheme
-- `R(C) = gr ∘ C ∘ fn` and the isomorphism `im(R(C)) ≅ im(C)`, both of which are
-- stated there without any closure hypothesis and so serve the projection case
-- unchanged. This import also brings `Cpo` and `IsRepresentable`.
import ScottDomains.Powerdomain.Universal

/-!
# §7.3: p-representability, over `Fp(U)`

Gunter & Scott, *Semantic Domains*, §7.3, quoted from the source PDF:

> Let us say that an operator `F` on cpo's is **p-representable over a cpo `U`**
> if and only if there is a continuous function `R_F` which completes the
> following diagram (up to isomorphism):
>
> > `Cpo's --F--> Cpo's`
> > `  ↑ im         ↑ im`
> > `Fp(U) --R_F--> Fp(U)`
>
> Since there will be no chance of confusion, let us just use the term
> "representable" for "p-representable" for the remainder of this section. Since
> `Fp(U)` is a cpo we can solve domain equations in the same way we did before
> provided we can find domains over which the necessary operators can be
> represented.

## Why this is not `IsRepresentable`

`ScottDomains.IsRepresentable` (`UniversalDomain.lean`) is §7's *first* notion:
the same square drawn with `Fc(U)`, the finitary **closures**, down both sides.
`IsPRepresentable` draws it with `Fp(U)`, the finitary **projections**. The two
posets sit on opposite sides of the identity — `r ∈ Fc(U)` means `r ∘ r = r ⊒ id`
and `p ∈ Fp(U)` means `p ∘ p = p ⊑ id` — so they intersect in exactly one point:
`eq_id_of_mem_Fp_of_mem_Fc` shows that anything both a finitary projection and a
finitary closure is `id`. A representing map for one notion is therefore not a
representing map for the other, and the paper's *"there will be no chance of
confusion"* holds only inside §7.3, where the older notion is not in play.

This matters for **Lemma 28 versus Lemma 30**. Lemma 28 lists `→, ⇸, ×, ⊗, +, ⊕,
()⊥, ()♯, ()♭` over §7.3's `U`; Lemma 30 is the same nine plus `()♮` over §7.4's
bifinite `V`. **Both are the `Fp` notion.** An earlier version of this paragraph
called Lemma 28 the `Fc` notion; that is wrong, and §7.3's own *"let us just use
the term 'representable' for 'p-representable' for the remainder of this
section"* settles it — Lemma 28 stands four paragraphs after that sentence and
inside the same subsection. `PRep.Lemma28` is accordingly built from
`IsPRepresentable`. Stating either lemma with the wrong class produces a theorem
that compiles and is not the paper's, which is why the correction is recorded
here rather than quietly applied: the wrong reading survived two rounds.

## What is here and what is not

`IsPRepresentable` and `IsPRepresentable₂` are the definitions, and
`isProjection_repOf` is the projection half of the paper's own recipe for a
representing map:

> As with most of the other operators, to get a representation for `()♮`, take a
> pair of continuous functions `♮⁻ : V → V♮`, `♮⁺ : V♮ → V` such that
> `♮⁻ ∘ ♮⁺ = id` and `♮⁺ ∘ ♮⁻ ⊑ id`. Then `R♮(p) = ♮⁺ ∘ (p♮) ∘ ♮⁻` is a
> representation for the convex powerdomain operator.

The conjugation `R(C) = gr ∘ C ∘ fn` and the isomorphism `im(R(C)) ≅ im(C)` are
already in `Powerdomain/Universal.lean`, stated with no closure hypothesis, so
only one obligation is new: that `R(C)` is a *projection* when `C` is. Note the
second condition on the pair points the other way here — `gr ∘ fn ⊑ id`, where
the `Fc` case has `id ⊑ gr ∘ fn`.

**Lemma 30 is stated in full and proved for none of its ten operators.**
`LemThirty.Lemma30` is a ten-fold conjunction and `lemma30_of` takes ten named
hypotheses, so the count is kernel-checked; nothing is stubbed with `sorry`.

An earlier version of this paragraph said `V` "does not exist in this
development". **It does** — `Colimit.V`, built in r0036 as the ω-colimit of the
stage tower, with `Colimit.domain_V`, `Colimit.isBifinite_V` and
`Colimit.isoPlus : V ≃o Plus V`. The colimit is taken at the level of countable
posets and `IdealCompletion.thm11` applied once at the end, so it needed neither
[Gun87] nor a cpo construction. What remains open is Theorem 29's *second*
sentence, reduced to the single named proposition `LemThirty.Thm29Normal`.
-/

namespace ScottDomains.BifiniteUniversal

open ScottDomains

universe u

/-! ## `Fp(U)` and the p-representability square -/

section Defs

variable {U : Type u} [CompletePartialOrder U]

/-- `im(p)` as a cpo, for a finitary projection `p`. The companion of
`ClosurePoset.image`, built from `IsProjection.rangeCompletePartialOrder` rather
than `IsClosure.rangeCompletePartialOrder`. -/
def FpImage (p : ↥(Fp U)) : Cpo.{u} :=
  ⟨↥(Set.range ⇑p.val),
    ScottHom.IsProjection.rangeCompletePartialOrder
      (ScottHom.IsFinitaryProjection.isProjection (mem_Fp.mp p.2))⟩

@[simp] theorem FpImage_carrier (p : ↥(Fp U)) :
    (FpImage p).carrier = ↥(Set.range ⇑p.val) := rfl

/-- **P-representable** (Gunter & Scott, §7.3): the square with `im : Fp(U) →
Cpo's` down both sides, `F` across the top and `R_F` across the bottom, commuting
up to `≃o`.

Distinct from `ScottDomains.IsRepresentable`, which is the same square over
`Fc(U)`; see the module docstring and `eq_id_of_mem_Fp_of_mem_Fc`. -/
def IsPRepresentable (U : Type u) [CompletePartialOrder U] (F : Cpo.{u} → Cpo.{u}) : Prop :=
  ∃ R : ↥(Fp U) → ↥(Fp U), ScottContinuous R ∧
    ∀ p : ↥(Fp U), Nonempty ((FpImage (R p)).carrier ≃o (F (FpImage p)).carrier)

/-- **P-representable**, binary case, the shape Lemma 30's `→`, `×`, `⊗`, `+`
and `⊕` conjuncts need. Continuity of `R` is with respect to the product order on
`Fp(U) × Fp(U)`. -/
def IsPRepresentable₂ (U : Type u) [CompletePartialOrder U]
    (F : Cpo.{u} → Cpo.{u} → Cpo.{u}) : Prop :=
  ∃ R : ↥(Fp U) × ↥(Fp U) → ↥(Fp U), ScottContinuous R ∧
    ∀ q : ↥(Fp U) × ↥(Fp U),
      Nonempty ((FpImage (R q)).carrier ≃o (F (FpImage q.1) (FpImage q.2)).carrier)

/-- **`Fp(U)` and `Fc(U)` meet only at the identity.** A finitary projection
satisfies `p ⊑ id` and a finitary closure `id ⊑ r`, so anything in both is `id`
by antisymmetry, pointwise.

This is the precise sense in which p-representability is a different notion:
outside the single point `id` the two posets the square is drawn over are
disjoint, so no representing map can be reused between them. -/
theorem eq_id_of_mem_Fp_of_mem_Fc {r : ScottHom U U} (hp : r ∈ Fp U) (hc : r ∈ Fc U) :
    r = ScottHom.id :=
  ScottHom.ext fun x =>
    le_antisymm (ScottHom.IsFinitaryProjection.isProjection (mem_Fp.mp hp) |>.le x)
      ((mem_Fc.mp hc).isClosure.le_apply x)

end Defs

/-! ## The paper's recipe, at a projection

`R(C) = gr ∘ C ∘ fn` for a pair `fn : U → V`, `gr : V → U` with
`fn ∘ gr = id` and `gr ∘ fn ⊑ id`. The definition and the isomorphism
`im(R(C)) ≅ im(C)` are `PowerdomainRep.repOf` and
`PowerdomainRep.repRangeOrderIso`, which assume nothing about `C`; the one new
obligation is idempotence and `⊑ id`. -/

section Scheme

open PowerdomainRep

variable {U V : Type u} [CompletePartialOrder U] [CompletePartialOrder V]
variable {fn : ScottHom U V} {gr : ScottHom V U}

/-- **`R(C)` is a projection whenever `C` is.** Idempotence deletes the inner
pair by `fn ∘ gr = id` and collapses the rest by idempotence of `C`, exactly as
in the closure case; the inequality is the only step that differs — `C ⊑ id`
pushes through `gr`'s monotonicity and then `gr ∘ fn ⊑ id` finishes, where the
closure case ends with `id ⊑ gr ∘ fn`. -/
theorem isProjection_repOf (hfg : ∀ y, fn (gr y) = y) (hgf : ∀ x, gr (fn x) ≤ x)
    {C : ScottHom V V} (hC : ScottHom.IsProjection C) :
    ScottHom.IsProjection (repOf fn gr C) := by
  refine ⟨fun x => ?_, fun x => ?_⟩
  · show gr (C (fn (gr (C (fn x))))) = gr (C (fn x))
    rw [hfg, hC.idem]
  · exact (gr.monotone (hC.le (fn x))).trans (hgf x)

end Scheme

end ScottDomains.BifiniteUniversal
