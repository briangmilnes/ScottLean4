import ScottDomains.ClosureProperties.StrictFunction

/-!
# Lemma 17's function-space conjuncts without `[BoundedComplete β]`

`ClosureProperties.lean:54` records `[BoundedComplete β]` on `lemma_17_fun` and
`lemma_17_strictFun` as **"a real open item, not a formality"**. This file removes
it. The binder is not an artifact of Lemma 17; it is an artifact of the *route*
the development took to the conjunct — through Theorem 7's step-function
decomposition of a compact function (`CompactFunction.lean`,
`exists_finite_isLUB_of_isCompactElement`), whose directedness argument
(`directedOn_finiteJoinsBelow`) is the sole consumer of bounded completeness.

## The route taken here

Gunter & Scott's own §6.2 argument names the finitary projections
`(q, p)(f) = q ∘ f ∘ p` directly and never decomposes a compact function. Written
against `IsBifinite` as the Plotkin condition on the basis, it is:

* `approx f` is the set of values `(p_{N₂}, p_{N₁})(f)` as `N₁ ◁ K(D)` and
  `N₂ ◁ K(E)` range over the **finite** normal subposets.
* It is nonempty (`IsPlotkinOrder.exists_finite_normal_empty` on each side) and
  directed (`IsBifinite` merges `N₁ ∪ N₁'` into one finite normal subposet, and
  `normalHom_mono` plus `compHom_mono` push the two members below the merge).
* Its least upper bound is `f` (`isLUB_approx`). This is the only step with
  content, and it spends algebraicity of `D` and of `E` — never bounded
  completeness. Given a compact `e ≤ f x`, continuity of `f` over
  `compactsBelow x` produces a compact `k ≤ x` with `e ≤ f k`; putting `k` into a
  finite normal `N₁` and `e` into a finite normal `N₂` makes
  `e ≤ p_{N₂}(f(p_{N₁} x))`.
* A compact `f` therefore satisfies `(p_{N₂}, p_{N₁})(f) = f` for some finite
  normal pair (`exists_fixing`), and the fixing is inherited by every larger
  normal pair — which is what lets one pair serve a whole finite `u`.

Nothing below mentions `stepFun`, `IsStepPair` or `stepsBelow`.

## What this buys beyond Lemma 17

`IsAlgebraic (ScottHom α β)` (`FunctionSpaceDomain.lean:121`) and hence
`Domain (ScottHom α β)` (`FunctionSpaceCountable.lean:122`) also carry
`[BoundedComplete β]`. `isLUB_approx` and the merge argument discharge both of
those for **bifinite** operands as well, which is what `Theorem29SecondAtDomains`
needs at `E := ScottHom V V`. Those are proved in `A4FunctionSpaceBifinite.lean`.

Every theorem here is stated with `IsBifinite α` and `IsBifinite β` as explicit
hypotheses and **no instance binder beyond `[Domain α] [Domain β]`**, which
`lemma_17_fun` already carries.
-/

namespace ScottDomains.R47.Agent4

open ScottDomains ScottHom

variable {α β : Type*} [CompletePartialOrder α] [CompletePartialOrder β]

/-! ### `(q, p)` is monotone in both arguments -/

/-- `(q, p)(f) = q ∘ f ∘ p` is monotone in `p` and in `q` separately, hence in
the pair. This is what makes the family of finitary projections directed once the
family of finite normal subposets is directed under `⊆`. -/
theorem compHom_mono {p p' : ScottHom α α} {q q' : ScottHom β β}
    (hp : p ≤ p') (hq : q ≤ q') (f : ScottHom α β) :
    compHom p q f ≤ compHom p' q' f := by
  intro x
  show q (f (p x)) ≤ q' (f (p' x))
  exact (ScottHom.le_def.mp hq (f (p x))).trans
    (q'.monotone (f.monotone (ScottHom.le_def.mp hp x)))

section Approx

variable [Domain α] [Domain β]

/-! ### The directed family of finitary projections applied to `f` -/

/-- `approx f = {(p_{N₂}, p_{N₁})(f) | N₁ ◁ K(D), N₂ ◁ K(E) finite}`.

The normality proofs are existentially bound inside the set because `normalHom`
consumes them; `IsNormalIn` is a `Prop`, so two proofs of the same normality give
the same `normalHom`. -/
def approx (f : ScottHom α β) : Set (ScottHom α β) :=
  {g | ∃ (N₁ : Set α) (N₂ : Set β) (hN₁ : N₁ ◁ compacts α) (hN₂ : N₂ ◁ compacts β),
    N₁.Finite ∧ N₂.Finite ∧ compHom (normalHom hN₁) (normalHom hN₂) f = g}

/-- `approx f` is nonempty: a Plotkin order has a finite normal subposet above
the empty set, on each side. -/
theorem approx_nonempty (h₁ : IsBifinite α) (h₂ : IsBifinite β) (f : ScottHom α β) :
    (approx f).Nonempty := by
  obtain ⟨N₁, hfin₁, hN₁⟩ := IsPlotkinOrder.exists_finite_normal_empty h₁
  obtain ⟨N₂, hfin₂, hN₂⟩ := IsPlotkinOrder.exists_finite_normal_empty h₂
  exact ⟨_, N₁, N₂, hN₁, hN₂, hfin₁, hfin₂, rfl⟩

/-- `approx f` is directed. The Plotkin condition merges the two normal subposets
on each side into one finite normal subposet containing both; `normalHom_mono`
and `compHom_mono` then place both members below the merge's value. -/
theorem directedOn_approx (h₁ : IsBifinite α) (h₂ : IsBifinite β) (f : ScottHom α β) :
    DirectedOn (· ≤ ·) (approx f) := by
  rintro _ ⟨N₁, N₂, hN₁, hN₂, hfin₁, hfin₂, rfl⟩ _ ⟨M₁, M₂, hM₁, hM₂, hgin₁, hgin₂, rfl⟩
  obtain ⟨P₁, hP₁fin, hP₁, hP₁sub⟩ :=
    h₁ (N₁ ∪ M₁) (hfin₁.union hgin₁) (Set.union_subset hN₁.subset hM₁.subset)
  obtain ⟨P₂, hP₂fin, hP₂, hP₂sub⟩ :=
    h₂ (N₂ ∪ M₂) (hfin₂.union hgin₂) (Set.union_subset hN₂.subset hM₂.subset)
  refine ⟨compHom (normalHom hP₁) (normalHom hP₂) f,
    ⟨P₁, P₂, hP₁, hP₂, hP₁fin, hP₂fin, rfl⟩, ?_, ?_⟩
  · exact compHom_mono (normalHom_mono hN₁ hP₁ fun _ hx => hP₁sub (Or.inl hx))
      (normalHom_mono hN₂ hP₂ fun _ hx => hP₂sub (Or.inl hx)) f
  · exact compHom_mono (normalHom_mono hM₁ hP₁ fun _ hx => hP₁sub (Or.inr hx))
      (normalHom_mono hM₂ hP₂ fun _ hx => hP₂sub (Or.inr hx)) f

/-- **`f = ⨆ {(p_{N₂}, p_{N₁})(f)}`.** The substantive step, and the one the
step-function route spent bounded completeness on.

Upper bound: each `(q, p)` is a projection, so `(q,p)(f) ≤ f`.

Least: let `g` bound the family and fix `x`. By algebraicity of `E` it suffices
to put every compact `e ≤ f x` below `g x`. Continuity of `f` over the directed
`compactsBelow x` and compactness of `e` give a compact `k ≤ x` with `e ≤ f k`.
Choose finite normal `N₁ ∋ k` and `N₂ ∋ e`. Then `k ≤ p_{N₁} x`, so
`e ≤ f k ≤ f (p_{N₁} x)`, and `e ∈ N₂` gives `e ≤ p_{N₂}(f(p_{N₁} x))`, which is
the family's value at `x` and hence `≤ g x`. -/
theorem isLUB_approx (h₁ : IsBifinite α) (h₂ : IsBifinite β) (f : ScottHom α β) :
    IsLUB (approx f) f := by
  constructor
  · rintro _ ⟨N₁, N₂, hN₁, hN₂, -, -, rfl⟩
    exact (isProjection_compHom (isProjection_normalHom hN₁) (isProjection_normalHom hN₂)).le f
  · intro g hg x
    refine (IsAlgebraic.isLUB_compactsBelow (f x)).2 ?_
    rintro e ⟨he, hef⟩
    have hdir := IsAlgebraic.directedOn_compactsBelow (α := α) x
    have hfx : IsLUB (⇑f '' compactsBelow x) (f x) :=
      f.scottContinuous (compactsBelow_nonempty x) hdir (IsAlgebraic.isLUB_compactsBelow x)
    obtain ⟨_, ⟨k, hk, rfl⟩, hek⟩ :=
      he (⇑f '' compactsBelow x) (f x) ((compactsBelow_nonempty x).image _)
        (directedOn_image f hdir) hfx hef
    obtain ⟨N₁, hN₁fin, hN₁, hN₁sub⟩ :=
      h₁ {k} (Set.finite_singleton k) (Set.singleton_subset_iff.mpr hk.1)
    obtain ⟨N₂, hN₂fin, hN₂, hN₂sub⟩ :=
      h₂ {e} (Set.finite_singleton e) (Set.singleton_subset_iff.mpr he)
    have hle : compHom (normalHom hN₁) (normalHom hN₂) f ≤ g :=
      hg ⟨N₁, N₂, hN₁, hN₂, hN₁fin, hN₂fin, rfl⟩
    have hkp : k ≤ normalFun N₁ x := le_normalFun hN₁ (hN₁sub rfl) hk.2
    have hstep : e ≤ normalFun N₂ (f (normalFun N₁ x)) :=
      le_normalFun hN₂ (hN₂sub rfl) (hek.trans (f.monotone hkp))
    exact hstep.trans (ScottHom.le_def.mp hle x)

/-- **A compact `f` is fixed by some finite normal pair, and by every larger
one.** The upward-closure clause is what lets a single pair serve a whole finite
set of compacts: `P ≤ P'` between projections and `P f = f` force `P' f = f`. -/
theorem exists_fixing (h₁ : IsBifinite α) (h₂ : IsBifinite β) {f : ScottHom α β}
    (hf : IsCompactElement f) :
    ∃ (N₁ : Set α) (N₂ : Set β), N₁.Finite ∧ N₂.Finite ∧
      N₁ ⊆ compacts α ∧ N₂ ⊆ compacts β ∧
      ∀ (M₁ : Set α) (M₂ : Set β) (hM₁ : M₁ ◁ compacts α) (hM₂ : M₂ ◁ compacts β),
        N₁ ⊆ M₁ → N₂ ⊆ M₂ → compHom (normalHom hM₁) (normalHom hM₂) f = f := by
  obtain ⟨_, ⟨N₁, N₂, hN₁, hN₂, hfin₁, hfin₂, rfl⟩, hfle⟩ :=
    hf (approx f) f (approx_nonempty h₁ h₂ f) (directedOn_approx h₁ h₂ f)
      (isLUB_approx h₁ h₂ f) le_rfl
  refine ⟨N₁, N₂, hfin₁, hfin₂, hN₁.subset, hN₂.subset, fun M₁ M₂ hM₁ hM₂ hs₁ hs₂ => ?_⟩
  refine le_antisymm
    ((isProjection_compHom (isProjection_normalHom hM₁) (isProjection_normalHom hM₂)).le f) ?_
  exact hfle.trans (compHom_mono (normalHom_mono hN₁ hM₁ hs₁) (normalHom_mono hN₂ hM₂ hs₂) f)

/-- The bare existence half of `exists_fixing`: a compact `f` is in the image of
some `(p_{N₂}, p_{N₁})` with `N₁`, `N₂` finite normal. Used by
`A4FunctionSpaceBifinite.lean` to enumerate `K(D → E)`. -/
theorem exists_normal_fixing (h₁ : IsBifinite α) (h₂ : IsBifinite β) {f : ScottHom α β}
    (hf : IsCompactElement f) :
    ∃ (N₁ : Set α) (N₂ : Set β) (hN₁ : N₁ ◁ compacts α) (hN₂ : N₂ ◁ compacts β),
      N₁.Finite ∧ N₂.Finite ∧ compHom (normalHom hN₁) (normalHom hN₂) f = f := by
  obtain ⟨_, ⟨N₁, N₂, hN₁, hN₂, hfin₁, hfin₂, rfl⟩, hfle⟩ :=
    hf (approx f) f (approx_nonempty h₁ h₂ f) (directedOn_approx h₁ h₂ f)
      (isLUB_approx h₁ h₂ f) le_rfl
  exact ⟨N₁, N₂, hN₁, hN₂, hfin₁, hfin₂,
    le_antisymm ((isProjection_compHom (isProjection_normalHom hN₁)
      (isProjection_normalHom hN₂)).le f) hfle⟩

/-- Every member of `approx f` is a compact element below `f`: it lies in the
image of a projection with finite image (`finite_range_compHom` of two
`finite_range_normalHom`s), and such an image consists of compacts. -/
theorem approx_subset_compactsBelow (f : ScottHom α β) : approx f ⊆ compactsBelow f := by
  rintro _ ⟨N₁, N₂, hN₁, hN₂, hfin₁, hfin₂, rfl⟩
  have hp := isProjection_normalHom hN₁
  have hq := isProjection_normalHom hN₂
  have hP := isProjection_compHom hp hq
  have hPfin := finite_range_compHom hp hq (finite_range_normalHom hN₁ hfin₁)
    (finite_range_normalHom hN₂ hfin₂)
  exact ⟨isCompactElement_of_mem_range_of_finite hP hPfin (Set.mem_range_self f), hP.le f⟩

/-! ### The engine, and Lemma 17's two function-space conjuncts -/

/-- **`ClosureProperties.exists_finite_projection_fixing` without
`[BoundedComplete β]`.** Same conclusion, same argument order; the proof is
`exists_fixing` for each `f ∈ u` followed by one merge of the finitely many
witnesses through the Plotkin condition. -/
theorem exists_finite_projection_fixing (h₁ : IsBifinite α) (h₂ : IsBifinite β)
    {u : Set (ScottHom α β)} (hu : u.Finite) (husub : u ⊆ compacts (ScottHom α β)) :
    ∃ (p : ScottHom α α) (q : ScottHom β β), IsProjection p ∧ IsProjection q ∧
      p (⊥ : α) = ⊥ ∧ q (⊥ : β) = ⊥ ∧ (Set.range ⇑(compHom p q)).Finite ∧
      ∀ f ∈ u, compHom p q f = f := by
  classical
  have key : ∀ f : ScottHom α β, f ∈ u →
      ∃ (N₁ : Set α) (N₂ : Set β), N₁.Finite ∧ N₂.Finite ∧
        N₁ ⊆ compacts α ∧ N₂ ⊆ compacts β ∧
        ∀ (M₁ : Set α) (M₂ : Set β) (hM₁ : M₁ ◁ compacts α) (hM₂ : M₂ ◁ compacts β),
          N₁ ⊆ M₁ → N₂ ⊆ M₂ → compHom (normalHom hM₁) (normalHom hM₂) f = f :=
    fun f hf => exists_fixing h₁ h₂ (husub hf)
  choose! K₁ K₂ hfin₁ hfin₂ hsub₁ hsub₂ hfix using key
  have hU₁fin : (⋃ f ∈ u, K₁ f).Finite := hu.biUnion hfin₁
  have hU₂fin : (⋃ f ∈ u, K₂ f).Finite := hu.biUnion hfin₂
  have hU₁sub : (⋃ f ∈ u, K₁ f) ⊆ compacts α := by
    intro a ha
    obtain ⟨f, hf, haf⟩ := Set.mem_iUnion₂.mp ha
    exact hsub₁ f hf haf
  have hU₂sub : (⋃ f ∈ u, K₂ f) ⊆ compacts β := by
    intro b hb
    obtain ⟨f, hf, hbf⟩ := Set.mem_iUnion₂.mp hb
    exact hsub₂ f hf hbf
  obtain ⟨M₁, hM₁fin, hM₁, hM₁sup⟩ := h₁ _ hU₁fin hU₁sub
  obtain ⟨M₂, hM₂fin, hM₂, hM₂sup⟩ := h₂ _ hU₂fin hU₂sub
  have hp : IsProjection (normalHom hM₁) := isProjection_normalHom hM₁
  have hq : IsProjection (normalHom hM₂) := isProjection_normalHom hM₂
  refine ⟨normalHom hM₁, normalHom hM₂, hp, hq,
    ClosureProperties.normalHom_bot hM₁, ClosureProperties.normalHom_bot hM₂,
    finite_range_compHom hp hq (finite_range_normalHom hM₁ hM₁fin)
      (finite_range_normalHom hM₂ hM₂fin), fun f hf => ?_⟩
  exact hfix f hf M₁ M₂ hM₁ hM₂ (fun a ha => hM₁sup (Set.mem_biUnion hf ha))
    (fun b hb => hM₂sup (Set.mem_biUnion hf hb))

/-- **Lemma 17, function-space conjunct, with `[BoundedComplete β]` removed.**
Compare `ClosureProperties.lemma_17_fun`, whose binders are
`[Domain α] [Domain β] [BoundedComplete β]`; this statement's are
`[Domain α] [Domain β]`. -/
theorem lemma_17_fun (h₁ : IsBifinite α) (h₂ : IsBifinite β) :
    IsBifinite (ScottHom α β) := by
  intro u hu husub
  obtain ⟨p, q, hp, hq, -, -, hPfin, hfix⟩ :=
    exists_finite_projection_fixing h₁ h₂ hu husub
  have hP : IsProjection (compHom p q) := isProjection_compHom hp hq
  exact ⟨Set.range ⇑(compHom p q), hPfin, isNormalIn_range_of_finite hP hPfin,
    fun f hf => ⟨f, hfix f hf⟩⟩

/-- **Lemma 17, strict-function-space conjunct, with `[BoundedComplete β]`
removed.** The packaging is `ClosureProperties.lemma_17_strictFun`'s verbatim; only
the engine underneath it changed. -/
theorem lemma_17_strictFun (h₁ : IsBifinite α) (h₂ : IsBifinite β) :
    IsBifinite (StrictHom α β) := by
  intro u hu husub
  have huvfin : (Subtype.val '' u : Set (ScottHom α β)).Finite := hu.image _
  have huvsub : (Subtype.val '' u : Set (ScottHom α β)) ⊆ compacts (ScottHom α β) := by
    rintro _ ⟨f, hf, rfl⟩
    exact ClosureProperties.isCompactElement_val_of_isCompactElement (husub hf)
  obtain ⟨p, q, hp, hq, hpbot, hqbot, hPfin, hfix⟩ :=
    exists_finite_projection_fixing h₁ h₂ huvfin huvsub
  have hP : IsProjection (compHom p q) := isProjection_compHom hp hq
  refine ⟨Subtype.val ⁻¹' Set.range ⇑(compHom p q), hPfin.preimage Subtype.val_injective.injOn,
    ⟨?_, ?_⟩, ?_⟩
  · intro y hy
    exact ClosureProperties.isCompactElement_of_isCompactElement_val
      (isCompactElement_of_mem_range_of_finite hP hPfin hy)
  · intro x _
    refine ⟨⟨⟨compHom p q x.val, ClosureProperties.isStrict_compHom hpbot hqbot x.2⟩,
      Set.mem_range_self _, Set.mem_Iic.mpr (hP.le x.val)⟩, ?_⟩
    rintro a ⟨ha, hax⟩ b ⟨hb, hbx⟩
    refine ⟨⟨compHom p q x.val, ClosureProperties.isStrict_compHom hpbot hqbot x.2⟩,
      ⟨Set.mem_range_self _, Set.mem_Iic.mpr (hP.le x.val)⟩, ?_, ?_⟩
    · exact (hP.apply_of_mem_range ha).symm.trans_le ((compHom p q).monotone hax)
    · exact (hP.apply_of_mem_range hb).symm.trans_le ((compHom p q).monotone hbx)
  · intro f hf
    exact ⟨f.val, hfix f.val ⟨f, hf, rfl⟩⟩

end Approx

/-! ### The bar was not lowered

The two theorems below are the kernel's record that the binder-free statements
**imply** the ones the development already has. They are one-line instantiations;
their content is that no hypothesis was traded for the one removed. -/

/-- `lemma_17_fun` above implies `ClosureProperties.lemma_17_fun`'s statement. -/
theorem lemma_17_fun_imp_old [Domain α] [Domain β] [BoundedComplete β]
    (h₁ : IsBifinite α) (h₂ : IsBifinite β) : IsBifinite (ScottHom α β) :=
  lemma_17_fun h₁ h₂

/-- `lemma_17_strictFun` above implies `ClosureProperties.lemma_17_strictFun`'s
statement. -/
theorem lemma_17_strictFun_imp_old [Domain α] [Domain β] [BoundedComplete β]
    (h₁ : IsBifinite α) (h₂ : IsBifinite β) : IsBifinite (StrictHom α β) :=
  lemma_17_strictFun h₁ h₂

end ScottDomains.R47.Agent4
