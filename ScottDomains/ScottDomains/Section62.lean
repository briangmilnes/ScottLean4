import ScottDomains.FinitaryProjectionEmbedding
import ScottDomains.MinimalUpperBounds

/-!
# §6.2: Theorem 16's positive form, and Theorem 18's proof architecture

Gunter & Scott, *Semantic Domains*, §6.2, quoted from the source PDF:

> **Theorem 16** If `D` is bifinite, then the poset `Fp(D)` of finitary
> projections on `D` is an algebraic lattice and the inclusion map
> `i : Fp(D) ↪ (D → D)` is an embedding.

The sentence has two conjuncts and this development has settled both, in
opposite directions:

* the first, "`Fp(D)` is an algebraic lattice", is `ScottDomains.thm16`
  (`Skeleton/Section6b.lean`, r0028) — proved;
* the second, "`i : Fp(D) ↪ (D → D)` is an embedding", is **false**, refuted by
  the kernel in `ScottDomains/FinitaryProjectionEmbedding.lean` (r0032) at the
  five-element bifinite domain `TwoMub`.

This file supplies the missing third piece: the **hypothesis under which the
refuted conjunct does hold**, and its proof. The pair of results is then a single
settled statement rather than two loose ends — the conjunct is not simply wrong,
it is wrong at exactly the domains where `S_f` has no greatest normal subposet,
and bounded complete domains are never among them.

## The exact criterion, and what it costs

`FinitaryProjectionEmbedding.lean` records the criterion that diagnoses the
paper's sketch, `Fp.le_iff_fpBasis_subset_stableCompacts`:

> For `p ∈ Fp(D)` with basis `N = im(p) ∩ K(D)`, and `f : D → D` continuous,
> `p ⊑ f` **if and only if** `N ⊆ S_f`, where `S_f = {x ∈ K(D) | x ⊑ f(x)}`.

So a section `s : (D → D) → Fp(D)` of the inclusion exists exactly when, for
every continuous `f`, the normal subposets of `K(D)` contained in `S_f` have a
**greatest** member: that member is `s(f)`'s basis. The paper's sketch instead
builds the least normal set *containing* `S_f`, which is the opposite inclusion;
the two agree only when `S_f` is itself normal.

`HasGreatestStableNormal` below is that condition, stated in the paper's own
vocabulary. Two facts about it are proved here:

1. `thm16_positive` — the condition is **sufficient**. It produces a map
   `s : (D → D) → Fp(D)` with `s ∘ i = id` and `i ∘ s ⊑ id`, monotone. This is
   the literal negation of `TwoMub.not_exists_monotone_projection`, so the two
   statements together are a dichotomy and not a pair of unrelated facts.
2. `hasGreatestStableNormal_of_boundedComplete` — every **bounded complete**
   domain satisfies it, with `S_f` itself the greatest member
   (`stableCompacts_isNormalIn`). Bounded completeness is spent exactly once, on
   the least upper bound `k₁ ⊔ k₂` of two members of `S_f`: `f(k₁ ⊔ k₂)` bounds
   both, so the join is again in `S_f`, which is directedness.

The condition is also **necessary** — `isGreatest_fp_le_of_hasGreatestStableNormal`
runs in the direction that matters, and the refutation supplies the converse
failure — so the hypothesis is not an artifact chosen to make a proof go through.

Under bounded completeness the section is moreover **Scott continuous**
(`scottContinuous_fpOfStable`), so the paper's conjunct holds in full, as an
embedding–projection pair: `thm16_positive_isEmbeddingProjectionPair`. Its
statement is the exact negation of `TwoMub.not_isEmbeddingProjectionPair`,
including the way the inclusion `i` is passed in as a hypothesis with its
defining equation `hi : ∀ p, i p = p.val` — that is how the refutation avoids
committing to a cpo structure on `Fp(D)`, and the positive form matches it so the
two can be read against each other line by line.

Continuity is where the argument uses that `K(D)` consists of compact elements a
second time: for a directed family `T` with least upper bound `f`,
`S_f = ⋃_{g ∈ T} S_g`, because `k ⊑ f(k) = ⨆_{g ∈ T} g(k)` and compactness of `k`
puts `k ⊑ g(k)` for a single `g`. `isLUB_eval_image_of_isLUB` is the bridge.

## Scope

Nothing here restates or re-derives the refutation, which is kernel-checked in
`FinitaryProjectionEmbedding.lean`. `TwoMub` fails `HasGreatestStableNormal`
precisely because `{⊥, a, m₁}` and `{⊥, b, m₁}` are two *maximal* normal
subposets inside `S_{λx.m₁}` with no normal subposet above both — and it is not
bounded complete, which is consistent with the second result above.
-/

namespace ScottDomains.Section62

open ScottDomains ScottDomains.FpEmbedding

variable {α : Type*}

section Sufficient

variable [CompletePartialOrder α] [Domain α]

/-- **The hypothesis under which Theorem 16's second conjunct holds.** For every
continuous `f : D → D`, the normal subposets of `K(D)` contained in
`S_f = {x ∈ K(D) | x ⊑ f(x)}` have a greatest member.

This is the condition the paper's sketch needs and does not have. It is stated as
"greatest", not "maximal": `TwoMub` has maximal ones and no greatest one, which
is exactly the refutation. -/
def HasGreatestStableNormal (α : Type*) [CompletePartialOrder α] [Domain α] : Prop :=
  ∀ f : ScottHom α α, ∃ N : Set α, N ◁ compacts α ∧ N ⊆ stableCompacts f ∧
    ∀ N' : Set α, N' ◁ compacts α → N' ⊆ stableCompacts f → N' ⊆ N

/-- **The hypothesis, transported through Theorem 6.** A greatest normal subposet
inside `S_f` is the same thing as a greatest finitary projection below `f`: the
correspondence `N ↦ p_N` (`toFp`) is an order isomorphism onto `Fp(D)`
(`Fp.le_iff_fpBasis_subset`), and `Fp.le_iff_fpBasis_subset_stableCompacts`
identifies "below `f`" with "basis inside `S_f`".

This is the step that the refutation blocks in the other direction:
`isGreatest_of_section` shows a monotone section forces such a greatest element to
exist, and `TwoMub.not_isGreatest_below_fConst` shows it need not. -/
theorem isGreatest_fp_le_of_hasGreatestStableNormal (h : HasGreatestStableNormal α)
    (f : ScottHom α α) : ∃ p : ↥(Fp α), IsGreatest {q : ↥(Fp α) | q.val ≤ f} p := by
  obtain ⟨N, hN, hNS, hmax⟩ := h f
  refine ⟨toFp hN, ?_, fun q hq => ?_⟩
  · show (toFp hN).val ≤ f
    refine le_of_fpBasis_subset_stableCompacts ?_
    rw [fpBasis_toFp]
    exact hNS
  · refine Fp.le_iff_fpBasis_subset.mpr ?_
    rw [fpBasis_toFp]
    exact hmax _ (fpBasis_isNormalIn q) (fpBasis_subset_stableCompacts hq)

/-- **Theorem 16's second conjunct, positively.** If every `S_f` has a greatest
normal subposet, then the inclusion `i : Fp(D) ↪ (D → D)` *does* have a section
`s` below the identity — the two equations `s ∘ i = id` and `i ∘ s ⊑ id` that make
`(i, s)` an embedding–projection pair, with `s` monotone.

This is the literal negation of `ScottDomains.FpEmbedding.TwoMub.not_exists_monotone_projection`,
which refutes the same three conjuncts at a bifinite `D` where the hypothesis
fails. Read together: the conjunct is equivalent to `HasGreatestStableNormal`, and
bounded complete domains are on the true side of it
(`hasGreatestStableNormal_of_boundedComplete`).

The three components are all read off the greatest element `s f`:
membership gives `i ∘ s ⊑ id`; the upper-bound half applied to `s f ⊑ f ⊑ g`
gives monotonicity; and applied to `p ⊑ p` together with membership it gives
`s (i p) = p` by antisymmetry. -/
theorem thm16_positive (h : HasGreatestStableNormal α) :
    ∃ s : ScottHom α α → ↥(Fp α),
      Monotone s ∧ (∀ p : ↥(Fp α), s p.val = p) ∧ ∀ g : ScottHom α α, (s g).val ≤ g := by
  choose s hs using isGreatest_fp_le_of_hasGreatestStableNormal h
  refine ⟨s, fun f g hfg => ?_, fun p => ?_, fun g => (hs g).1⟩
  · exact (hs g).2 (le_trans (hs f).1 hfg)
  · exact le_antisymm (hs p.val).1 ((hs p.val).2 (le_refl p.val))

end Sufficient

section BoundedComplete

variable [CompletePartialOrder α] [Domain α] [BoundedComplete α]

omit [Domain α] in
/-- **In a bounded complete domain `S_f` is itself normal in `K(D)`.**

`S_f ⊆ K(D)` by definition and `⊥ ∈ S_f` supplies nonemptiness. Directedness
below any `x` is where bounded completeness is spent, once: two members `k₁, k₂`
of `S_f` below `x` are bounded, so `c = k₁ ⊔ k₂` exists; it is compact by
`isCompactElement_of_isLUB_pair`, it is below `x` because `x` bounds the pair, and
it is in `S_f` because `f(c)` is an upper bound of `{k₁, k₂}` — each `kᵢ ⊑ f(kᵢ)`
by membership and `f(kᵢ) ⊑ f(c)` by monotonicity — so the least upper bound `c`
lies below `f(c)`.

This is the exact point at which `TwoMub` differs: there `{a, b}` is bounded but
has no least upper bound, and `S_{λx.m₁} ∩ ↓m₂ = {⊥, a, b}` is not directed.

Countability of `K(D)` is not used, so the statement is `omit [Domain α]`: this is
a fact about bounded complete *algebraic* cpos. -/
theorem stableCompacts_isNormalIn (f : ScottHom α α) : stableCompacts f ◁ compacts α := by
  refine ⟨fun _ hk => hk.1, fun x _ => ⟨⟨⊥, ⟨isCompactElement_bot, bot_le⟩, bot_le⟩, ?_⟩⟩
  rintro k₁ ⟨⟨hk₁c, hk₁f⟩, hk₁x⟩ k₂ ⟨⟨hk₂c, hk₂f⟩, hk₂x⟩
  have hbdd : BddAbove ({k₁, k₂} : Set α) := by
    refine ⟨x, ?_⟩
    rintro y (rfl | rfl)
    · exact hk₁x
    · exact hk₂x
  have hlub : IsLUB ({k₁, k₂} : Set α) (sSup ({k₁, k₂} : Set α)) := isLUB_sSup_of_bddAbove hbdd
  have h₁ : k₁ ≤ sSup ({k₁, k₂} : Set α) := hlub.1 (Set.mem_insert _ _)
  have h₂ : k₂ ≤ sSup ({k₁, k₂} : Set α) := hlub.1 (Set.mem_insert_of_mem _ rfl)
  refine ⟨sSup ({k₁, k₂} : Set α), ⟨⟨isCompactElement_of_isLUB_pair hk₁c hk₂c hlub, ?_⟩, ?_⟩,
    h₁, h₂⟩
  · refine hlub.2 ?_
    rintro y (rfl | rfl)
    · exact hk₁f.trans (f.monotone h₁)
    · exact hk₂f.trans (f.monotone h₂)
  · refine hlub.2 ?_
    rintro y (rfl | rfl)
    · exact hk₁x
    · exact hk₂x

/-- **Every bounded complete domain satisfies the hypothesis**, with `S_f` itself
the greatest normal subposet inside `S_f` — a set is trivially the greatest subset
of itself once it is known to be normal.

Note that this is not a vacuous instance of the hypothesis: bounded complete
domains are bifinite (`ScottDomains.prop15`), so Theorem 16's own hypothesis holds
at them and its second conjunct is a real statement there. -/
theorem hasGreatestStableNormal_of_boundedComplete : HasGreatestStableNormal α :=
  fun f => ⟨stableCompacts f, stableCompacts_isNormalIn f, subset_rfl, fun _ _ hN' => hN'⟩

/-- The section itself, `f ↦ p_{S_f}`. Under bounded completeness this is the
paper's `f ↦ p_{N_f}` with the inclusion repaired: `N_f` is `S_f`, not the least
normal set containing it, and the two coincide here because `S_f` is already
normal. -/
noncomputable def fpOfStable (f : ScottHom α α) : ↥(Fp α) := toFp (stableCompacts_isNormalIn f)

@[simp] theorem fpBasis_fpOfStable (f : ScottHom α α) :
    fpBasis (fpOfStable f) = stableCompacts f := fpBasis_toFp _

/-- `i ∘ s ⊑ id`: the projection determined by `S_f` lies below `f`, by the
criterion, since its basis is `S_f`. -/
theorem fpOfStable_le (f : ScottHom α α) : (fpOfStable f).val ≤ f :=
  le_of_fpBasis_subset_stableCompacts (by rw [fpBasis_fpOfStable])

/-- `S_f` grows with `f`, so `f ↦ p_{S_f}` is monotone. -/
theorem monotone_fpOfStable : Monotone (fpOfStable (α := α)) := by
  intro f g hfg
  refine Fp.le_iff_fpBasis_subset.mpr ?_
  rw [fpBasis_fpOfStable, fpBasis_fpOfStable]
  rintro k ⟨hkc, hkf⟩
  exact ⟨hkc, hkf.trans (hfg k)⟩

/-- **The section is Scott continuous.** For a nonempty directed `d` with least
upper bound `f`, `S_f = ⋃_{g ∈ d} S_g`.

`⊇` is monotonicity. `⊆` is the only place compactness of the basis is spent a
second time: `k ∈ S_f` means `k ⊑ f(k)`, and `isLUB_eval_image_of_isLUB` makes
`f(k)` the least upper bound of the directed set `{g(k) | g ∈ d}`, so compactness
of `k` produces a single `g ∈ d` with `k ⊑ g(k)`, that is `k ∈ S_g`.

Translated through `Fp.le_iff_fpBasis_subset` — under which the order on `Fp(D)`
*is* inclusion of bases — that union statement is exactly the least-upper-bound
property of `p_{S_f}` over the image of `d`. -/
theorem scottContinuous_fpOfStable : ScottContinuous (fpOfStable (α := α)) := by
  intro d hne hd f hf
  refine ⟨?_, fun q hq => ?_⟩
  · rintro _ ⟨g, hg, rfl⟩
    exact monotone_fpOfStable (hf.1 hg)
  · refine Fp.le_iff_fpBasis_subset.mpr ?_
    rw [fpBasis_fpOfStable]
    rintro k ⟨hkc, hkf⟩
    obtain ⟨_, ⟨g, hg, rfl⟩, hkg⟩ :=
      hkc ((fun h : ScottHom α α => h k) '' d) (f k) (hne.image _)
        (ScottHom.directedOn_eval_image hd k) (ScottHom.isLUB_eval_image_of_isLUB hd hf k) hkf
    have hle : fpBasis (fpOfStable g) ⊆ fpBasis q :=
      Fp.le_iff_fpBasis_subset.mp (hq ⟨g, hg, rfl⟩)
    refine hle ?_
    rw [fpBasis_fpOfStable]
    exact ⟨hkc, hkg⟩

/-- The section as a morphism of the function space. -/
noncomputable def fpSection : ScottHom (ScottHom α α) ↥(Fp α) :=
  ⟨fpOfStable, scottContinuous_fpOfStable⟩

/-- **Theorem 16's second conjunct, in full, over a bounded complete domain.** The
inclusion `i : Fp(D) ↪ (D → D)` *is* an embedding: `(i, fpSection)` is an
embedding–projection pair in the paper's §3.1 sense,
`ScottHom.IsEmbeddingProjectionPair`.

The statement is the exact negation of
`ScottDomains.FpEmbedding.TwoMub.not_isEmbeddingProjectionPair`, down to the way
the inclusion is supplied — as a `ScottHom` `i` together with its defining
equation `hi : ∀ p, i p = p.val`. Neither side assumes a cpo structure on
`Fp(D)`; `ScottHom` needs only preorders, and `↥(Fp α)` carries the pointwise
order it inherits as a subtype.

The round trip `fpSection (i p) = p` is the sketch's own correct half: for a
finitary projection `p`, `S_p = im(p) ∩ K(D)` (`stableCompacts_val`), so the two
bases agree and `Fp.le_iff_fpBasis_subset` gives equality by antisymmetry. -/
theorem thm16_positive_isEmbeddingProjectionPair
    (i : ScottHom ↥(Fp α) (ScottHom α α)) (hi : ∀ p, i p = p.val) :
    ScottHom.IsEmbeddingProjectionPair i (fpSection (α := α)) := by
  refine ⟨fun p => ?_, fun g => ?_⟩
  · show fpOfStable (i p) = p
    have hb : fpBasis (fpOfStable (i p)) = fpBasis p := by
      rw [fpBasis_fpOfStable, hi p, stableCompacts_val]
    exact le_antisymm (Fp.le_iff_fpBasis_subset.mpr hb.subset)
      (Fp.le_iff_fpBasis_subset.mpr hb.symm.subset)
  · show i (fpOfStable g) ≤ g
    rw [hi (fpOfStable g)]
    exact fpOfStable_le g

end BoundedComplete

end ScottDomains.Section62
