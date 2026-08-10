import ScottDomains.FinitaryProjectionPoset

/-!
# Theorem 14: Plotkin's SFP characterization

Gunter & Scott, *Semantic Domains*, §6 and §6.1, read from the page content
stream of `papers/Gunter Scott 1990.pdf` (PDF pages 30–31, printed 29–30):

> **Definition:** Let `D` be a cpo. Let `M` be the set of finitary projections
> with finite image. Then `D` is said to be bifinite if `M` is countable,
> directed and `⨆M = id`. ∎

> **Theorem 14** The following are equivalent for any cpo `D`.
> 1. `D` is bifinite.
> 2. `D` is a domain and `K(D)` is a Plotkin order. ∎

The paper gives its own sketch of the forward direction three sentences above
the theorem, and this file follows it line for line:

> … it follows from properties of finitary projections that we mentioned
> earlier that whenever `p : D → D` is a finitary projection and `im(p)` is
> finite, then `im(p) ⊆ K(D)`. From this, together with the fact that the set
> `M` is directed and `⨆M = id`, it is possible to show `D` is a domain with
> `⋃{im(p) | p ∈ M}` as its basis.

`Skeleton/Recovered.lean` states Theorem 14 and names the paper's `M` as
`finiteImageProjections`; that module imports this one, so the two halves here
are stated against a *characterization* of `M` (`hM : ∀ p, p ∈ M ↔ …`) rather
than against the definition, which keeps the dependency one-way.

## What the four gaps of `thm14`'s r0034 docstring cost

| # | Gap | Outcome |
| -- | --- | ------- |
| 1 | the `FpLattice` machinery is stated at `[Domain α]`, which the forward direction must conclude | **dissolved** — the forward direction needs none of it |
| 2 | `Set.range ⇑(toFp hN) = N` for finite normal `N` | **proved** as `range_normalHom_of_finite` |
| 3 | `IsLUB` in `↥(Fp α)` is weaker than `IsLUB … ScottHom.id` in `ScottHom α α` | **dissolved** — `isLUB_id_of_normalHom_mem` argues in the function space directly, never in `↥(Fp α)` |
| 4 | two finite-combinatorial lemmas | **proved** as `exists_upperBound_of_finite_subset` and `exists_greatest_of_finite` |

Gap 1 turned out to be a false constraint rather than a `variable` move. The
forward direction never touches `toFp`, `fpBasis` or `Fp.le_iff_fpBasis_subset`:
each of those speaks about `im(p) ∩ K(D)`, and on a *finite* image
`im(p) ∩ K(D) = im(p)` (`range_inter_compacts_of_finite`), so the whole
argument can be run on `im(p)` in `D` with no basis coordinate at all. The
measurement asked for by the plan — which of the four `FpLattice` declarations
survive at `[CompletePartialOrder α]` — is therefore moot for Theorem 14;
`toFp` and `fpBasis_toFp` in fact still need `[Domain α]`, because
`isFinitaryProjection_normalHom` spends countability of `K(D)` on the basis of
`im(p_N)`.

Gap 3 was likewise a false constraint. Leastness of `ScottHom.id` above `M` is
proved by algebraicity: an upper bound `b` of `M` dominates `p_{⟨k⟩} x` for
every compact `k ⊑ x`, where `⟨k⟩` is the least finite normal subposet
containing `k`, and `k ⊑ p_{⟨k⟩} x`; so `x = ⨆(K(D) ∩ ↓x) ⊑ b x`. No transfer
from `↥(Fp α)` is involved.

## Gap 2, and why finiteness is exactly what it needs

`p_N(x) = ⨆(N ∩ ↓x)` always lies in `N`'s *downward closure*, but for infinite
`N` it need not lie in `N` — the supremum of an infinite directed subset of `N`
escapes. When `N` is finite the directed set `N ∩ ↓x` is finite and nonempty, so
it contains its own greatest element, and that element *is* the supremum. That is
the whole content of `range_normalHom_of_finite`, and it is the step the paper
compresses into "whenever `im(p)` is finite".
-/

namespace ScottDomains

namespace SFP

open ScottHom

variable {α : Type*}

/-! ## Gap 4: the two finite-combinatorial lemmas -/

section FiniteDirected

variable [Preorder α] {s t : Set α}

/-- **Gap 4(b).** A finite subset of a nonempty directed set has an upper bound
*inside the set*. Induction on the finite subset: the empty case takes any member
of `s`, and `insert a t` pairs `a` against the bound for `t` with directedness.

The upper bound must be produced inside `s`, not merely in the ambient order;
that is what makes it usable as "the single projection dominating a finite set of
projections". -/
theorem exists_upperBound_of_finite_subset (hne : s.Nonempty)
    (hdir : DirectedOn (· ≤ ·) s) (ht : t.Finite) :
    t ⊆ s → ∃ m ∈ s, ∀ y ∈ t, y ≤ m := by
  induction t, ht using Set.Finite.induction_on with
  | empty =>
    intro _
    obtain ⟨m, hm⟩ := hne
    exact ⟨m, hm, fun y hy => absurd hy (Set.notMem_empty y)⟩
  | @insert a u _ _ ih =>
    intro hsub
    obtain ⟨m, hm, hmu⟩ := ih fun y hy => hsub (Set.mem_insert_of_mem a hy)
    obtain ⟨c, hc, hac, hmc⟩ := hdir a (hsub (Set.mem_insert a u)) m hm
    refine ⟨c, hc, ?_⟩
    rintro y (rfl | hy)
    · exact hac
    · exact (hmu y hy).trans hmc

/-- **Gap 4(a).** A nonempty finite directed set contains its own greatest
element — the previous lemma applied to `t := s`. -/
theorem exists_greatest_of_finite (hfin : s.Finite) (hne : s.Nonempty)
    (hdir : DirectedOn (· ≤ ·) s) : ∃ m ∈ s, ∀ y ∈ s, y ≤ m :=
  exists_upperBound_of_finite_subset hne hdir hfin subset_rfl

/-- The greatest element of a nonempty finite directed set is its least upper
bound. This is the form both uses below want: it identifies `sSup` with a member
of the set. -/
theorem exists_mem_isLUB_of_finite (hfin : s.Finite) (hne : s.Nonempty)
    (hdir : DirectedOn (· ≤ ·) s) : ∃ m ∈ s, IsLUB s m := by
  obtain ⟨m, hm, hmax⟩ := exists_greatest_of_finite hfin hne hdir
  exact ⟨m, hm, fun y hy => hmax y hy, fun b hb => hb hm⟩

end FiniteDirected

/-! ## Projections of finite image

The paper's "whenever `p : D → D` is a finitary projection and `im(p)` is finite,
then `im(p) ⊆ K(D)`" — which needs neither *finitary* nor algebraicity of `D`,
only that `p` is a Scott-continuous projection. -/

section FiniteImage

variable [CompletePartialOrder α] {p q : ScottHom α α}

/-- **Every element of a finite image is compact.** Given a nonempty directed `s`
with `IsLUB s u` and `y ⊑ u` for `y ∈ im(p)`: the image `p '' s` is a nonempty
directed subset of the finite `im(p)`, so it has a greatest element `p a` with
`a ∈ s`, which is therefore its least upper bound; continuity says `p u` is too,
so `p u = p a`. Then `y = p y ⊑ p u = p a ⊑ a`.

This is where gap 4(a) is spent, and it is the only place the *finiteness* of the
image enters the forward direction. -/
theorem isCompactElement_of_mem_range_of_finite (hp : IsProjection p)
    (hfin : (Set.range ⇑p).Finite) {y : α} (hy : y ∈ Set.range ⇑p) :
    IsCompactElement y := by
  intro s u hne hs hlub hyu
  have hdir : DirectedOn (· ≤ ·) (⇑p '' s) := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    obtain ⟨c, hc, hac, hbc⟩ := hs a ha b hb
    exact ⟨p c, ⟨c, hc, rfl⟩, p.monotone hac, p.monotone hbc⟩
  have hsubr : (⇑p '' s) ⊆ Set.range ⇑p := by
    rintro _ ⟨a, _, rfl⟩
    exact Set.mem_range_self a
  obtain ⟨_, ⟨a, ha, rfl⟩, hmlub⟩ :=
    exists_mem_isLUB_of_finite (hfin.subset hsubr) (hne.image _) hdir
  refine ⟨a, ha, ?_⟩
  have hpa : p u = p a := (p.scottContinuous hne hs hlub).unique hmlub
  calc y = p y := (hp.apply_of_mem_range hy).symm
    _ ≤ p u := p.monotone hyu
    _ = p a := hpa
    _ ≤ a := hp.le a

/-- `im(p) ⊆ K(D)` for a projection of finite image — the paper's sentence. -/
theorem range_subset_compacts_of_finite (hp : IsProjection p)
    (hfin : (Set.range ⇑p).Finite) : Set.range ⇑p ⊆ compacts α :=
  fun _ hy => isCompactElement_of_mem_range_of_finite hp hfin hy

/-- **Gap 2, in the coordinate the forward direction needs it.** On a finite
image, `fpBasis` and the image coincide: `im(p) ∩ K(D) = im(p)`. This is what
makes the `FpLattice` machinery unnecessary for the forward direction — there is
no basis coordinate distinct from the image. -/
theorem range_inter_compacts_of_finite (hp : IsProjection p)
    (hfin : (Set.range ⇑p).Finite) : Set.range ⇑p ∩ compacts α = Set.range ⇑p :=
  Set.inter_eq_left.mpr (range_subset_compacts_of_finite hp hfin)

/-- **A projection is determined by its image.** `p x` is the greatest member of
`im(p) ∩ ↓x`: it lies there, and any `y ∈ im(p)` with `y ⊑ x` satisfies
`y = p y ⊑ p x`. Two projections with the same image therefore agree pointwise.

This is the injectivity that makes `M` countable in the converse. -/
theorem eq_of_range_eq (hp : IsProjection p) (hq : IsProjection q)
    (h : Set.range ⇑p = Set.range ⇑q) : p = q := by
  have key : ∀ r t : ScottHom α α, IsProjection r → IsProjection t →
      Set.range ⇑r ⊆ Set.range ⇑t → ∀ x, r x ≤ t x := by
    intro r t hr ht hsub x
    calc r x = t (r x) := (ht.apply_of_mem_range (hsub (Set.mem_range_self x))).symm
      _ ≤ t x := t.monotone (hr.le x)
  exact ScottHom.ext fun x =>
    le_antisymm (key p q hp hq h.subset x) (key q p hq hp h.superset x)

end FiniteImage

/-! ## The least projection

`M` must be nonempty for the forward direction: compactness is stated for
*nonempty* directed sets, and the argument applies it to `{p x | p ∈ M}`.
Mathlib's `DirectedOn` holds vacuously on `∅`, so the paper's "directed" — which
asks every finite subset, including `∅`, for an upper bound in the set — is not
recovered from `IsBifiniteViaProjections`'s second conjunct. The witness is the
constant-`⊥` map, which is the least finitary projection. -/

section BotProjection

variable [CompletePartialOrder α]

theorem isProjection_const_bot :
    IsProjection (ScottHom.const (⊥ : α) : ScottHom α α) :=
  ⟨fun _ => rfl, fun _ => bot_le⟩

theorem eq_bot_of_mem_range_const_bot {y : α}
    (hy : y ∈ Set.range ⇑(ScottHom.const (⊥ : α) : ScottHom α α)) : y = ⊥ := by
  obtain ⟨x, hx⟩ := hy
  exact hx.symm

theorem range_const_bot_finite :
    (Set.range ⇑(ScottHom.const (⊥ : α) : ScottHom α α)).Finite :=
  (Set.finite_singleton (⊥ : α)).subset fun _ hy => eq_bot_of_mem_range_const_bot hy

/-- The constant-`⊥` map is a finitary projection: its image is the one-point cpo
`{⊥}`, whose single element is compact and whose basis is countable. -/
theorem isFinitaryProjection_const_bot :
    IsFinitaryProjection (ScottHom.const (⊥ : α) : ScottHom α α) := by
  refine ⟨isProjection_const_bot, ?_⟩
  letI : CompletePartialOrder ↥(Set.range ⇑(ScottHom.const (⊥ : α) : ScottHom α α)) :=
    IsProjection.rangeCompletePartialOrder isProjection_const_bot
  have hss : ∀ y z : ↥(Set.range ⇑(ScottHom.const (⊥ : α) : ScottHom α α)), y = z :=
    fun y z => Subtype.ext
      ((eq_bot_of_mem_range_const_bot y.2).trans (eq_bot_of_mem_range_const_bot z.2).symm)
  exact
    { __ := isAlgebraic_of_forall_isCompactElement fun y s _ hne _ _ _ => by
        obtain ⟨a, ha⟩ := hne
        exact ⟨a, ha, le_of_eq (hss y a)⟩
      countable_compacts := Set.Subsingleton.countable fun a _ b _ => hss a b }

end BotProjection

/-! ## Theorem 14, forward direction -/

section Forward

variable [CompletePartialOrder α] {M : Set (ScottHom α α)}

/-- **Theorem 14, `1 → 2`.** If the finitary projections of finite image are
countable, directed and join to `id`, then `D` is a domain whose basis is a
Plotkin order.

`hM` characterizes `M` as the paper's set rather than defining it, so this module
does not import `Skeleton/Recovered.lean`, which imports it.

The four steps are the paper's own, in its order.

1. Every `p ∈ M` has `im(p) ⊆ K(D)` (`isCompactElement_of_mem_range_of_finite`).
2. `⨆M = id` evaluates pointwise (`ScottHom.isLUB_eval_image_of_isLUB`), so
   `{p x | p ∈ M}` is a directed set of compacts below `x` with least upper bound
   `x`; that forces `K(D) ∩ ↓x` itself to be directed with least upper bound `x`,
   which is `IsAlgebraic`.
3. Every compact `k` satisfies `k = p k` for some `p ∈ M`, so
   `K(D) ⊆ ⋃{im(p) | p ∈ M}` — a countable union of finite sets.
4. A finite `u ⊆ K(D)` is fixed by a single `p ∈ M`, chosen as an upper bound in
   `M` of the finitely many `p_k` (gap 4(b)); then `im(p) ∩ K(D) = im(p)` is
   finite, normal by `IsFinitaryProjection.isNormalIn_compacts`, and contains
   `u`. -/
theorem theorem_14_forward
    (hM : ∀ p : ScottHom α α,
      p ∈ M ↔ (IsFinitaryProjection p ∧ (Set.range ⇑p).Finite))
    (hcount : M.Countable) (hdir : DirectedOn (· ≤ ·) M)
    (hlub : IsLUB M (ScottHom.id : ScottHom α α)) :
    Domain α ∧ IsBifinite α := by
  -- `M` is nonempty: the constant-`⊥` map is the least finitary projection.
  have hMne : M.Nonempty :=
    ⟨ScottHom.const ⊥, (hM _).mpr ⟨isFinitaryProjection_const_bot, range_const_bot_finite⟩⟩
  -- Step 2's evaluation data.
  have hedir : ∀ x : α, DirectedOn (· ≤ ·) ((fun f : ScottHom α α => f x) '' M) :=
    fun x => ScottHom.directedOn_eval_image hdir x
  have hene : ∀ x : α, ((fun f : ScottHom α α => f x) '' M).Nonempty :=
    fun x => hMne.image _
  have heval : ∀ x : α, IsLUB ((fun f : ScottHom α α => f x) '' M) x :=
    fun x => ScottHom.isLUB_eval_image_of_isLUB hdir hlub x
  -- Step 1.
  have hsub : ∀ x : α, (fun f : ScottHom α α => f x) '' M ⊆ compactsBelow x := by
    rintro x _ ⟨p, hp, rfl⟩
    obtain ⟨hfp, hfin⟩ := (hM p).mp hp
    exact ⟨isCompactElement_of_mem_range_of_finite hfp.isProjection hfin
      (Set.mem_range_self x), hfp.isProjection.le x⟩
  -- The workhorse: every compact below `x` is dominated by some `p x`, `p ∈ M`.
  have hkey : ∀ x k : α, IsCompactElement k → k ≤ x → ∃ p ∈ M, k ≤ p x := by
    intro x k hk hkx
    obtain ⟨_, ⟨p, hp, rfl⟩, hkp⟩ := hk _ x (hene x) (hedir x) (heval x) hkx
    exact ⟨p, hp, hkp⟩
  -- Step 2.
  have halg : IsAlgebraic α := by
    constructor
    case directedOn_compactsBelow =>
      intro x a ha b hb
      obtain ⟨p, hp, hap⟩ := hkey x a ha.1 ha.2
      obtain ⟨q, hq, hbq⟩ := hkey x b hb.1 hb.2
      obtain ⟨r, hr, hpr, hqr⟩ := hdir p hp q hq
      exact ⟨r x, hsub x ⟨r, hr, rfl⟩, hap.trans (hpr x), hbq.trans (hqr x)⟩
    case isLUB_compactsBelow =>
      intro x
      exact ⟨fun k hk => hk.2, fun b hb => (heval x).2 fun z hz => hb (hsub x hz)⟩
  haveI := halg
  -- Every compact is fixed by some `p ∈ M`.
  have hfix : ∀ k : α, IsCompactElement k → ∃ p ∈ M, p k = k := by
    intro k hk
    obtain ⟨p, hp, hkp⟩ := hkey k k hk le_rfl
    obtain ⟨hfp, _⟩ := (hM p).mp hp
    exact ⟨p, hp, le_antisymm (hfp.isProjection.le k) hkp⟩
  -- Step 3.
  have hKcount : (compacts α).Countable := by
    refine Set.Countable.mono (fun k hk => ?_)
      (Set.Countable.biUnion (t := fun (p : ScottHom α α) (_ : p ∈ M) => Set.range ⇑p) hcount
        (fun p hp => ((hM p).mp hp).2.countable))
    obtain ⟨p, hp, hpk⟩ := hfix k hk
    exact Set.mem_biUnion hp ⟨k, hpk⟩
  refine ⟨{ __ := halg, countable_compacts := hKcount }, ?_⟩
  -- Step 4: the Plotkin order.
  intro u hufin husub
  choose! P hPM hPfix using fun k (hk : k ∈ u) => hfix k (husub hk)
  obtain ⟨p, hpM, hpub⟩ :=
    exists_upperBound_of_finite_subset hMne hdir (hufin.image P)
      (by rintro _ ⟨k, hk, rfl⟩; exact hPM k hk)
  obtain ⟨hfp, hfin⟩ := (hM p).mp hpM
  have hup : u ⊆ Set.range ⇑p := by
    intro k hk
    refine ⟨k, le_antisymm (hfp.isProjection.le k) ?_⟩
    calc k = P k k := (hPfix k hk).symm
      _ ≤ p k := hpub (P k) ⟨k, hk, rfl⟩ k
  refine ⟨Set.range ⇑p ∩ compacts α, hfin.subset Set.inter_subset_left,
    hfp.isNormalIn_compacts, fun k hk => ⟨hup hk, husub hk⟩⟩

alias thm14_forward := theorem_14_forward

end Forward

/-! ## Gap 2: the image of a finite normal subposet's projection -/

section Bridge

variable [CompletePartialOrder α] [IsAlgebraic α] {N : Set α}

/-- **Gap 2's bridge lemma.** For a **finite** normal subposet `N ◁ K(D)`, the
image of `p_N` is exactly `N`.

`p_N(x) = ⨆(N ∩ ↓x)`, and `N ∩ ↓x` is finite, nonempty (`⊥ ∈ N`) and directed, so
by gap 4(a) it has a greatest element, which is its supremum and lies in `N`. The
reverse inclusion is `normalFun_of_mem`.

Finiteness is not decoration: for infinite `N` the supremum of a directed subset
of `N` need not lie in `N`, and `im(p_N)` is then strictly larger than `N` — only
`im(p_N) ∩ K(D) = N` survives (`range_normalHom_inter_compacts`). -/
theorem range_normalHom_of_finite (hN : N ◁ compacts α) (hfin : N.Finite) :
    Set.range ⇑(normalHom hN) = N := by
  apply Set.Subset.antisymm
  · rintro _ ⟨x, rfl⟩
    obtain ⟨m, hm, hmlub⟩ :=
      exists_mem_isLUB_of_finite (hfin.subset Set.inter_subset_left)
        (hN.nonempty_inter_Iic x) (hN.directedOn_inter_Iic x)
    have hval : sSup (N ∩ Set.Iic x) = m :=
      (hN.directedOn_inter_Iic x).isLUB_sSup.unique hmlub
    show sSup (N ∩ Set.Iic x) ∈ N
    rw [hval]
    exact hm.1
  · exact fun z hz => ⟨z, normalFun_of_mem hN hz⟩

/-- A projection whose image sits inside `N` is below `p_N`: `r x ∈ N` and
`r x ⊑ x`, so `r x ⊑ ⨆(N ∩ ↓x)`. This is how the converse produces `⊑` in the
*function space* — no order isomorphism with the normal subposets is needed, and
so gap 3 never arises. -/
theorem le_normalHom_of_range_subset (hN : N ◁ compacts α) {r : ScottHom α α}
    (hr : IsProjection r) (hrN : Set.range ⇑r ⊆ N) : r ≤ normalHom hN :=
  fun x => le_normalFun hN (hrN (Set.mem_range_self x)) (hr.le x)

end Bridge

section BridgeDomain

variable [CompletePartialOrder α] [Domain α] {N : Set α}

/-- Gap 2 in the `Fp(D)` coordinates the r0034 docstring names it in:
`Set.range ⇑(toFp hN) = N`. `toFp hN` is `normalHom hN` with its
finitary-projection proof attached, so this is `range_normalHom_of_finite`
transported along `Subtype.val`. -/
theorem range_toFp_eq (hN : N ◁ compacts α) (hfin : N.Finite) :
    Set.range ⇑(toFp hN).val = N :=
  range_normalHom_of_finite hN hfin

/-- On the finite side, `fpBasis` and the image of a finitary projection agree.
Combined with `range_inter_compacts_of_finite`, this says the two finiteness
conditions of gap 2 — `(fpBasis p).Finite` and `(Set.range ⇑p).Finite` — define
the same subset of `Fp(D)`. -/
theorem range_eq_fpBasis_of_finite {p : ↥(Fp α)} (hfin : (fpBasis p).Finite) :
    Set.range ⇑p.val = fpBasis p := by
  have h := range_normalHom_of_finite (fpBasis_isNormalIn p) hfin
  rwa [normalHom_fpBasis p] at h

/-- `p_N` for finite normal `N` is a finitary projection of finite image — the
converse's supply of members of `M`. -/
theorem isFinitaryProjection_and_finite_normalHom (hN : N ◁ compacts α) (hfin : N.Finite) :
    IsFinitaryProjection (normalHom hN) ∧ (Set.range ⇑(normalHom hN)).Finite :=
  ⟨isFinitaryProjection_normalHom hN, (range_normalHom_of_finite hN hfin).symm ▸ hfin⟩

end BridgeDomain

/-! ## Theorem 14, converse -/

section Converse

variable [CompletePartialOrder α] [Domain α] {M : Set (ScottHom α α)}

/-- `M` is countable: `p ↦ im(p)` is injective on projections (`eq_of_range_eq`)
and lands in the finite subsets of the countable `K(D)`
(`Set.countable_setOf_finite_subset`). Only `M ⊆ …` is used, so no
characterization of `M` is needed. -/
theorem countable_of_subset_finiteImage
    (hM : ∀ p ∈ M, IsFinitaryProjection p ∧ (Set.range ⇑p).Finite) : M.Countable := by
  have hmaps : Set.MapsTo (fun p : ScottHom α α => Set.range ⇑p) M
      {t : Set α | t.Finite ∧ t ⊆ compacts α} := by
    intro p hp
    obtain ⟨hfp, hfin⟩ := hM p hp
    exact ⟨hfin, range_subset_compacts_of_finite hfp.isProjection hfin⟩
  have hinj : Set.InjOn (fun p : ScottHom α α => Set.range ⇑p) M := by
    intro p hp q hq hpq
    exact eq_of_range_eq (hM p hp).1.isProjection (hM q hq).1.isProjection hpq
  exact hmaps.countable_of_injOn hinj
    (Set.countable_setOf_finite_subset (Domain.countable_compacts (α := α)))

/-- `M` is directed. Given `p, q ∈ M`, the least normal subposet of `K(D)`
containing `im(p) ∪ im(q)` is finite (this is the one place the Plotkin condition
is spent, via `normalClosure_finite`) and its projection dominates both by
`le_normalHom_of_range_subset`. -/
theorem directedOn_of_normalHom_mem (h : IsBifinite α)
    (hM : ∀ p ∈ M, IsFinitaryProjection p ∧ (Set.range ⇑p).Finite)
    (hMN : ∀ {N : Set α} (hN : N ◁ compacts α), N.Finite → normalHom hN ∈ M) :
    DirectedOn (· ≤ ·) M := by
  intro p hp q hq
  obtain ⟨hfp, hpfin⟩ := hM p hp
  obtain ⟨hfq, hqfin⟩ := hM q hq
  have hSc : Set.range ⇑p ∪ Set.range ⇑q ⊆ compacts α :=
    Set.union_subset (range_subset_compacts_of_finite hfp.isProjection hpfin)
      (range_subset_compacts_of_finite hfq.isProjection hqfin)
  have hN : (normalClosure (compacts α) (Set.range ⇑p ∪ Set.range ⇑q)) ◁ compacts α :=
    normalClosure_isNormalIn h isCompactElement_bot hSc
  refine ⟨normalHom hN, hMN hN (normalClosure_finite h (hpfin.union hqfin) hSc),
    le_normalHom_of_range_subset hN hfp.isProjection ?_,
    le_normalHom_of_range_subset hN hfq.isProjection ?_⟩
  · exact fun z hz => subset_normalClosure _ _ (Or.inl hz)
  · exact fun z hz => subset_normalClosure _ _ (Or.inr hz)

/-- `⨆M = id`. Upper bound: every member is a projection. **Least**: for an upper
bound `b` and a compact `k ⊑ x`, the least finite normal subposet containing `k`
gives a `p_{⟨k⟩} ∈ M` with `k ⊑ p_{⟨k⟩} x ⊑ b x`; algebraicity then lifts
`∀ k ∈ K(D) ∩ ↓x, k ⊑ b x` to `x ⊑ b x`.

This is gap 3, discharged in `ScottHom α α` directly. Nothing here mentions
`↥(Fp α)`, so no weaker `IsLUB` has to be strengthened. -/
theorem isLUB_id_of_normalHom_mem (h : IsBifinite α)
    (hM : ∀ p ∈ M, IsFinitaryProjection p ∧ (Set.range ⇑p).Finite)
    (hMN : ∀ {N : Set α} (hN : N ◁ compacts α), N.Finite → normalHom hN ∈ M) :
    IsLUB M (ScottHom.id : ScottHom α α) := by
  constructor
  · intro p hp x
    exact (hM p hp).1.isProjection.le x
  · intro b hb
    refine ScottHom.le_def.mpr fun x => ?_
    rw [ScottHom.id_apply]
    refine (IsAlgebraic.isLUB_compactsBelow x).2 ?_
    rintro k ⟨hkc, hkx⟩
    have hkc' : ({k} : Set α) ⊆ compacts α := Set.singleton_subset_iff.mpr hkc
    have hN : (normalClosure (compacts α) {k}) ◁ compacts α :=
      normalClosure_isNormalIn h isCompactElement_bot hkc'
    calc k ≤ normalFun (normalClosure (compacts α) {k}) x :=
          le_normalFun hN (subset_normalClosure _ _ rfl) hkx
      _ ≤ b x := hb (hMN hN (normalClosure_finite h (Set.finite_singleton k) hkc')) x

/-- **Theorem 14, `2 → 1`.** A domain whose basis is a Plotkin order is bifinite
in the paper's sense. -/
theorem theorem_14_converse (h : IsBifinite α)
    (hM : ∀ p : ScottHom α α,
      p ∈ M ↔ (IsFinitaryProjection p ∧ (Set.range ⇑p).Finite)) :
    M.Countable ∧ DirectedOn (· ≤ ·) M ∧ IsLUB M (ScottHom.id : ScottHom α α) := by
  have hsub : ∀ p ∈ M, IsFinitaryProjection p ∧ (Set.range ⇑p).Finite :=
    fun p hp => (hM p).mp hp
  have hmem : ∀ {N : Set α} (hN : N ◁ compacts α), N.Finite → normalHom hN ∈ M :=
    fun hN hfin => (hM _).mpr (isFinitaryProjection_and_finite_normalHom hN hfin)
  exact ⟨countable_of_subset_finiteImage hsub, directedOn_of_normalHom_mem h hsub hmem,
    isLUB_id_of_normalHom_mem h hsub hmem⟩

alias thm14_converse := theorem_14_converse

end Converse

end SFP

end ScottDomains
