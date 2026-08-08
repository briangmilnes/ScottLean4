import ScottDomains.Theorem6
-- `IsPlotkinOrder` and `IsBifinite`, previously reached through the skeleton.
import ScottDomains.Bifinite
-- `IsClosure` and its API. This was `ScottDomains.Skeleton.Section6` until r0042;
-- importing the skeleton put it inside `JungFinite`'s import cone, which made
-- citing Theorem 18's proof from `Skeleton/Section6.lean`'s `thm18` a cycle.
import ScottDomains.Closure

/-!
# `Fp(D)` and `Fc(D)` as posets

Gunter & Scott, *Semantic Domains*, §3.1 and §7.1:

> … there is an isomorphism between the cpo of normal substructures of `K(D)`
> and the poset `Fp(D)` of finitary projections on `D`.

> By analogy with the notion of a finitary projection, we will say that a
> function `r : D → D` is a **finitary closure** if `r ∘ r = r ⊒ id` and `im(r)`
> is a domain. … We let `Fc(D)` be the poset of finitary closures `r : D → D`.

The paper names both posets and never says what the order is, because there is
only one candidate: both are *subsets of the function space* `D → D`, and the
order they carry is the one `D → D` already has — the pointwise order
`p ⊑ q ⟺ ∀ x, p(x) ⊑ q(x)` (`ScottHom.le_def`). Three things fix that choice.

1. Every statement the paper makes about these posets is a statement about the
   pointwise order. Theorem 6's monotonicity clause is `N ⊆ N' → p_N ⊑ p_{N'}`,
   proved pointwise in `normalHom_mono`; and Lemma 17 computes `⨆M = id` for a
   set `M` of finitary projections, which is a pointwise supremum.

   An earlier version of this paragraph also cited Theorem 16's claim that the
   *inclusion* `Fp(D) ↪ (D → D)` is an embedding, as only meaningful under the
   subspace order. That reason is withdrawn: r0032 proved the claim **false** for
   the embedding–projection reading (`FinitaryProjectionEmbedding.lean`), and
   under the order-embedding reading it is true by `Fp.le_def`'s `Iff.rfl` and so
   supports nothing. The design choice stands on the two reasons that remain.
2. On projections the pointwise order agrees with inclusion of images
   (`IsProjection.range_mono`, and `range_normalHom_inter_compacts` in the
   opposite direction), so it is also the order that makes Theorem 6 an order
   isomorphism onto the normal substructures ordered by `⊆`.
3. It costs nothing to install: `Fp α` and `Fc α` are `Set (ScottHom α α)`, and
   `↥(Fp α)` gets `Subtype.partialOrder` over `ScottHom`'s pointwise
   `PartialOrder` by instance resolution. `Fp.le_def` and `Fc.le_def` record
   that the resulting order really is the pointwise one, by `Iff.rfl`.

## What this file supplies

* `Fp α`, `Fc α`, and the pointwise order on each.
* **Lemma 19 in the paper's strength**: for a domain `D` and a closure
  `r : D → D`, `im(r)` is a *domain*, not merely a cpo. `Skeleton/Section6.lean`
  proves only the cpo half (`lem19` there asserts the existence of a
  `CompletePartialOrder`); the basis is what the paper's one-line proof sketch
  ("by showing that `{r(x) | x ∈ K(D)}` forms a basis for `im(r)`") supplies, and
  Lemma 20 cannot be stated without it — `Fc(D)` is defined by "`im(r)` is a
  domain", so a supremum of closures is a *member of `Fc(D)*` only once the image
  of every closure is known to be a domain.
* The cpo structure on `Fc(D)` (Lemma 20) and the algebraic-lattice structure on
  `Fp(D)` (Theorem 16). The two numbered statements themselves are in
  `Skeleton/Section6b.lean`.

## The `SupSet`/`InfSet` case split

`Fc.completePartialOrder` must give `sSup` on *every* subset of `↥(Fc α)`, but
the pointwise supremum of an arbitrary family of closures is not a closure. The
`dite` therefore branches on **membership of the candidate value in `Fc α`** —
the proposition the subtype constructor needs — and not on directedness, which is
merely sufficient. That is the rule the `ScottHom` and `Smash` defects
established.

The candidate is the supremum of `insert id (val '' S)` rather than of
`val '' S`. Adjoining `id` costs nothing (it is the least closure, so it changes
no supremum of a nonempty family) and removes the empty case entirely: the
inserted family is nonempty and directed whenever `S` is, so one argument covers
`S = ∅` and `S ≠ ∅` alike.
-/

namespace ScottDomains

variable {α : Type*}

section IdHom

variable [Preorder α]

/-- The identity of the function space. It is the greatest finitary projection
and the least finitary closure, so both §6 results need it. -/
def ScottHom.id : ScottHom α α := ⟨_root_.id, ScottContinuous.id⟩

@[simp] theorem ScottHom.id_apply (x : α) : (ScottHom.id : ScottHom α α) x = x := rfl

end IdHom

section Posets

variable [CompletePartialOrder α]

/-- `Fp(D)`, the finitary projections on `D`, as a subset of the function space.
The poset structure is the pointwise order inherited from `D → D`; see the module
docstring. -/
def Fp (α : Type*) [CompletePartialOrder α] : Set (ScottHom α α) :=
  {p | ScottHom.IsFinitaryProjection p}

@[simp] theorem mem_Fp {p : ScottHom α α} : p ∈ Fp α ↔ ScottHom.IsFinitaryProjection p := Iff.rfl

/-- A **finitary closure**: `r ∘ r = r ⊒ id` with `im(r)` a domain. The dual of
`ScottHom.IsFinitaryProjection`, and stated the same way — the cpo structure on
`im(r)` depends on the closure *proof*, so the `Domain` claim is applied to
`IsClosure.rangeCompletePartialOrder` explicitly. -/
def IsFinitaryClosure (r : ScottHom α α) : Prop :=
  ∃ hr : IsClosure r, @Domain _ (IsClosure.rangeCompletePartialOrder hr)

theorem IsFinitaryClosure.isClosure {r : ScottHom α α} (h : IsFinitaryClosure r) :
    IsClosure r := h.choose

/-- `Fc(D)`, the finitary closures on `D`, with the same pointwise order. -/
def Fc (α : Type*) [CompletePartialOrder α] : Set (ScottHom α α) :=
  {r | IsFinitaryClosure r}

@[simp] theorem mem_Fc {r : ScottHom α α} : r ∈ Fc α ↔ IsFinitaryClosure r := Iff.rfl

/-- The order on `Fp(D)` is the pointwise order of the function space. -/
theorem Fp.le_def {p q : ↥(Fp α)} : p ≤ q ↔ ∀ x, p.val x ≤ q.val x := Iff.rfl

/-- The order on `Fc(D)` is the pointwise order of the function space. -/
theorem Fc.le_def {r s : ↥(Fc α)} : r ≤ s ↔ ∀ x, r.val x ≤ s.val x := Iff.rfl

end Posets

/-! ## Lemma 19 at the paper's strength: `im(r)` is a domain -/

section ClosureImage

variable [CompletePartialOrder α] {r : ScottHom α α}

/-- For a **nonempty** directed set in `im(r)`, the ambient least upper bound
already lies in `im(r)`: continuity moves `r` inside, and `r` fixes its own
image. Nonemptiness is essential — `r ⊥` is in general not `⊥`, so `sSup ∅` need
not be a fixed point of `r`.

This is the form indexed by a set of the **subtype** `↥(im r)`.
`IsClosure.apply_sSup_of_directed` in `Skeleton/Section6.lean` is the ambient
form, taking `D : Set α` with `D ⊆ im r`; the two carried one name until r0028's
merge, which is why this one is spelled out. -/
theorem IsClosure.apply_sSup_val_image_of_directed (hr : IsClosure r)
    {s : Set ↥(Set.range ⇑r)}
    (hne : s.Nonempty) (hs : DirectedOn (· ≤ ·) s) :
    r (sSup (Subtype.val '' s)) = sSup (Subtype.val '' s) := by
  have hdir := ScottHom.directedOn_val_image (p := r) hs
  have hlub : IsLUB ((⇑r) '' (Subtype.val '' s)) (r (sSup (Subtype.val '' s))) :=
    r.scottContinuous (hne.image _) hdir hdir.isLUB_sSup
  have himg : (⇑r) '' (Subtype.val '' s) = Subtype.val '' s := by
    ext y
    constructor
    · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
      exact ⟨a, ha, (hr.apply_of_mem_range a.2).symm⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a.val, ⟨a, ha, rfl⟩, hr.apply_of_mem_range a.2⟩
  rw [himg] at hlub
  exact hlub.unique hdir.isLUB_sSup

/-- On a nonempty directed set, a least upper bound in `im(r)` is a least upper
bound in `D`. Compare `IsProjection.isLUB_val_image`, which needs no nonemptiness
because a projection fixes `⊥`. -/
theorem IsClosure.isLUB_val_image (hr : IsClosure r) {s : Set ↥(Set.range ⇑r)}
    {u : ↥(Set.range ⇑r)} (hne : s.Nonempty) (hs : DirectedOn (· ≤ ·) s) (hu : IsLUB s u) :
    IsLUB (Subtype.val '' s) u.val := by
  have heq : u = ⟨r (sSup (Subtype.val '' s)), Set.mem_range_self _⟩ :=
    hu.unique (hr.isLUB_range hs)
  have hval : u.val = sSup (Subtype.val '' s) := by
    rw [heq]; exact hr.apply_sSup_val_image_of_directed hne hs
  rw [hval]
  exact (ScottHom.directedOn_val_image (p := r) hs).isLUB_sSup

/-- **`r(k)` is compact in `im(r)` for every compact `k` of `D`.** This is the
first half of the paper's "`{r(x) | x ∈ K(D)}` forms a basis for `im(r)`".

The argument is one step: a nonempty directed `s ⊆ im(r)` has the *same* least
upper bound `u` computed in `im(r)` or in `D`, and `k ⊑ r(k) ⊑ u`, so
compactness of `k` in `D` produces `a ∈ s` with `k ⊑ a`; applying `r` and using
that `r` fixes `a` gives `r(k) ⊑ a`. -/
theorem IsClosure.isCompactElement_apply (hr : IsClosure r) {k : α}
    (hk : IsCompactElement k) :
    IsCompactElement (⟨r k, Set.mem_range_self k⟩ : ↥(Set.range ⇑r)) := by
  intro s u hne hs hlub hle
  obtain ⟨_, ⟨a, ha, rfl⟩, hka⟩ :=
    hk _ _ (hne.image _) (ScottHom.directedOn_val_image (p := r) hs)
      (hr.isLUB_val_image hne hs hlub) ((hr.le_apply k).trans hle)
  refine ⟨a, ha, ?_⟩
  show r k ≤ a.val
  calc r k ≤ r a.val := r.monotone hka
    _ = a.val := hr.apply_of_mem_range a.2

/-- `{r(k) | k ∈ K(D) and k ⊑ y}`, the paper's basis of `im(r)`, cut down to the
approximants of `y`. -/
def closureApprox (r : ScottHom α α) (y : ↥(Set.range ⇑r)) : Set ↥(Set.range ⇑r) :=
  (fun k => (⟨r k, Set.mem_range_self k⟩ : ↥(Set.range ⇑r))) '' compactsBelow y.val

theorem closureApprox_nonempty (r : ScottHom α α) (y : ↥(Set.range ⇑r)) :
    (closureApprox r y).Nonempty :=
  (compactsBelow_nonempty y.val).image _

variable [IsAlgebraic α]

theorem directedOn_closureApprox (r : ScottHom α α) (y : ↥(Set.range ⇑r)) :
    DirectedOn (· ≤ ·) (closureApprox r y) := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  obtain ⟨c, hc, hac, hbc⟩ := IsAlgebraic.directedOn_compactsBelow y.val a ha b hb
  exact ⟨_, ⟨c, hc, rfl⟩, r.monotone hac, r.monotone hbc⟩

omit [IsAlgebraic α] in
/-- Every member of `closureApprox r y` is a compact element of `im(r)` below
`y`. -/
theorem closureApprox_subset (hr : IsClosure r) (y : ↥(Set.range ⇑r)) :
    closureApprox r y ⊆ compactsBelow y := by
  rintro _ ⟨k, hk, rfl⟩
  refine ⟨hr.isCompactElement_apply hk.1, ?_⟩
  show r k ≤ y.val
  calc r k ≤ r y.val := r.monotone hk.2
    _ = y.val := hr.apply_of_mem_range y.2

/-- `y` is the least upper bound of `closureApprox r y` in `im(r)`: continuity of
`r` carries the least upper bound `y` of `K(D) ∩ ↓y` to the least upper bound
`r(y) = y` of its image. -/
theorem isLUB_closureApprox (hr : IsClosure r) (y : ↥(Set.range ⇑r)) :
    IsLUB (closureApprox r y) y := by
  refine isLUB_of_isLUB_val_image (p := r) ?_
  have hcont := r.scottContinuous (compactsBelow_nonempty y.val)
    (IsAlgebraic.directedOn_compactsBelow y.val) (IsAlgebraic.isLUB_compactsBelow y.val)
  rw [hr.apply_of_mem_range y.2] at hcont
  have himg : Subtype.val '' closureApprox r y = (⇑r) '' compactsBelow y.val := by
    ext z
    constructor
    · rintro ⟨_, ⟨k, hk, rfl⟩, rfl⟩
      exact ⟨k, hk, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨_, ⟨k, hk, rfl⟩, rfl⟩
  rw [himg]
  exact hcont

/-- **`im(r)` is algebraic.** `closureApprox r y` is directed, sits inside the
compact approximants of `y`, and has `y` as its least upper bound; that forces
the compact approximants themselves to be directed with least upper bound `y`. -/
theorem IsClosure.isAlgebraic_range (hr : IsClosure r) :
    @IsAlgebraic _ (IsClosure.rangeCompletePartialOrder hr) := by
  letI : CompletePartialOrder ↥(Set.range ⇑r) := IsClosure.rangeCompletePartialOrder hr
  constructor
  case directedOn_compactsBelow =>
    intro y a ha b hb
    obtain ⟨s, hs, has⟩ := ha.1 _ _ (closureApprox_nonempty r y) (directedOn_closureApprox r y)
      (isLUB_closureApprox hr y) ha.2
    obtain ⟨t, ht, hbt⟩ := hb.1 _ _ (closureApprox_nonempty r y) (directedOn_closureApprox r y)
      (isLUB_closureApprox hr y) hb.2
    obtain ⟨c, hc, hsc, htc⟩ := directedOn_closureApprox r y s hs t ht
    exact ⟨c, closureApprox_subset hr y hc, has.trans hsc, hbt.trans htc⟩
  case isLUB_compactsBelow =>
    intro y
    refine ⟨fun a ha => ha.2, fun b hb => ?_⟩
    exact (isLUB_closureApprox hr y).2 fun c hc => hb (closureApprox_subset hr y hc)

/-- Every compact element of `im(r)` is of the form `r(k)` with `k ∈ K(D)`: it is
the least upper bound of `closureApprox`, so compactness pulls it back into that
set. -/
theorem IsClosure.compacts_range_subset (hr : IsClosure r) :
    compacts ↥(Set.range ⇑r) ⊆
      (fun k => (⟨r k, Set.mem_range_self k⟩ : ↥(Set.range ⇑r))) '' compacts α := by
  intro c hc
  obtain ⟨_, ⟨k, hk, rfl⟩, hck⟩ := hc _ _ (closureApprox_nonempty r c)
    (directedOn_closureApprox r c) (isLUB_closureApprox hr c) le_rfl
  have hle : (⟨r k, Set.mem_range_self k⟩ : ↥(Set.range ⇑r)) ≤ c :=
    (closureApprox_subset hr c ⟨k, hk, rfl⟩).2
  exact ⟨k, hk.1, (le_antisymm hle hck).symm ▸ rfl⟩

omit [IsAlgebraic α] in
/-- The basis of `im(r)` is countable, being the image of `K(D)` under `r`. -/
theorem IsClosure.countable_compacts_range [Domain α] (hr : IsClosure r) :
    (compacts ↥(Set.range ⇑r)).Countable :=
  Set.Countable.mono hr.compacts_range_subset
    ((Domain.countable_compacts (α := α)).image _)

omit [IsAlgebraic α] in
/-- **Lemma 19, at the paper's strength.** If `D` is a domain and `r : D → D` is
a closure, then `im(r)` is a *domain*.

`Skeleton/Section6.lean`'s `lem19` records only the cpo half. The basis is
`{r(k) | k ∈ K(D)}`, exactly as the paper's proof sketch says, and it is
countable because `K(D)` is. -/
theorem IsClosure.domain_range [Domain α] (hr : IsClosure r) :
    @Domain _ (IsClosure.rangeCompletePartialOrder hr) := by
  letI : CompletePartialOrder ↥(Set.range ⇑r) := IsClosure.rangeCompletePartialOrder hr
  exact { __ := hr.isAlgebraic_range
          countable_compacts := hr.countable_compacts_range }

end ClosureImage

/-! ## Lemma 20: `Fc(D)` is a cpo -/

section FcCpo

variable [CompletePartialOrder α] [Domain α]

omit [Domain α] in
theorem isClosure_id : IsClosure (ScottHom.id : ScottHom α α) :=
  ⟨fun _ => rfl, fun _ => le_rfl⟩

/-- Over a domain, "finitary closure" collapses to "closure": the requirement
that `im(r)` be a domain is automatic by Lemma 19. This is the sentence the paper
states just before Lemma 19. -/
theorem mem_Fc_iff {r : ScottHom α α} : r ∈ Fc α ↔ IsClosure r :=
  ⟨fun h => h.isClosure, fun h => ⟨h, h.domain_range⟩⟩

theorem id_mem_Fc : (ScottHom.id : ScottHom α α) ∈ Fc α := mem_Fc_iff.mpr isClosure_id

/-- `id` is below every closure, which is what makes it the least element of
`Fc(D)`. -/
theorem id_le_of_mem_Fc {r : ScottHom α α} (hr : r ∈ Fc α) : ScottHom.id ≤ r :=
  fun x => (mem_Fc_iff.mp hr).le_apply x

-- `isClosure_sSup` was proved here and, independently and identically, in
-- `UniversalDomain.lean`. The single copy now lives in `Skeleton/Section6.lean`
-- beside `IsClosure`, and this file reaches it through that import.

/-- `insert id (val '' S)` is nonempty and directed whenever `S` is directed, and
all of its members are closures. Adjoining `id` is what lets one argument cover
`S = ∅`. -/
theorem directedOn_insert_id_val_image {S : Set ↥(Fc α)} (hS : DirectedOn (· ≤ ·) S) :
    DirectedOn (· ≤ ·) (insert (ScottHom.id : ScottHom α α) (Subtype.val '' S)) := by
  have hid : ∀ f ∈ insert (ScottHom.id : ScottHom α α) (Subtype.val '' S),
      (ScottHom.id : ScottHom α α) ≤ f := by
    rintro _ (rfl | ⟨a, _, rfl⟩)
    · exact le_rfl
    · exact id_le_of_mem_Fc a.2
  rintro u hu v hv
  rcases hu with rfl | ⟨a, ha, rfl⟩
  · exact ⟨v, hv, hid v hv, le_rfl⟩
  rcases hv with rfl | ⟨b, hb, rfl⟩
  · exact ⟨a.val, Set.mem_insert_of_mem _ ⟨a, ha, rfl⟩, le_rfl, hid _ (Set.mem_insert_of_mem _ ⟨a, ha, rfl⟩)⟩
  obtain ⟨c, hc, hac, hbc⟩ := hS a ha b hb
  exact ⟨c.val, Set.mem_insert_of_mem _ ⟨c, hc, rfl⟩, hac, hbc⟩

open Classical in
/-- **Lemma 20's content.** `Fc(D)` is a cpo: `id` is least, and the least upper
bound of a directed family is the pointwise supremum.

`sSup` branches on **membership of the candidate value in `Fc α`**, the
proposition the subtype constructor needs. The candidate is the supremum of
`insert id (val '' S)`, which is nonempty and directed for every directed `S`,
including `S = ∅`; that is why no separate empty case appears below. -/
@[reducible] noncomputable def Fc.completePartialOrder : CompletePartialOrder ↥(Fc α) :=
  { (inferInstance : PartialOrder ↥(Fc α)) with
    sSup := fun S =>
      if h : sSup (insert (ScottHom.id : ScottHom α α) (Subtype.val '' S)) ∈ Fc α then ⟨_, h⟩
      else ⟨ScottHom.id, id_mem_Fc⟩
    bot := ⟨ScottHom.id, id_mem_Fc⟩
    bot_le := fun r => id_le_of_mem_Fc r.2
    lubOfDirected := fun S hS => by
      have hdir := directedOn_insert_id_val_image hS
      have hcl : ∀ f ∈ insert (ScottHom.id : ScottHom α α) (Subtype.val '' S), IsClosure f := by
        rintro _ (rfl | ⟨a, _, rfl⟩)
        · exact isClosure_id
        · exact mem_Fc_iff.mp a.2
      have hmem : sSup (insert (ScottHom.id : ScottHom α α) (Subtype.val '' S)) ∈ Fc α :=
        mem_Fc_iff.mpr (isClosure_sSup ⟨_, Set.mem_insert _ _⟩ hdir hcl)
      rw [dif_pos hmem]
      constructor
      · intro a ha
        exact hdir.le_sSup (Set.mem_insert_of_mem _ ⟨a, ha, rfl⟩)
      · intro b hb
        refine hdir.sSup_le ?_
        rintro _ (rfl | ⟨a, ha, rfl⟩)
        · exact id_le_of_mem_Fc b.2
        · exact hb ha }

end FcCpo

/-! ## Theorem 16: `Fp(D)` is an algebraic lattice

The route is Theorem 6, as the paper's sketch says: `Fp(D)` is order-isomorphic
to the normal subposets of `K(D)` ordered by `⊆`, so it is enough to show that
*those* form an algebraic lattice when `K(D)` is a Plotkin order.

The one fact that makes the whole argument run is about **minimal upper bounds**:

* in a Plotkin order every upper bound `c` of a pair `a, b` dominates a *minimal*
  upper bound `m ⊑ c` of that pair (`IsPlotkinOrder.exists_isMinimalUpperBound`);
* a normal subposet containing `a` and `b` contains **every** minimal upper bound
  of `a` and `b` (`IsNormalIn.mem_of_isMinimalUpperBound`).

Together these make the normal subposets closed under *arbitrary* intersections
(`isNormalIn_sInter`): given `a, b` in every `Nᵢ` and below `x`, pick a witness
`c` from one `N₀` and replace it by a minimal upper bound `m ⊑ c`, which then
lies in **all** the `Nᵢ` at once. So the normal subposets form a closure system,
and the corresponding least-normal-subposet operator `normalClosure` produces the
compact elements.

Neither closure under intersection nor Theorem 16 holds without the Plotkin
condition. Take `A = {⊥, a, b} ∪ {u₀ ⊐ u₁ ⊐ …}` with every `uᵢ` an upper bound of
`{a, b}`: the even-indexed and the odd-indexed `uᵢ` give two normal subposets
whose intersection `{⊥, a, b}` is not normal, and no minimal upper bound of
`{a, b}` exists. That poset is not a Plotkin order, which is exactly the
hypothesis Theorem 16 spends.
-/

section MinimalUpperBound

variable [Preorder α]

/-- A **minimal upper bound** of `a` and `b` inside `A`: an upper bound in `A`
that no smaller upper bound of `a, b` in `A` sits strictly below. Stated with
`m ⊑ z` rather than `z = m` so that a `Preorder` suffices. -/
structure IsMinimalUpperBound (A : Set α) (a b m : α) : Prop where
  /-- The bound lies in `A`. -/
  mem : m ∈ A
  /-- It is above `a`. -/
  left_le : a ≤ m
  /-- It is above `b`. -/
  right_le : b ≤ m
  /-- Nothing in `A` above `a` and `b` is strictly below it. -/
  min : ∀ z ∈ A, a ≤ z → b ≤ z → z ≤ m → m ≤ z

/-- A finite nonempty subset of a preorder has a minimal member. Induction on the
finite set: at `insert a t`, either `a` is below the minimal member of `t`, in
which case `a` is minimal in `insert a t`, or it is not, in which case the old
minimal member still is. -/
theorem exists_minimal_mem_of_finite {s : Set α} (hs : s.Finite) :
    s.Nonempty → ∃ m ∈ s, ∀ y ∈ s, y ≤ m → m ≤ y := by
  induction s, hs using Set.Finite.induction_on with
  | empty => rintro ⟨x, hx⟩; exact absurd hx (Set.notMem_empty x)
  | @insert a t _ _ ih =>
    intro _
    rcases Set.eq_empty_or_nonempty t with rfl | htne
    · refine ⟨a, Set.mem_insert _ _, ?_⟩
      rintro y (rfl | hy) _
      · exact le_rfl
      · exact absurd hy (Set.notMem_empty y)
    · obtain ⟨m, hm, hmin⟩ := ih htne
      by_cases hab : a ≤ m
      · refine ⟨a, Set.mem_insert _ _, ?_⟩
        rintro y (rfl | hy) hya
        · exact le_rfl
        · exact hab.trans (hmin y hy (hya.trans hab))
      · refine ⟨m, Set.mem_insert_of_mem _ hm, ?_⟩
        rintro y (rfl | hy) hym
        · exact absurd hym hab
        · exact hmin y hy hym

end MinimalUpperBound

section ClosureSystem

variable [PartialOrder α] {A : Set α}

/-- **In a Plotkin order every upper bound dominates a minimal upper bound.**

Take a *finite* `N ◁ A` containing `a, b, c`, which the Plotkin condition
supplies, and let `m` be a minimal member of the finite nonempty set
`{y ∈ N | a ⊑ y, b ⊑ y, y ⊑ c}`. Minimality inside that finite set upgrades to
minimality in the whole of `A`: an upper bound `z ⊑ m` of `a, b` in `A` has, by
normality of `N` at `z`, some `w ∈ N ∩ ↓z` above `a` and `b`; then `w` belongs to
the finite set and `w ⊑ m`, so `m ⊑ w ⊑ z`.

This is the only place bifiniteness is spent, and it is spent through
*finiteness* alone — no minimal-upper-bound closure operator `U^∞` and no König
argument. -/
theorem IsPlotkinOrder.exists_isMinimalUpperBound (h : IsPlotkinOrder A) {a b c : α}
    (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A) (hac : a ≤ c) (hbc : b ≤ c) :
    ∃ m, IsMinimalUpperBound A a b m ∧ m ≤ c := by
  obtain ⟨N, hNfin, hN, hsub⟩ :=
    h {a, b, c} ((Set.finite_singleton c).insert b |>.insert a)
      (by rintro z (rfl | rfl | rfl) <;> assumption)
  have hbot : ∀ {z : α}, z ∈ ({a, b, c} : Set α) → z ∈ N := fun hz => hsub hz
  set F : Set α := {y | y ∈ N ∧ a ≤ y ∧ b ≤ y ∧ y ≤ c} with hF
  have hFfin : F.Finite := hNfin.subset fun _ hy => hy.1
  have hFne : F.Nonempty := ⟨c, hbot (by simp), hac, hbc, le_rfl⟩
  obtain ⟨m, hm, hmin⟩ := exists_minimal_mem_of_finite hFfin hFne
  refine ⟨m, ⟨hN.subset hm.1, hm.2.1, hm.2.2.1, ?_⟩, hm.2.2.2⟩
  intro z hz haz hbz hzm
  obtain ⟨w, ⟨hwN, hwz⟩, haw, hbw⟩ :=
    hN.directedOn hz a ⟨hbot (by simp), haz⟩ b ⟨hbot (by simp), hbz⟩
  have hwF : w ∈ F := ⟨hwN, haw, hbw, ((hwz.trans hzm).trans hm.2.2.2)⟩
  exact (hmin w hwF (hwz.trans hzm)).trans hwz

/-- **A normal subposet containing `a` and `b` contains every minimal upper bound
of `a` and `b`.** Normality at `m` produces `c ∈ N ∩ ↓m` above `a` and `b`;
minimality forces `m ⊑ c`, so `c = m`. -/
theorem IsNormalIn.mem_of_isMinimalUpperBound {N : Set α} (hN : N ◁ A) {a b m : α}
    (ha : a ∈ N) (hb : b ∈ N) (hm : IsMinimalUpperBound A a b m) : m ∈ N := by
  obtain ⟨c, ⟨hcN, hcm⟩, hac, hbc⟩ :=
    hN.directedOn hm.mem a ⟨ha, hm.left_le⟩ b ⟨hb, hm.right_le⟩
  exact le_antisymm hcm (hm.min c (hN.subset hcN) hac hbc hcm) ▸ hcN

variable [OrderBot α]

/-- **The normal subposets of a Plotkin order are closed under arbitrary
intersection.** The witness for directedness is a minimal upper bound, which lies
in every member of the family at once. -/
theorem isNormalIn_sInter (h : IsPlotkinOrder A) (hbot : (⊥ : α) ∈ A) {M : Set (Set α)}
    (hMne : M.Nonempty) (hM : ∀ N ∈ M, N ◁ A) : (⋂₀ M) ◁ A := by
  obtain ⟨N₀, hN₀⟩ := hMne
  refine ⟨fun z hz => (hM N₀ hN₀).subset (Set.mem_sInter.mp hz N₀ hN₀), fun x hx => ⟨?_, ?_⟩⟩
  · exact ⟨⊥, Set.mem_sInter.mpr fun N hN => (hM N hN).bot_mem hbot, bot_le⟩
  · rintro a ⟨haI, hax⟩ b ⟨hbI, hbx⟩
    have haN₀ := Set.mem_sInter.mp haI N₀ hN₀
    have hbN₀ := Set.mem_sInter.mp hbI N₀ hN₀
    obtain ⟨c, ⟨hcN₀, hcx⟩, hac, hbc⟩ := (hM N₀ hN₀).directedOn hx a ⟨haN₀, hax⟩ b ⟨hbN₀, hbx⟩
    obtain ⟨m, hm, hmc⟩ := h.exists_isMinimalUpperBound ((hM N₀ hN₀).subset haN₀)
      ((hM N₀ hN₀).subset hbN₀) ((hM N₀ hN₀).subset hcN₀) hac hbc
    exact ⟨m, ⟨Set.mem_sInter.mpr fun N hN =>
        (hM N hN).mem_of_isMinimalUpperBound (Set.mem_sInter.mp haI N hN)
          (Set.mem_sInter.mp hbI N hN) hm,
      hmc.trans hcx⟩, hm.left_le, hm.right_le⟩

/-- The **least normal subposet of `A` containing `S`**, as the intersection of
all of them. Well behaved only because of `isNormalIn_sInter`. -/
def normalClosure (A S : Set α) : Set α := ⋂₀ {N | N ◁ A ∧ S ⊆ N}

omit [OrderBot α] in
theorem subset_normalClosure (A S : Set α) : S ⊆ normalClosure A S :=
  fun _ hz => Set.mem_sInter.mpr fun _ hN => hN.2 hz

omit [OrderBot α] in
theorem normalClosure_subset {S N : Set α} (hN : N ◁ A) (hSN : S ⊆ N) :
    normalClosure A S ⊆ N := fun _ hz => Set.mem_sInter.mp hz N ⟨hN, hSN⟩

theorem normalClosure_isNormalIn (h : IsPlotkinOrder A) (hbot : (⊥ : α) ∈ A) {S : Set α}
    (hSA : S ⊆ A) : (normalClosure A S) ◁ A :=
  isNormalIn_sInter h hbot ⟨A, IsNormalIn.refl A, hSA⟩ fun _ hN => hN.1

omit [OrderBot α] in
/-- For a **finite** `S` the least normal subposet containing it is finite: the
Plotkin condition supplies a finite normal `N ⊇ S`, and the closure is inside it.
This is what makes the compact elements of `Fp(D)` plentiful. -/
theorem normalClosure_finite (h : IsPlotkinOrder A) {S : Set α} (hSfin : S.Finite)
    (hSA : S ⊆ A) : (normalClosure A S).Finite := by
  obtain ⟨N, hNfin, hN, hSN⟩ := h S hSfin hSA
  exact hNfin.subset (normalClosure_subset hN hSN)

omit [PartialOrder α] [OrderBot α] in
/-- A finite subset of a `⊆`-directed union already sits inside one member. -/
theorem exists_mem_of_finite_subset_sUnion {M : Set (Set α)} (hMne : M.Nonempty)
    (hdir : DirectedOn (· ⊆ ·) M) {u : Set α} (hu : u.Finite) :
    u ⊆ ⋃₀ M → ∃ N ∈ M, u ⊆ N := by
  induction u, hu using Set.Finite.induction_on with
  | empty =>
    intro _
    obtain ⟨N, hN⟩ := hMne
    exact ⟨N, hN, Set.empty_subset _⟩
  | @insert a t _ _ ih =>
    intro hsub
    obtain ⟨N₁, hN₁, haN₁⟩ := hsub (Set.mem_insert a t)
    obtain ⟨N₂, hN₂, htN₂⟩ := ih fun y hy => hsub (Set.mem_insert_of_mem a hy)
    obtain ⟨N, hN, h₁, h₂⟩ := hdir N₁ hN₁ N₂ hN₂
    refine ⟨N, hN, ?_⟩
    rintro y (rfl | hy)
    · exact h₁ haN₁
    · exact h₂ (htN₂ hy)

end ClosureSystem

section FpLattice

variable [CompletePartialOrder α] [Domain α]

/-- `im(p) ∩ K(D)`, the normal subposet Theorem 6 assigns to a finitary
projection. It is the coordinate in which every statement below is proved. -/
def fpBasis (p : ↥(Fp α)) : Set α := Set.range ⇑p.val ∩ compacts α

omit [Domain α] in
theorem fpBasis_isNormalIn (p : ↥(Fp α)) : (fpBasis p) ◁ compacts α :=
  p.2.isNormalIn_compacts

/-- Theorem 6's second round trip: `p_{im(p) ∩ K(D)} = p`. -/
theorem normalHom_fpBasis (p : ↥(Fp α)) : normalHom (fpBasis_isNormalIn p) = p.val :=
  ScottHom.ext fun x => normalFun_range_inter_compacts p.2 x

/-- A normal subposet of `K(D)`, viewed inside `Fp(D)` — Theorem 6's other
direction. -/
noncomputable def toFp {N : Set α} (hN : N ◁ compacts α) : ↥(Fp α) :=
  ⟨normalHom hN, isFinitaryProjection_normalHom hN⟩

/-- Theorem 6's first round trip: `im(p_N) ∩ K(D) = N`. -/
@[simp] theorem fpBasis_toFp {N : Set α} (hN : N ◁ compacts α) : fpBasis (toFp hN) = N :=
  range_normalHom_inter_compacts hN

/-- **Theorem 6 as an order isomorphism.** The pointwise order on `Fp(D)` is
inclusion of bases: `⊆` gives `⊑` by `normalHom_mono`, and `⊑` gives `⊆` by
`IsProjection.range_mono`. -/
theorem Fp.le_iff_fpBasis_subset {p q : ↥(Fp α)} : p ≤ q ↔ fpBasis p ⊆ fpBasis q := by
  constructor
  · intro hpq
    exact Set.inter_subset_inter_left _
      (IsProjection.range_mono p.2.isProjection q.2.isProjection hpq)
  · intro hsub
    have := normalHom_mono (fpBasis_isNormalIn p) (fpBasis_isNormalIn q) hsub
    rwa [normalHom_fpBasis, normalHom_fpBasis] at this

/-- The family whose intersection is the meet of `S` in `Fp(D)`: the bases of the
members of `S`, together with `K(D)` itself so the family is never empty. -/
def fpMeetFamily (S : Set ↥(Fp α)) : Set (Set α) := insert (compacts α) (fpBasis '' S)

omit [Domain α] in
theorem fpMeetFamily_isNormalIn {S : Set ↥(Fp α)} :
    ∀ N ∈ fpMeetFamily S, N ◁ compacts α := by
  rintro _ (rfl | ⟨p, _, rfl⟩)
  · exact IsNormalIn.refl _
  · exact fpBasis_isNormalIn p

omit [Domain α] in
theorem fpMeet_isNormalIn (h : IsBifinite α) (S : Set ↥(Fp α)) :
    (⋂₀ fpMeetFamily S) ◁ compacts α :=
  isNormalIn_sInter h isCompactElement_bot ⟨_, Set.mem_insert _ _⟩ fpMeetFamily_isNormalIn

/-- **`Fp(D)` has all meets.** The meet of `S` is the projection of the
intersection of the bases, which is normal by `isNormalIn_sInter` — the step that
spends bifiniteness. -/
theorem isGLB_fpMeet (h : IsBifinite α) (S : Set ↥(Fp α)) :
    IsGLB S (toFp (fpMeet_isNormalIn h S)) := by
  constructor
  · intro p hp
    refine Fp.le_iff_fpBasis_subset.mpr ?_
    rw [fpBasis_toFp]
    exact fun z hz => Set.mem_sInter.mp hz _ (Set.mem_insert_of_mem _ ⟨p, hp, rfl⟩)
  · intro q hq
    refine Fp.le_iff_fpBasis_subset.mpr ?_
    rw [fpBasis_toFp]
    intro z hz
    refine Set.mem_sInter.mpr ?_
    rintro _ (rfl | ⟨p, hp, rfl⟩)
    · exact hz.2
    · exact Fp.le_iff_fpBasis_subset.mp (hq hp) hz

/-- **`Fp(D)` is a complete lattice.** Built from the meets, so the order is the
pointwise order it already had — `completeLatticeOfInf` splices in the ambient
`PartialOrder` rather than deriving a new one. -/
@[reducible] noncomputable def Fp.completeLattice (h : IsBifinite α) :
    CompleteLattice ↥(Fp α) :=
  @completeLatticeOfInf _ (inferInstance : PartialOrder ↥(Fp α))
    ⟨fun S => toFp (fpMeet_isNormalIn h S)⟩ (isGLB_fpMeet h)

/-- **The basis of a directed least upper bound is the union of the bases.** Only
the inclusion `⊆` is stated, which is the half compactness needs: the union is
normal (a `◁`-directed union of normal subposets), so the projection it
determines is an upper bound of `T`, hence above `w`. -/
theorem fpBasis_subset_sUnion_of_isLUB {T : Set ↥(Fp α)} (hTne : T.Nonempty)
    (hT : DirectedOn (· ≤ ·) T) {w : ↥(Fp α)} (hw : IsLUB T w) :
    fpBasis w ⊆ ⋃₀ (fpBasis '' T) := by
  have hdir : DirectedOn IsNormalIn (fpBasis '' T) := by
    rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩
    obtain ⟨s, hs, hps, hqs⟩ := hT p hp q hq
    exact ⟨fpBasis s, ⟨s, hs, rfl⟩,
      IsNormalIn.mono_right (Fp.le_iff_fpBasis_subset.mp hps) (fpBasis_isNormalIn s).subset
        (fpBasis_isNormalIn p),
      IsNormalIn.mono_right (Fp.le_iff_fpBasis_subset.mp hqs) (fpBasis_isNormalIn s).subset
        (fpBasis_isNormalIn q)⟩
  have hU : (⋃₀ (fpBasis '' T)) ◁ compacts α :=
    isNormalIn_sUnion (hTne.image _) (by rintro _ ⟨p, _, rfl⟩; exact fpBasis_isNormalIn p) hdir
  have hub : toFp hU ∈ upperBounds T := by
    intro p hp
    refine Fp.le_iff_fpBasis_subset.mpr ?_
    rw [fpBasis_toFp]
    exact fun z hz => ⟨fpBasis p, ⟨p, hp, rfl⟩, hz⟩
  have := Fp.le_iff_fpBasis_subset.mp (hw.2 hub)
  rwa [fpBasis_toFp] at this

/-- **A finitary projection with a finite basis is a compact element of
`Fp(D)`.** The basis of a directed least upper bound is the union of the bases,
and a finite set inside a directed union is inside one member. -/
theorem isCompactElement_toFp_of_finite {N : Set α} (hN : N ◁ compacts α) (hfin : N.Finite) :
    IsCompactElement (toFp hN) := by
  intro T w hTne hT hlub hle
  have hsub : N ⊆ ⋃₀ (fpBasis '' T) := by
    have h₁ : N ⊆ fpBasis w := by
      have := Fp.le_iff_fpBasis_subset.mp hle
      rwa [fpBasis_toFp] at this
    exact h₁.trans (fpBasis_subset_sUnion_of_isLUB hTne hT hlub)
  have hdir : DirectedOn (· ⊆ ·) (fpBasis '' T) := by
    rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩
    obtain ⟨s, hs, hps, hqs⟩ := hT p hp q hq
    exact ⟨fpBasis s, ⟨s, hs, rfl⟩, Fp.le_iff_fpBasis_subset.mp hps,
      Fp.le_iff_fpBasis_subset.mp hqs⟩
  obtain ⟨_, ⟨p, hp, rfl⟩, hNp⟩ :=
    exists_mem_of_finite_subset_sUnion (hTne.image _) hdir hfin hsub
  refine ⟨p, hp, Fp.le_iff_fpBasis_subset.mpr ?_⟩
  rwa [fpBasis_toFp]

/-- **Every finitary projection is the least upper bound of the compact ones
below it.** For each `k` in the basis of `p`, the least normal subposet
containing `{k}` is finite (`normalClosure_finite`) and lies inside the basis of
`p`, so the projection it determines is a compact element below `p` whose basis
contains `k`. -/
theorem isLUB_compactsBelow_fp (h : IsBifinite α) (p : ↥(Fp α)) :
    IsLUB {q : ↥(Fp α) | (fpBasis q).Finite ∧ q ≤ p} p := by
  constructor
  · exact fun q hq => hq.2
  · intro b hb
    refine Fp.le_iff_fpBasis_subset.mpr fun k hk => ?_
    have hkc : ({k} : Set α) ⊆ compacts α := Set.singleton_subset_iff.mpr hk.2
    have hcl : (normalClosure (compacts α) {k}) ◁ compacts α :=
      normalClosure_isNormalIn h isCompactElement_bot hkc
    have hclp : normalClosure (compacts α) {k} ⊆ fpBasis p :=
      normalClosure_subset (fpBasis_isNormalIn p) (Set.singleton_subset_iff.mpr hk)
    have hmem : toFp hcl ∈ {q : ↥(Fp α) | (fpBasis q).Finite ∧ q ≤ p} := by
      refine ⟨?_, Fp.le_iff_fpBasis_subset.mpr ?_⟩
      · rw [fpBasis_toFp]
        exact normalClosure_finite h (Set.finite_singleton k) hkc
      · rwa [fpBasis_toFp]
    have := Fp.le_iff_fpBasis_subset.mp (hb hmem)
    rw [fpBasis_toFp] at this
    exact this (subset_normalClosure _ _ rfl)

/-- **Theorem 16's content.** `Fp(D)` is compactly generated: every element is
the supremum of the compact elements below it, the compact elements being the
projections with a finite basis. -/
theorem Fp.isCompactlyGenerated (h : IsBifinite α) :
    @IsCompactlyGenerated _ (Fp.completeLattice h) := by
  letI : CompleteLattice ↥(Fp α) := Fp.completeLattice h
  refine ⟨fun p => ⟨{q : ↥(Fp α) | (fpBasis q).Finite ∧ q ≤ p}, ?_, ?_⟩⟩
  · rintro q ⟨hfin, -⟩
    have hq : toFp (fpBasis_isNormalIn q) = q := Subtype.ext (normalHom_fpBasis q)
    exact hq ▸ isCompactElement_toFp_of_finite (fpBasis_isNormalIn q) hfin
  · exact (isLUB_sSup _).unique (isLUB_compactsBelow_fp h p)

end FpLattice

end ScottDomains
