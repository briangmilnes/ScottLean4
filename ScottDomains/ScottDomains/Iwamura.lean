import ScottDomains.JungNets
import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.SetTheory.Ordinal.Basic

/-!
# Iwamura's lemma and Markowsky's theorem: chain-complete implies directed-complete

This file supplies **Jung 1989, Theorem 1.2** — "a partially ordered set `D` is a
dcpo if and only if each chain in `D` has a supremum" — which Jung attributes to
Iwamura and does not prove, and which `ScottDomains/JungNets.lean` measured to be
absent from Mathlib. It is the first and largest of the five dependencies of
Jung's Theorem 1.37.

The nontrivial direction is *chain-complete ⟹ directed-complete*, and it is
proved here from a hypothesis weaker still: suprema of **well-ordered** chains.
Three consequences, in increasing usefulness to this development:

1. `hasDirectedSuprema_of_hasWellOrderedSuprema` — Markowsky's theorem.
2. `hasChainInfima_of_hasWellOrderedInfima` — its dual, which is **Jung's
   Corollary 1.3 as he uses it**: finding infima for monotone injective nets
   indexed by an ordinal suffices to have infima for all chains.
3. `thm137Chains_of_wellOrderedInfima` — so `JungNets.Thm137Chains D`, the only
   form of Theorem 1.37 the route to Theorem 18 actually spends, follows from the
   ordinal-indexed case alone. `thm137Chains_iff_thm137` records that the chain
   form and the bicompleteness form are now the same proposition.

## What is proved

* `close` — the **directed closure** of a subset of a directed set `t`: iterate
  "adjoin a chosen upper bound of each pair" `ω` times. It is directed, contained
  in `t`, monotone in its argument, and of cardinality at most
  `max (#E) ℵ₀`.
* `exists_isLUB_of_countable` — the countable case, proved directly and without
  cardinal induction: enumerate `t` as `f : ℕ → D`, build a monotone `v : ℕ → t`
  with `f n ≤ v n`, and take the supremum of the chain `range v`.
* `exists_chain_directed_cover` — **Iwamura's lemma**: a directed set `t` of
  infinite cardinality `κ` is the union of a `⊆`-chain of nonempty directed
  subsets each of cardinality `< κ`. Two constructions, one per case: for
  `κ = ℵ₀` the finite sets `f '' Iic n ∪ v '' Iic n`, which are directed because
  `v n` is a greatest element of each; for `κ > ℵ₀` the directed closures
  `close ub (e '' Iic a)` indexed by `κ.ord.ToType`.
* `hasDirectedSuprema_of_hasWellOrderedSuprema` — **Markowsky's theorem**, by
  strong induction on `#t` over the well-founded order on `Cardinal`: countable
  sets by the direct construction, uncountable ones by applying the induction
  hypothesis to each member of the Iwamura cover and taking the supremum of the
  resulting chain of suprema. That chain is well-ordered, which is why the
  well-ordered hypothesis suffices.
* `hasChainSuprema_of_hasWellOrderedSuprema` — suprema of well-ordered chains
  give suprema of *all* chains, obtained free of charge because a chain is a
  directed set. This replaces the direct argument (every chain has a cofinal
  well-ordered subset), which is not proved here and is not needed.
* `hasChainInfima_of_hasWellOrderedInfima`, `isBicomplete_of_hasChainInfima`,
  `thm137Chains_of_wellOrderedInfima`, `thm137Chains_iff_thm137` — the dual
  forms, obtained by instantiating the theorems at `Dᵒᵈ`, and the consequences
  for `JungNets`.

No `sorry` and no new axioms: the proof uses `Classical.choice` (for the choice
of upper bounds, for the well-ordering of `t` at its own cardinality, and inside
Mathlib's cardinal arithmetic), `propext` and `Quot.sound`.

## Why the countable case is separate

Iwamura's lemma at `κ = ℵ₀` asks for a chain of **finite** directed subsets, and
the `ω`-iterated directed closure of a finite set is in general infinite, so the
closure construction proves the lemma only for `ℵ₀ < κ`. The two constructions
below are therefore genuinely different, and `exists_chain_directed_cover` splits
on `ℵ₀ < #t` for that reason and no other. Markowsky's theorem does not need the
`κ = ℵ₀` case of Iwamura's lemma at all — the countable case is settled outright
by `exists_isLUB_of_countable` — but the lemma is stated in full because it is
the named result.

## Relation to Jung's use of it

Jung uses Corollary 1.3 to reduce the search for infima to *monotone injective
nets indexed by an ordinal*, which is what makes his retraction onto `A ∪ αᵒᵖ`
well defined. `hasChainInfima_of_hasWellOrderedInfima` is that reduction: a
proof of Theorem 1.37 may assume a well-ordered index throughout and never return
to arbitrary chains or filtered sets.

The step from a well-ordered chain to an arbitrary one is *not* proved here by
the direct argument (every linear order has a coinitial well-ordered subset,
which needs Zorn over initial segments). It comes out of Markowsky's theorem
instead: an arbitrary chain is in particular a directed set, so the directed
conclusion already covers it. That is why the whole file costs one transfinite
induction and no second one.
-/

namespace ScottDomains.Iwamura

open Cardinal Ordinal Set

universe u

/-! ## Chain-, well-ordered- and directed-completeness as predicates -/

/-- A subset is **well-ordered** when every nonempty subset of it has a least
element. For a chain this is the order-theoretic well-ordering condition, so such
a `c` is order-isomorphic to an ordinal and its inclusion into `D` is a monotone
injective net indexed by that ordinal — the shape Jung's Corollary 1.3 delivers
its reduction in. -/
def IsWellOrderedSet {D : Type*} [Preorder D] (c : Set D) : Prop :=
  ∀ S ⊆ c, S.Nonempty → ∃ m ∈ S, ∀ x ∈ S, m ≤ x

/-- Every nonempty **well-ordered chain** has a least upper bound. This is the
weakest of the three hypotheses in this file, and the one Markowsky's theorem is
proved from. -/
def HasWellOrderedSuprema (D : Type*) [Preorder D] : Prop :=
  ∀ c : Set D, c.Nonempty → IsChain (· ≤ ·) c → IsWellOrderedSet c → ∃ u, IsLUB c u

/-- Every nonempty **chain** has a least upper bound. -/
def HasChainSuprema (D : Type*) [Preorder D] : Prop :=
  ∀ c : Set D, c.Nonempty → IsChain (· ≤ ·) c → ∃ u, IsLUB c u

/-- Every nonempty **directed** set has a least upper bound. -/
def HasDirectedSuprema (D : Type*) [Preorder D] : Prop :=
  ∀ t : Set D, t.Nonempty → DirectedOn (· ≤ ·) t → ∃ u, IsLUB t u

theorem HasChainSuprema.hasWellOrderedSuprema {D : Type*} [Preorder D]
    (h : HasChainSuprema D) : HasWellOrderedSuprema D :=
  fun c hne hc _ => h c hne hc

/-- Every nonempty chain is directed, so directed-completeness implies
chain-completeness. This is `JungNets.IsBicomplete.hasChainInfima` in the sup
form; both directions of the equivalence therefore hold. -/
theorem HasDirectedSuprema.hasChainSuprema {D : Type*} [Preorder D]
    (h : HasDirectedSuprema D) : HasChainSuprema D :=
  fun c hne hc => h c hne hc.directedOn

/-- **The range of a monotone map out of a well-ordered index is well-ordered.**
Given `S ⊆ range g` nonempty, the preimage `{a | g a ∈ S}` is nonempty, hence has
a `<`-minimal element `a₀`; linearity of the index turns minimality into
`a₀ ≤ b` for every `b` in the preimage, and monotonicity of `g` sends that to
`g a₀ ≤ g b`. So `g a₀` is a least element of `S`. -/
theorem isWellOrderedSet_range {D : Type*} [Preorder D] {ι : Type*} [LinearOrder ι]
    [WellFoundedLT ι] {g : ι → D} (hg : Monotone g) : IsWellOrderedSet (Set.range g) := by
  intro S hS hne
  obtain ⟨y, hy⟩ := hne
  have hT : {a : ι | g a ∈ S}.Nonempty := by
    obtain ⟨a, ha⟩ := hS hy
    exact ⟨a, show g a ∈ S by rw [ha]; exact hy⟩
  obtain ⟨a₀, ha₀, hmin⟩ := wellFounded_lt.has_min _ hT
  refine ⟨g a₀, ha₀, ?_⟩
  intro x hx
  obtain ⟨b, rfl⟩ := hS hx
  exact hg (not_lt.1 (hmin b hx))

/-- The same, for a family indexed by a **well-ordered set** rather than by a
well-founded type: if `c` is well-ordered and `g : c → E` is monotone then
`range g` is well-ordered. Used with `c` the Iwamura chain and `g` the choice of
supremum on each of its members. -/
theorem isWellOrderedSet_range_of_set {D E : Type*} [Preorder D] [Preorder E]
    {c : Set D} (hc : IsWellOrderedSet c) {g : c → E}
    (hg : ∀ x y : c, (x : D) ≤ (y : D) → g x ≤ g y) : IsWellOrderedSet (Set.range g) := by
  intro S hS hne
  obtain ⟨y, hy⟩ := hne
  obtain ⟨p₀, hp₀⟩ := hS hy
  obtain ⟨m, ⟨q, hq, hqm⟩, hmin⟩ :=
    hc (Subtype.val '' {p : c | g p ∈ S}) (by rintro _ ⟨p, -, rfl⟩; exact p.2)
      ⟨(p₀ : D), p₀, show g p₀ ∈ S by rw [hp₀]; exact hy, rfl⟩
  refine ⟨g q, hq, ?_⟩
  intro x hx
  obtain ⟨p, rfl⟩ := hS hx
  refine hg q p ?_
  rw [hqm]
  exact hmin (p : D) ⟨p, hx, rfl⟩

/-! ## The directed closure

Throughout this section `t : Set D` is directed and `ub : t → t → t` is a chosen
upper-bound operation on it. `close ub E` is the least directed subset of `t`
containing `E` that this choice generates: adjoin `ub x y` for every pair, and
iterate `ω` times. Working inside the subtype `↥t` rather than with subsets of
`D` carrying a `⊆ t` side condition keeps the cardinality bookkeeping to
`Cardinal.mk_image_eq` at the end.
-/

section Closure

variable {D : Type u} {t : Set D} (ub : t → t → t)

/-- One step of the directed closure: adjoin `ub x y` for every pair `x, y ∈ E`. -/
def step (E : Set t) : Set t :=
  E ∪ Set.range fun p : ↥E × ↥E => ub p.1.1 p.2.1

theorem subset_step (E : Set t) : E ⊆ step ub E := Set.subset_union_left

theorem step_mono {E F : Set t} (h : E ⊆ F) : step ub E ⊆ step ub F := by
  rintro x (hx | ⟨p, rfl⟩)
  · exact Set.mem_union_left _ (h hx)
  · exact Set.mem_union_right _ ⟨(⟨p.1.1, h p.1.2⟩, ⟨p.2.1, h p.2.2⟩), rfl⟩

theorem iterate_subset_succ (E : Set t) (n : ℕ) :
    (step ub)^[n] E ⊆ (step ub)^[n + 1] E := by
  rw [Function.iterate_succ_apply']
  exact subset_step ub _

theorem iterate_mono_index (E : Set t) : Monotone fun n => (step ub)^[n] E :=
  monotone_nat_of_le_succ fun n => iterate_subset_succ ub E n

theorem iterate_mono_arg {E F : Set t} (h : E ⊆ F) (n : ℕ) :
    (step ub)^[n] E ⊆ (step ub)^[n] F := by
  induction n with
  | zero => exact h
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact step_mono ub ih

/-- The **directed closure** of `E` inside `t`: `ω` iterations of `step`.
`ULift.{u} ℕ` rather than `ℕ` so that the index type sits in the same universe as
`↥t`, which is what `Cardinal.mk_iUnion_le` requires. -/
def close (E : Set t) : Set t :=
  ⋃ n : ULift.{u} ℕ, (step ub)^[n.down] E

theorem mem_close {E : Set t} {x : t} (n : ℕ) (hx : x ∈ (step ub)^[n] E) :
    x ∈ close ub E :=
  Set.mem_iUnion.2 ⟨⟨n⟩, hx⟩

theorem exists_of_mem_close {E : Set t} {x : t} (hx : x ∈ close ub E) :
    ∃ n : ℕ, x ∈ (step ub)^[n] E := by
  obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hx
  exact ⟨n.down, hn⟩

theorem subset_close (E : Set t) : E ⊆ close ub E := fun _ hx => mem_close ub 0 hx

theorem close_mono {E F : Set t} (h : E ⊆ F) : close ub E ⊆ close ub F := by
  intro x hx
  obtain ⟨n, hn⟩ := exists_of_mem_close ub hx
  exact mem_close ub n (iterate_mono_arg ub h n hn)

/-- `close ub E` is directed: any two of its members appear at a common stage `k`,
and their chosen upper bound then appears at stage `k + 1`. -/
theorem close_directedOn [Preorder D] (hub₁ : ∀ x y : t, (x : D) ≤ ub x y)
    (hub₂ : ∀ x y : t, (y : D) ≤ ub x y) (E : Set t) :
    DirectedOn (· ≤ ·) (close ub E) := by
  intro x hx y hy
  obtain ⟨m, hm⟩ := exists_of_mem_close ub hx
  obtain ⟨n, hn⟩ := exists_of_mem_close ub hy
  have hxk : x ∈ (step ub)^[max m n] E := iterate_mono_index ub E (le_max_left m n) hm
  have hyk : y ∈ (step ub)^[max m n] E := iterate_mono_index ub E (le_max_right m n) hn
  refine ⟨ub x y, mem_close ub (max m n + 1) ?_, hub₁ x y, hub₂ x y⟩
  rw [Function.iterate_succ_apply']
  exact Set.mem_union_right _ ⟨(⟨x, hxk⟩, ⟨y, hyk⟩), rfl⟩

theorem mk_step_le {E : Set t} {c : Cardinal.{u}} (hc : ℵ₀ ≤ c) (hE : #E ≤ c) :
    #(step ub E) ≤ c := by
  have hprod : #(↥E × ↥E) ≤ c := by
    have : #(↥E × ↥E) = #E * #E := by simp
    rw [this]
    exact (mul_le_mul' hE hE).trans_eq (Cardinal.mul_eq_self hc)
  refine (Cardinal.mk_union_le _ _).trans ?_
  refine le_trans (add_le_add hE (Cardinal.mk_range_le.trans hprod)) ?_
  exact (Cardinal.add_eq_self hc).le

theorem mk_iterate_le {E : Set t} {c : Cardinal.{u}} (hc : ℵ₀ ≤ c) (hE : #E ≤ c) :
    ∀ n : ℕ, #((step ub)^[n] E) ≤ c := by
  intro n
  induction n with
  | zero => exact hE
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact mk_step_le ub hc ih

/-- The closure of `E` has cardinality at most any infinite bound on `#E`: it is a
countable union of stages, each of cardinality at most `c`, and `ℵ₀ * c = c`. -/
theorem mk_close_le {E : Set t} {c : Cardinal.{u}} (hc : ℵ₀ ≤ c) (hE : #E ≤ c) :
    #(close ub E) ≤ c := by
  have hsup : (⨆ i : ULift.{u} ℕ, #((step ub)^[i.down] E)) ≤ c :=
    ciSup_le fun i => mk_iterate_le ub hc hE i.down
  have hnat : #(ULift.{u} ℕ) = ℵ₀ := by simp
  refine (Cardinal.mk_iUnion_le _).trans ?_
  rw [hnat]
  exact (mul_le_mul' le_rfl hsup).trans_eq (Cardinal.aleph0_mul_eq hc)

end Closure

/-! ## Choosing upper bounds inside a directed set -/

/-- A directed set carries a chosen binary upper-bound operation on its subtype.
This is the one use of choice that is specific to this file; the rest is
Mathlib's. -/
theorem exists_ub_fun {D : Type u} [Preorder D] {t : Set D} (hdir : DirectedOn (· ≤ ·) t) :
    ∃ ub : t → t → t, (∀ x y : t, (x : D) ≤ ub x y) ∧ (∀ x y : t, (y : D) ≤ ub x y) := by
  have h : ∀ x y : t, ∃ z : t, (x : D) ≤ z ∧ (y : D) ≤ z := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩
    obtain ⟨z, hz, h₁, h₂⟩ := hdir x hx y hy
    exact ⟨⟨z, hz⟩, h₁, h₂⟩
  choose ub h₁ h₂ using h
  exact ⟨ub, h₁, h₂⟩

/-! ## The countable case, without cardinal induction -/

/-- A nonempty countable directed set has a supremum as soon as chains do.

Enumerate `t` as `f : ℕ → D` and build `v : ℕ → t` by `v 0 = f 0`,
`v (n+1) = ub (v n) (f (n+1))`. Then `v` is monotone, so `range v` is a chain;
its supremum `w` exists by hypothesis, dominates every `f n ≤ v n`, hence all of
`t`, and is below every upper bound of `t` because each `v n` lies in `t`. -/
theorem exists_isLUB_of_countable {D : Type u} [Preorder D] (h : HasWellOrderedSuprema D)
    {t : Set D} (hcnt : t.Countable) (hne : t.Nonempty) (hdir : DirectedOn (· ≤ ·) t) :
    ∃ w, IsLUB t w := by
  obtain ⟨f, hf⟩ := hcnt.exists_eq_range hne
  have hfm : ∀ n, f n ∈ t := by
    intro n; rw [hf]; exact Set.mem_range_self n
  obtain ⟨ub, hub₁, hub₂⟩ := exists_ub_fun hdir
  obtain ⟨d, hdc⟩ : ∃ d : ℕ → t, ∀ n, (d n : D) = f n :=
    ⟨fun n => ⟨f n, hfm n⟩, fun _ => rfl⟩
  obtain ⟨v, hv0, hvs⟩ :
      ∃ v : ℕ → t, v 0 = d 0 ∧ ∀ n, v (n + 1) = ub (v n) (d (n + 1)) :=
    ⟨fun n => Nat.rec (d 0) (fun k w => ub w (d (k + 1))) n, rfl, fun _ => rfl⟩
  have hvmono : Monotone fun n => ((v n : D)) := by
    apply monotone_nat_of_le_succ
    intro n
    rw [hvs n]
    exact hub₁ _ _
  have hdv : ∀ n, f n ≤ (v n : D) := by
    intro n
    cases n with
    | zero => exact le_of_eq (by rw [hv0, hdc 0])
    | succ k => rw [hvs k, ← hdc (k + 1)]; exact hub₂ _ _
  obtain ⟨w, hw⟩ := h (Set.range fun n => ((v n : D)))
    ⟨(v 0 : D), ⟨0, rfl⟩⟩ hvmono.isChain_range (isWellOrderedSet_range hvmono)
  refine ⟨w, ?_, ?_⟩
  · intro x hx
    rw [hf] at hx
    obtain ⟨n, rfl⟩ := hx
    exact (hdv n).trans (hw.1 ⟨n, rfl⟩)
  · intro y hy
    refine hw.2 ?_
    rintro _ ⟨n, rfl⟩
    exact hy (v n).2

/-! ## Iwamura's lemma -/

/-- **Iwamura's lemma** (Jung 1989, the content of his Theorem 1.2).

A directed set `t` of infinite cardinality `κ` is the union of a `⊆`-chain of
nonempty directed subsets, each of cardinality `< κ`. The chain is moreover
**well-ordered** by `⊆`, because in both constructions it is the range of a
monotone map out of a well-founded index; that extra clause is what makes the
weaker hypothesis `HasWellOrderedSuprema` enough in Markowsky's theorem below.

Two constructions, split on `ℵ₀ < #t`:

* `#t = ℵ₀`: enumerate `t` as `f : ℕ → D` and take the **finite** sets
  `f '' Iic n ∪ v '' Iic n` with `v` the monotone sequence of
  `exists_isLUB_of_countable`. Each is directed because `v n` is a greatest
  element of it, and they increase with `n`.
* `ℵ₀ < #t`: well-order `t` in order type `(#t).ord` and take the directed
  closures `close ub (e '' Iic a)`. Each has cardinality at most
  `max (#(Iic a)) ℵ₀ < #t`, and they increase with `a`.

The `ω`-iterated closure of a finite set is in general infinite, which is exactly
why the first case cannot be run through `close`. -/
theorem exists_chain_directed_cover {D : Type u} [Preorder D] {t : Set D}
    (hdir : DirectedOn (· ≤ ·) t) (hinf : ℵ₀ ≤ #t) :
    ∃ 𝒞 : Set (Set D), IsChain (· ⊆ ·) 𝒞 ∧ IsWellOrderedSet 𝒞 ∧
      (∀ A ∈ 𝒞, A ⊆ t ∧ A.Nonempty ∧ DirectedOn (· ≤ ·) A ∧ #A < #t) ∧ ⋃₀ 𝒞 = t := by
  have hne : t.Nonempty := by
    rcases Set.eq_empty_or_nonempty t with rfl | hne
    · rw [show #(↥(∅ : Set D)) = 0 from Cardinal.mk_eq_zero _] at hinf
      exact absurd (Cardinal.aleph0_pos.trans_le hinf) (lt_irrefl 0)
    · exact hne
  obtain ⟨ub, hub₁, hub₂⟩ := exists_ub_fun hdir
  rcases eq_or_lt_of_le hinf with hcard | hcard
  · -- `#t = ℵ₀`: the finite stages `f '' Iic n ∪ v '' Iic n`.
    have hcnt : t.Countable := Cardinal.le_aleph0_iff_set_countable.1 hcard.ge
    obtain ⟨f, hf⟩ := hcnt.exists_eq_range hne
    have hfm : ∀ n, f n ∈ t := by
      intro n; rw [hf]; exact Set.mem_range_self n
    obtain ⟨d, hdc⟩ : ∃ d : ℕ → t, ∀ n, (d n : D) = f n :=
      ⟨fun n => ⟨f n, hfm n⟩, fun _ => rfl⟩
    obtain ⟨v, hv0, hvs⟩ :
        ∃ v : ℕ → t, v 0 = d 0 ∧ ∀ n, v (n + 1) = ub (v n) (d (n + 1)) :=
      ⟨fun n => Nat.rec (d 0) (fun k w => ub w (d (k + 1))) n, rfl, fun _ => rfl⟩
    have hvmono : Monotone fun n => ((v n : D)) := by
      apply monotone_nat_of_le_succ
      intro n
      rw [hvs n]
      exact hub₁ _ _
    have hdv : ∀ n, f n ≤ (v n : D) := by
      intro n
      cases n with
      | zero => exact le_of_eq (by rw [hv0, hdc 0])
      | succ k => rw [hvs k, ← hdc (k + 1)]; exact hub₂ _ _
    set A : ℕ → Set D := fun n => (f '' Set.Iic n) ∪ ((fun k => (v k : D)) '' Set.Iic n) with hA
    have hAmono : Monotone A := by
      intro m n hmn
      exact Set.union_subset_union (Set.image_mono (Set.Iic_subset_Iic.2 hmn))
        (Set.image_mono (Set.Iic_subset_Iic.2 hmn))
    have hAtop : ∀ n, ∀ x ∈ A n, x ≤ (v n : D) := by
      rintro n x (⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩)
      · exact (hdv k).trans (hvmono hk)
      · exact hvmono hk
    refine ⟨Set.range A, hAmono.isChain_range, isWellOrderedSet_range hAmono, ?_, ?_⟩
    · rintro _ ⟨n, rfl⟩
      refine ⟨?_, ⟨f n, Or.inl ⟨n, Set.self_mem_Iic, rfl⟩⟩, ?_, ?_⟩
      · rintro x (⟨k, _, rfl⟩ | ⟨k, _, rfl⟩)
        · exact hfm k
        · exact (v k).2
      · intro x hx y hy
        exact ⟨(v n : D), Or.inr ⟨n, Set.self_mem_Iic, rfl⟩, hAtop n x hx, hAtop n y hy⟩
      · rw [← hcard]
        exact (((Set.finite_Iic n).image f).union ((Set.finite_Iic n).image _)).lt_aleph0
    · apply Set.Subset.antisymm
      · rintro x ⟨_, ⟨n, rfl⟩, hx⟩
        rcases hx with ⟨k, _, rfl⟩ | ⟨k, _, rfl⟩
        · exact hfm k
        · exact (v k).2
      · intro x hx
        rw [hf] at hx
        obtain ⟨n, rfl⟩ := hx
        exact ⟨A n, ⟨n, rfl⟩, Or.inl ⟨n, Set.self_mem_Iic, rfl⟩⟩
  · -- `ℵ₀ < #t`: the directed closures of initial segments of a well-ordering.
    have hmk : #((#t).ord.ToType) = #t := Cardinal.mk_ord_toType _
    obtain ⟨e⟩ : Nonempty ((#t).ord.ToType ≃ t) := Cardinal.eq.1 (by rw [hmk])
    have hord : Cardinal.ord #((#t).ord.ToType) = typeLT ((#t).ord.ToType) := by
      rw [hmk, Ordinal.type_toType]
    set F : (#t).ord.ToType → Set D :=
      fun a => Subtype.val '' close ub ((⇑e) '' Set.Iic a) with hF
    have hFsub : ∀ a, F a ⊆ t := by
      rintro a x ⟨y, -, rfl⟩
      exact y.2
    have hFmono : Monotone F := fun a b hab =>
      Set.image_mono (close_mono ub (Set.image_mono (Set.Iic_subset_Iic.2 hab)))
    have hFne : ∀ a, (F a).Nonempty :=
      fun a => ⟨(e a : D), ⟨e a, subset_close ub _ ⟨a, Set.self_mem_Iic, rfl⟩, rfl⟩⟩
    have hFdir : ∀ a, DirectedOn (· ≤ ·) (F a) := fun a =>
      DirectedOn.mono_comp (g := Subtype.val) (fun _ _ h => h)
        (close_directedOn ub hub₁ hub₂ _)
    have hFcard : ∀ a, #(F a) < #t := by
      intro a
      have hIio : #(Set.Iio a) < #t := by
        have := Cardinal.mk_Iio_lt (α := (#t).ord.ToType) a hord
        rwa [hmk] at this
      have hIic : #(Set.Iic a) < #t := by
        rw [← Set.Iio_insert]
        refine lt_of_le_of_lt Cardinal.mk_insert_le ?_
        exact Cardinal.add_lt_of_lt hcard.le hIio (Cardinal.one_lt_aleph0.trans hcard)
      have himg : #((⇑e) '' Set.Iic a) ≤ max (#(Set.Iic a)) ℵ₀ :=
        Cardinal.mk_image_le.trans (le_max_left _ _)
      have hcl : #(close ub ((⇑e) '' Set.Iic a)) ≤ max (#(Set.Iic a)) ℵ₀ :=
        mk_close_le ub (le_max_right _ _) himg
      have := (Cardinal.mk_image_eq (f := (Subtype.val : t → D)) Subtype.val_injective
        (s := close ub ((⇑e) '' Set.Iic a))).le.trans hcl
      exact lt_of_le_of_lt this (max_lt hIic hcard)
    refine ⟨Set.range F, hFmono.isChain_range, isWellOrderedSet_range hFmono, ?_, ?_⟩
    · rintro _ ⟨a, rfl⟩
      exact ⟨hFsub a, hFne a, hFdir a, hFcard a⟩
    · apply Set.Subset.antisymm
      · rintro x ⟨_, ⟨a, rfl⟩, hx⟩
        exact hFsub a hx
      · intro x hx
        refine ⟨F (e.symm ⟨x, hx⟩), ⟨e.symm ⟨x, hx⟩, rfl⟩, ⟨x, hx⟩, ?_, rfl⟩
        refine subset_close ub _ ⟨e.symm ⟨x, hx⟩, Set.self_mem_Iic, ?_⟩
        exact e.apply_symm_apply _

/-! ## Markowsky's theorem -/

/-- **Well-ordered-chain-complete implies directed-complete.** If every nonempty
**well-ordered** chain of `D` has a least upper bound then so does every nonempty
directed subset. This is the strongest form: the hypothesis is Jung's Corollary
1.3 verbatim — suprema are needed only for monotone injective nets indexed by an
ordinal — and every stronger completeness hypothesis follows from the conclusion.

The proof is strong induction on `#t` along the well-founded order on `Cardinal`.
A countable `t` is settled outright by `exists_isLUB_of_countable`. For an
uncountable `t`, Iwamura's lemma writes `t = ⋃₀ 𝒞` with `𝒞` a well-ordered
`⊆`-chain of directed sets of strictly smaller cardinality; the induction
hypothesis gives each `A ∈ 𝒞` a supremum `g A`; `IsLUB.mono` makes
`{g A | A ∈ 𝒞}` a chain, and `isWellOrderedSet_range_of_set` makes it a
well-ordered one, so its supremum exists by hypothesis and is the supremum of
`t`. -/
theorem hasDirectedSuprema_of_hasWellOrderedSuprema {D : Type u} [Preorder D]
    (h : HasWellOrderedSuprema D) : HasDirectedSuprema D := by
  have key : ∀ κ : Cardinal.{u}, ∀ t : Set D, #t = κ → t.Nonempty →
      DirectedOn (· ≤ ·) t → ∃ w, IsLUB t w := by
    refine fun κ => Cardinal.lt_wf.induction (C := fun κ => ∀ t : Set D, #t = κ → t.Nonempty →
      DirectedOn (· ≤ ·) t → ∃ w, IsLUB t w) κ ?_
    rintro κ IH t rfl hne hdir
    by_cases hcnt : t.Countable
    · exact exists_isLUB_of_countable h hcnt hne hdir
    have hcard : ℵ₀ < #t :=
      not_le.1 fun hle => hcnt (Cardinal.le_aleph0_iff_set_countable.1 hle)
    obtain ⟨𝒞, hchain, hwo, hmem, hcover⟩ := exists_chain_directed_cover hdir hcard.le
    have hlub : ∀ A : 𝒞, ∃ w, IsLUB (A : Set D) w := by
      rintro ⟨A, hA⟩
      obtain ⟨-, hAne, hAdir, hAcard⟩ := hmem A hA
      exact IH _ hAcard A rfl hAne hAdir
    choose g hg using hlub
    have hgchain : IsChain (· ≤ ·) (Set.range g) := by
      rintro _ ⟨A, rfl⟩ _ ⟨B, rfl⟩ -
      rcases eq_or_ne (A : Set D) (B : Set D) with hAB | hAB
      · left
        exact (hg A).mono (hg B) hAB.le
      · rcases hchain A.2 B.2 hAB with hsub | hsub
        · exact Or.inl ((hg A).mono (hg B) hsub)
        · exact Or.inr ((hg B).mono (hg A) hsub)
    have h𝒞ne : Nonempty 𝒞 := by
      obtain ⟨x, hx⟩ := hne
      rw [← hcover] at hx
      obtain ⟨A, hA, -⟩ := hx
      exact ⟨⟨A, hA⟩⟩
    obtain ⟨A₀⟩ := h𝒞ne
    have hgwo : IsWellOrderedSet (Set.range g) :=
      isWellOrderedSet_range_of_set hwo fun A B hAB => (hg A).mono (hg B) hAB
    obtain ⟨w, hw⟩ := h (Set.range g) ⟨g A₀, ⟨A₀, rfl⟩⟩ hgchain hgwo
    refine ⟨w, ?_, ?_⟩
    · intro x hx
      rw [← hcover] at hx
      obtain ⟨A, hA, hxA⟩ := hx
      exact ((hg ⟨A, hA⟩).1 hxA).trans (hw.1 ⟨⟨A, hA⟩, rfl⟩)
    · intro y hy
      refine hw.2 ?_
      rintro _ ⟨A, rfl⟩
      refine (hg A).2 fun z hz => hy ?_
      rw [← hcover]
      exact ⟨A, A.2, hz⟩
  exact fun t hne hdir => key _ t rfl hne hdir

/-- **Chain-complete implies directed-complete** — Markowsky's theorem in the
form Jung's Theorem 1.2 states it. A weakening of the previous theorem, since a
chain hypothesis subsumes a well-ordered-chain one. -/
theorem hasDirectedSuprema_of_hasChainSuprema {D : Type u} [Preorder D]
    (h : HasChainSuprema D) : HasDirectedSuprema D :=
  hasDirectedSuprema_of_hasWellOrderedSuprema h.hasWellOrderedSuprema

/-- **Suprema of well-ordered chains give suprema of all chains.**

This is the consequence the round actually spends, and it is obtained for free:
a nonempty chain is a nonempty directed set, so the theorem above already covers
it. Formalizing the direct argument — every chain has a cofinal well-ordered
subset — is therefore unnecessary; the detour through directed sets replaces it.

The three completeness hypotheses are consequently all equivalent:
`HasWellOrderedSuprema ↔ HasChainSuprema ↔ HasDirectedSuprema`. -/
theorem hasChainSuprema_of_hasWellOrderedSuprema {D : Type u} [Preorder D]
    (h : HasWellOrderedSuprema D) : HasChainSuprema D :=
  (hasDirectedSuprema_of_hasWellOrderedSuprema h).hasChainSuprema

theorem hasWellOrderedSuprema_iff_hasChainSuprema {D : Type u} [Preorder D] :
    HasWellOrderedSuprema D ↔ HasChainSuprema D :=
  ⟨hasChainSuprema_of_hasWellOrderedSuprema, HasChainSuprema.hasWellOrderedSuprema⟩

theorem hasChainSuprema_iff_hasDirectedSuprema {D : Type u} [Preorder D] :
    HasChainSuprema D ↔ HasDirectedSuprema D :=
  ⟨hasDirectedSuprema_of_hasChainSuprema, HasDirectedSuprema.hasChainSuprema⟩

/-! ## The dual form, and what it discharges in `JungNets`

The development spends only `JungNets.Thm137Chains` — infima of nonempty
**chains** — because `JungNets.exists_minimal_upperBounds_le` obtains property m
by Zorn's lemma downwards, and Zorn quantifies over chains. The results below are
therefore stated so that the *weakest* hypothesis, infima of nonempty
**reverse-well-ordered** chains, already discharges it. That hypothesis is Jung's
Corollary 1.3 as he uses it: "we have to find infima only for monotone injective
nets `s : αᵒᵖ → D` where `α` is an ordinal number".
-/

/-- Every nonempty chain whose every nonempty subset has a **greatest** element
has a greatest lower bound. Dually to `IsWellOrderedSet`, such a chain is
order-isomorphic to `αᵒᵖ` for an ordinal `α`, so this predicate is exactly the
hypothesis Jung's Corollary 1.3 leaves to be discharged. -/
def HasWellOrderedInfima (D : Type*) [Preorder D] : Prop :=
  ∀ c : Set D, c.Nonempty → IsChain (· ≤ ·) c →
    (∀ S ⊆ c, S.Nonempty → ∃ m ∈ S, ∀ x ∈ S, x ≤ m) → ∃ i, IsGLB c i

/-- **Jung's Corollary 1.3, dually and in the form the development consumes.**
Infima of nonempty reverse-well-ordered chains give infima of *all* nonempty
chains, which is `JungNets.HasChainInfima`.

Obtained by instantiating `hasChainSuprema_of_hasWellOrderedSuprema` at `Dᵒᵈ`,
the way Mathlib's `zorn_superset` obtains the dual of `zorn_le₀`. `IsChain.symm`
converts the dual order's chain condition back to the original order's; the rest
of the translation (`Set Dᵒᵈ ≡ Set D`, `IsLUB` at `Dᵒᵈ` ≡ `IsGLB`, and
`DirectedOn (· ≤ ·)` at `Dᵒᵈ` ≡ `DirectedOn (· ≥ ·)`) is definitional. -/
theorem hasChainInfima_of_hasWellOrderedInfima {D : Type u} [Preorder D]
    (hwo : HasWellOrderedInfima D) : JungNets.HasChainInfima D := by
  have hdual : HasWellOrderedSuprema Dᵒᵈ := by
    intro c hne hchain hwoc
    obtain ⟨i, hi⟩ := hwo c hne hchain.symm hwoc
    exact ⟨i, hi⟩
  intro c hne hchain
  obtain ⟨i, hi⟩ := hasChainSuprema_of_hasWellOrderedSuprema hdual c hne hchain.symm
  exact ⟨i, hi⟩

/-- **The order dual of Markowsky's theorem**: infima of nonempty chains give
infima of nonempty filtered sets, i.e. `D` is bicomplete. -/
theorem isBicomplete_of_hasChainInfima {D : Type u} [Preorder D]
    (hci : JungNets.HasChainInfima D) : JungNets.IsBicomplete D := by
  have hdual : HasChainSuprema Dᵒᵈ := by
    intro c hne hchain
    obtain ⟨i, hi⟩ := hci c hne hchain.symm
    exact ⟨i, hi⟩
  intro s hne hfil
  obtain ⟨w, hw⟩ := hasDirectedSuprema_of_hasChainSuprema hdual s hne hfil
  exact ⟨w, hw⟩

/-- The same from the weakest hypothesis. -/
theorem isBicomplete_of_hasWellOrderedInfima {D : Type u} [Preorder D]
    (hwo : HasWellOrderedInfima D) : JungNets.IsBicomplete D :=
  isBicomplete_of_hasChainInfima (hasChainInfima_of_hasWellOrderedInfima hwo)

/-- Chain-completeness and directed-completeness of the dual coincide: the
converse is `JungNets.IsBicomplete.hasChainInfima`, a nonempty chain being
filtered. -/
theorem hasChainInfima_iff_isBicomplete {D : Type u} [Preorder D] :
    JungNets.HasChainInfima D ↔ JungNets.IsBicomplete D :=
  ⟨isBicomplete_of_hasChainInfima, JungNets.IsBicomplete.hasChainInfima⟩

/-- **`Thm137Chains` now implies `Thm137`.** `JungNets` stated the minimal
remaining obligation as infima of nonempty chains, noting that the passage from
chains to filtered sets was Jung's Theorem 1.2 and was unavailable. It is
available now, so the two remainders are the same proposition. -/
theorem thm137_of_thm137Chains {D : Type u} [CompletePartialOrder D]
    (h : JungNets.Thm137Chains D) : JungNets.Thm137 D :=
  fun hAlg => isBicomplete_of_hasChainInfima (h hAlg)

/-- The two forms of Jung's Theorem 1.37 recorded in `JungNets` are equivalent. -/
theorem thm137Chains_iff_thm137 {D : Type u} [CompletePartialOrder D] :
    JungNets.Thm137Chains D ↔ JungNets.Thm137 D :=
  ⟨thm137_of_thm137Chains, JungNets.Thm137.toChains⟩

/-- **The obligation this round is left with, in its weakest form.**

`JungNets.Thm137Chains D` — and hence, by `thm137Chains_iff_thm137`,
`JungNets.Thm137 D` — follows from finding infima for monotone injective nets
indexed by an ordinal alone. A proof of Jung's Theorem 1.37 may therefore assume
a well-ordered index throughout, which is exactly what his retraction argument
onto `A ∪ αᵒᵖ` requires, and need never return to arbitrary chains or filtered
sets. -/
theorem thm137Chains_of_wellOrderedInfima {D : Type u} [CompletePartialOrder D]
    (h : IsAlgebraic (ScottHom D D) → HasWellOrderedInfima D) : JungNets.Thm137Chains D :=
  fun hAlg => hasChainInfima_of_hasWellOrderedInfima (h hAlg)

end ScottDomains.Iwamura
