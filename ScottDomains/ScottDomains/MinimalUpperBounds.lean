import ScottDomains.Bifinite
-- `Set.Finite.exists_le_minimal`: a finite set contains a minimal element below any
-- given member. This is what turns a finite complete set of upper bounds into a
-- complete set of *minimal* upper bounds.
import Mathlib.Order.Preorder.Finite

/-!
# §6.1: minimal upper bounds, the operator `U`, and Plotkin's criterion

Gunter & Scott, *Semantic Domains*, §6.1, quoted from the source PDF:

> Given a poset `A` and a finite set `u ⊆ A`, an upper bound `x` for `u` is
> **minimal** if, for any upper bound `y` for `u`, `y ⊑ x` implies `y = x`. A set
> `v` of minimal upper bounds for `u` is said to be **complete** if, for every
> upper bound `x` for `u`, there is a `y ∈ v` with `y ⊑ x`.

> Now, let `A` be a Plotkin order and suppose `u ⊆ A` is finite. Then there is a
> finite `N ◁ A` with `u ⊆ N`. The set `N` must contain a complete set of minimal
> upper bounds for `u` (why?). This shows the first fact about Plotkin orders:
> every finite subset has a complete set of minimal upper bounds. … But the set
> `N` is finite so we have our second fact: every finite subset must have a finite
> complete set of minimal upper bounds. … However, having finite complete sets of
> minimal upper bounds for finite subsets is not a sufficient condition for
> characterizing the Plotkin orders. To see why, let `A` be a poset which has
> finite complete sets of minimal upper bounds for finite subsets. If `u ⊆ A` is
> finite, let
>
> `U(u) = {x | x is the minimal upper bound for some v ⊆ u}`.
>
> Now, if `u ⊆ N ◁ A`, then `U(u) ⊆ N`. Hence, `Uⁿ(u) ⊆ N` for each `n`. If `N` is
> finite, then there must be an `n` for which `Uⁿ(u) = Uⁿ⁺¹(u)`. This is a third
> fact about Plotkin orders: for each finite `u ⊆ A`, `U^∞(u) = ⋃ₙ Uⁿ(u)` is
> finite.

The paper's three facts are the three configurations of Figure 3: (a) a finite
set with no complete set of minimal upper bounds, (b) one whose complete set of
minimal upper bounds is infinite, (c) one with `U^∞(u)` infinite. This file
supplies the vocabulary and proves that those three facts are not merely
necessary but **jointly sufficient** — `isPlotkinOrder_iff_mubClosure`.

## What is new here

Nothing this file quantifies over existed in the development before it: the
project's r0027 audit measured **0** occurrences of "minimal upper bound",
"complete set of minimal upper bounds", `U`, or `U^∞` anywhere in
`ScottDomains/`. Everything else it uses is already present — `◁` is `IsNormalIn`
from `NormalSubposet.lean`, `IsPlotkinOrder` and `IsBifinite` are from
`Bifinite.lean`, and Mathlib supplies `upperBounds` and `Minimal`.

## Naming

`mub` abbreviates *minimal upper bound* throughout the derived names
(`mubStep`, `mubIter`, `mubClosure`, `IsMubClosed`, `HasCompleteMub`); it is the
literature's abbreviation, and `mubClosure` is the literature's name for
`U^∞`. The set-former itself is spelled out as `minimalUpperBounds`, parallel to
Mathlib's `upperBounds`.

## Relativization

Every notion is relative to a subset `A` of the ambient order, because that is
how §6 uses it: `A` is `K(D)`, and `IsPlotkinOrder` and `◁` are both conditions
on the *basis*, not on `D`. So `upperBoundsIn A u` is `A ∩ upperBounds u`, and
`minimalUpperBounds A u` is the set of `⊑`-minimal members of it. A minimal
upper bound of a set of compact elements need not be compact in `D`; what §6
needs is minimality inside `K(D)`, which is what these definitions give.

## The two directions

* **Plotkin order ⟹ the three facts** (`hasCompleteMub_of_isNormalIn`,
  `minimalUpperBounds_finite_of_isNormalIn`, `mubClosure_subset_of_isNormalIn`).
  The step the paper leaves as "(why?)" is `IsNormalIn.exists_mem_le_of_finite`:
  directedness of `N ∩ ↓x` collapses the finitely many members of `u` to a single
  `z ∈ N` with `u ⊑ z ⊑ x`, so `N ∩ ub(u)` is a finite *complete set of upper
  bounds*, and its minimal elements are exactly the minimal upper bounds.
* **The three facts ⟹ Plotkin order** (`isNormalIn_of_isMubClosed`). This
  direction the paper does not state; it is what makes the criterion an
  equivalence. `U^∞(u)` is closed under minimal upper bounds by construction, and
  a mub-closed, mub-complete set is normal: nonemptiness of `N ∩ ↓x` comes from
  completeness at `v = ∅`, whose minimal upper bounds are the minimal elements of
  `A`, and directedness comes from completeness at `v = {a, b}`.

Note that the first half of the second direction needs no least element: `⊥ ∈ N`
is not assumed but derived, since `upperBoundsIn A ∅ = A`.
-/

namespace ScottDomains

variable {α : Type*}

section Preorder

variable [Preorder α] {A N u v : Set α} {x : α}

/-- The upper bounds of `u` that lie in `A`. §6 always takes upper bounds inside
the basis `K(D)`, never in the ambient cpo. -/
def upperBoundsIn (A u : Set α) : Set α := A ∩ upperBounds u

theorem mem_upperBoundsIn : x ∈ upperBoundsIn A u ↔ x ∈ A ∧ ∀ y ∈ u, y ≤ x := Iff.rfl

theorem upperBoundsIn_subset : upperBoundsIn A u ⊆ A := Set.inter_subset_left

/-- Every member of `A` is an upper bound of `∅`. This is what makes the empty
set the right instance to read nonemptiness of `N ∩ ↓x` off from. -/
@[simp] theorem upperBoundsIn_empty : upperBoundsIn A ∅ = A := by
  simp [upperBoundsIn]

/-- The **minimal upper bounds** of `u` in `A`: the `⊑`-minimal members of
`upperBoundsIn A u`. In a partial order `Minimal` is the paper's condition "for
any upper bound `y` for `u`, `y ⊑ x` implies `y = x`" verbatim; in a preorder it
weakens `=` to `x ⊑ y`, which is the same statement up to the order's own
equivalence. -/
def minimalUpperBounds (A u : Set α) : Set α := {m | Minimal (· ∈ upperBoundsIn A u) m}

theorem minimalUpperBounds_subset : minimalUpperBounds A u ⊆ upperBoundsIn A u :=
  fun _ hm => hm.1

theorem mem_upperBounds_of_mem_minimalUpperBounds (hm : x ∈ minimalUpperBounds A u) :
    x ∈ upperBounds u := hm.1.2

/-- The paper's **complete set of minimal upper bounds**: every upper bound of `u`
in `A` dominates a minimal one. Stated of the whole set `minimalUpperBounds A u`
rather than of an arbitrary subset `v` of it, which is equivalent and removes an
existential — if some `v` of minimal upper bounds is complete, then so is the set
of all of them. -/
def HasCompleteMub (A u : Set α) : Prop :=
  ∀ x ∈ upperBoundsIn A u, ∃ m ∈ minimalUpperBounds A u, m ≤ x

/-- `N` is **closed under minimal upper bounds** taken in `A`: the minimal upper
bounds of any finite subset of `N` are again in `N`. This is the invariant
`U^∞(u)` is built to satisfy. -/
def IsMubClosed (A N : Set α) : Prop :=
  ∀ v : Set α, v ⊆ N → v.Finite → minimalUpperBounds A v ⊆ N

/-- A finite set each of whose members is dominated by a member of a nonempty
directed set `s` is dominated by a *single* member of `s`.

Induction on the finite set: the empty case takes any member of `s`, and the
insertion step feeds the two witnesses — one for the new element, one from the
induction hypothesis — to directedness. This is the paper's "(why?)" step, and it
is stated with the domination hypothesis as an implication so that the induction
does not have to carry a subset hypothesis about the varying set. -/
theorem exists_mem_upperBounds_of_directedOn {s t : Set α} (hd : DirectedOn (· ≤ ·) s)
    (hne : s.Nonempty) (ht : t.Finite) :
    (∀ y ∈ t, ∃ z ∈ s, y ≤ z) → ∃ z ∈ s, ∀ y ∈ t, y ≤ z := by
  induction t, ht using Set.Finite.induction_on with
  | empty =>
    intro _
    obtain ⟨z, hz⟩ := hne
    exact ⟨z, hz, fun y hy => absurd hy (Set.notMem_empty y)⟩
  | @insert a t _ _ ih =>
    intro h
    obtain ⟨z₁, hz₁, hz₁le⟩ := h a (Set.mem_insert a t)
    obtain ⟨z₂, hz₂, hz₂le⟩ := ih fun y hy => h y (Set.mem_insert_of_mem a hy)
    obtain ⟨z, hz, h₁, h₂⟩ := hd z₁ hz₁ z₂ hz₂
    refine ⟨z, hz, ?_⟩
    rintro y (rfl | hy)
    · exact hz₁le.trans h₁
    · exact (hz₂le y hy).trans h₂

/-- **The paper's "(why?)".** If `N ◁ A` and `u ⊆ N` is finite, then every upper
bound `x` of `u` in `A` dominates an upper bound of `u` *inside* `N`.

The whole content is that `N ∩ ↓x` is nonempty and directed, so the finitely many
members of `u` — all of which lie in `N ∩ ↓x` — are collapsed to a single `z`
there. So `N ∩ ub(u)` is a complete set of upper bounds of `u`, and when `N` is
finite it is a *finite* one. -/
theorem IsNormalIn.exists_mem_le_of_finite (hN : N ◁ A) (hu : u.Finite) (huN : u ⊆ N)
    (hx : x ∈ upperBoundsIn A u) : ∃ z ∈ N, z ≤ x ∧ z ∈ upperBounds u := by
  obtain ⟨z, hz, hzub⟩ :=
    exists_mem_upperBounds_of_directedOn (hN.directedOn hx.1) (hN.nonempty hx.1) hu
      fun y hy => ⟨y, ⟨huN hy, hx.2 hy⟩, le_rfl⟩
  exact ⟨z, hz.1, hz.2, fun y hy => hzub y hy⟩

/-- **The three facts are sufficient.** A subset of `A` closed under minimal upper
bounds, each of whose finite subsets has a complete set of them, is normal in `A`.

* nonempty — apply completeness to `v = ∅`, whose upper bounds in `A` are all of
  `A`; the minimal upper bound it produces below `x` lies in `N` by closedness.
  No least element is needed, and none is assumed.
* directed — apply completeness to `v = {a, b}` for `a, b ∈ N ∩ ↓x`, which `x`
  bounds; the minimal upper bound it produces is in `N`, is `⊑ x`, and is above
  both.

This direction is not in the paper, which states only the three necessary
conditions. It is what makes `isPlotkinOrder_iff_mubClosure` an equivalence. -/
theorem isNormalIn_of_isMubClosed (hNA : N ⊆ A) (hcl : IsMubClosed A N)
    (hcomp : ∀ v : Set α, v ⊆ N → v.Finite → HasCompleteMub A v) : N ◁ A := by
  refine ⟨hNA, fun x hx => ⟨?_, ?_⟩⟩
  · obtain ⟨m, hm, hmx⟩ :=
      hcomp ∅ (Set.empty_subset N) Set.finite_empty x (by simpa using hx)
    exact ⟨m, hcl ∅ (Set.empty_subset N) Set.finite_empty hm, hmx⟩
  · rintro a ⟨haN, hax⟩ b ⟨hbN, hbx⟩
    have hsub : ({a, b} : Set α) ⊆ N := by
      rintro y (rfl | rfl) <;> assumption
    have hxub : x ∈ upperBoundsIn A ({a, b} : Set α) := by
      refine ⟨hx, ?_⟩
      rintro y (rfl | rfl) <;> assumption
    obtain ⟨m, hm, hmx⟩ := hcomp _ hsub (Set.toFinite _) x hxub
    have hmub := mem_upperBounds_of_mem_minimalUpperBounds hm
    exact ⟨m, ⟨hcl _ hsub (Set.toFinite _) hm, hmx⟩,
      hmub (Set.mem_insert a _), hmub (Set.mem_insert_of_mem a rfl)⟩

/-! ### The operator `U` and its iterate `U^∞` -/

/-- One application of the paper's `U`: the minimal upper bounds of the finite
subsets of `N`, together with `N` itself.

The paper writes `U(u) = {x | x is the minimal upper bound for some v ⊆ u}` for
finite `u`, where `u ⊆ U(u)` holds automatically because each `a ∈ u` is the
unique minimal upper bound of `{a}`. Here `N` may be infinite, so the subsets `v`
are required to be finite, and `N` is adjoined explicitly so that monotonicity
holds without assuming `N ⊆ A`. `mubStep_eq_of_subset` shows the two agree when
`N ⊆ A`. -/
def mubStep (A N : Set α) : Set α :=
  N ∪ {m | ∃ v : Set α, v ⊆ N ∧ v.Finite ∧ m ∈ minimalUpperBounds A v}

theorem subset_mubStep : N ⊆ mubStep A N := Set.subset_union_left

theorem mubStep_mono (h : N ⊆ u) : mubStep A N ⊆ mubStep A u := by
  rintro m (hm | ⟨v, hvN, hvfin, hmv⟩)
  · exact Or.inl (h hm)
  · exact Or.inr ⟨v, hvN.trans h, hvfin, hmv⟩

/-- `Uⁿ(u)`. -/
def mubIter (A u : Set α) : ℕ → Set α
  | 0 => u
  | n + 1 => mubStep A (mubIter A u n)

/-- `U^∞(u) = ⋃ₙ Uⁿ(u)`, the **mub-closure** of `u` in `A`. -/
def mubClosure (A u : Set α) : Set α := ⋃ n, mubIter A u n

theorem mubIter_subset_succ (A u : Set α) (n : ℕ) :
    mubIter A u n ⊆ mubIter A u (n + 1) := subset_mubStep

theorem mubIter_mono (A u : Set α) : Monotone (mubIter A u) :=
  monotone_nat_of_le_succ (mubIter_subset_succ A u)

theorem mubIter_subset_mubClosure (A u : Set α) (n : ℕ) :
    mubIter A u n ⊆ mubClosure A u := Set.subset_iUnion _ n

theorem subset_mubClosure : u ⊆ mubClosure A u := mubIter_subset_mubClosure A u 0

/-- Every finite subset of `U^∞(u)` already lies in some finite stage `Uⁿ(u)`.
The stages form a chain, so the finitely many indices witnessing membership have
a maximum. -/
theorem exists_mubIter_of_finite_subset (hv : v.Finite) :
    v ⊆ mubClosure A u → ∃ n, v ⊆ mubIter A u n := by
  induction v, hv using Set.Finite.induction_on with
  | empty => exact fun _ => ⟨0, Set.empty_subset _⟩
  | @insert a v _ _ ih =>
    intro h
    obtain ⟨n₁, hn₁⟩ := Set.mem_iUnion.mp (h (Set.mem_insert a v))
    obtain ⟨n₂, hn₂⟩ := ih fun y hy => h (Set.mem_insert_of_mem a hy)
    refine ⟨max n₁ n₂, ?_⟩
    rintro y (rfl | hy)
    · exact mubIter_mono A u (le_max_left n₁ n₂) hn₁
    · exact mubIter_mono A u (le_max_right n₁ n₂) (hn₂ hy)

/-- `U^∞(u)` is closed under minimal upper bounds: a finite subset lands in some
stage `Uⁿ(u)`, and its minimal upper bounds land in `Uⁿ⁺¹(u)`. -/
theorem isMubClosed_mubClosure (A u : Set α) : IsMubClosed A (mubClosure A u) := by
  intro v hv hvfin m hm
  obtain ⟨n, hn⟩ := exists_mubIter_of_finite_subset hvfin hv
  exact mubIter_subset_mubClosure A u (n + 1) (Or.inr ⟨v, hn, hvfin, hm⟩)

theorem mubStep_subset (hNA : N ⊆ A) : mubStep A N ⊆ A := by
  rintro m (hm | ⟨v, _, _, hmv⟩)
  · exact hNA hm
  · exact upperBoundsIn_subset (minimalUpperBounds_subset hmv)

theorem mubIter_subset (hu : u ⊆ A) : ∀ n, mubIter A u n ⊆ A
  | 0 => hu
  | n + 1 => mubStep_subset (mubIter_subset hu n)

theorem mubClosure_subset (hu : u ⊆ A) : mubClosure A u ⊆ A :=
  Set.iUnion_subset fun n => mubIter_subset hu n

end Preorder

section PartialOrder

variable [PartialOrder α] {A N u v : Set α} {x : α}

/-- A member of `A` is its own unique minimal upper bound. This is why the paper
can write `U(u)` without adjoining `u`, and it identifies `mubStep` with the
paper's `U` (`mubStep_eq_of_subset`). -/
theorem mem_minimalUpperBounds_singleton (hx : x ∈ A) :
    x ∈ minimalUpperBounds A ({x} : Set α) :=
  ⟨⟨hx, fun _ hy => le_of_eq hy⟩, fun _ hy _ => hy.2 rfl⟩

/-- `mubStep` is the paper's `U` on the nose once `N ⊆ A`: the union with `N` is
redundant, because each `a ∈ N` is the unique minimal upper bound of `{a}`. -/
theorem mubStep_eq_of_subset (hNA : N ⊆ A) :
    mubStep A N = {m | ∃ v : Set α, v ⊆ N ∧ v.Finite ∧ m ∈ minimalUpperBounds A v} := by
  refine Set.Subset.antisymm ?_ Set.subset_union_right
  rintro m (hm | hm)
  · exact ⟨{m}, Set.singleton_subset_iff.mpr hm, Set.finite_singleton m,
      mem_minimalUpperBounds_singleton (hNA hm)⟩
  · exact hm

/-! ### Plotkin order ⟹ the three facts -/

/-- **Fact 1, and the sharper form of fact 2.** The minimal upper bounds of a
finite `u ⊆ N` with `N ◁ A` all lie in `N`.

Given a minimal upper bound `m`, the paper's "(why?)" step produces `z ∈ N` with
`u ⊑ z ⊑ m`; minimality of `m` forces `m ⊑ z`, so `m = z ∈ N` by antisymmetry. -/
theorem minimalUpperBounds_subset_of_isNormalIn (hN : N ◁ A) (hu : u.Finite) (huN : u ⊆ N) :
    minimalUpperBounds A u ⊆ N := by
  rintro m ⟨hmub, hmin⟩
  obtain ⟨z, hzN, hzm, hzub⟩ := hN.exists_mem_le_of_finite hu huN hmub
  exact le_antisymm hzm (hmin ⟨hN.subset hzN, hzub⟩ hzm) ▸ hzN

/-- **Fact 2.** In a *finite* normal subposet the minimal upper bounds of a finite
subset are finite in number. -/
theorem minimalUpperBounds_finite_of_isNormalIn (hfin : N.Finite) (hN : N ◁ A)
    (hu : u.Finite) (huN : u ⊆ N) : (minimalUpperBounds A u).Finite :=
  hfin.subset (minimalUpperBounds_subset_of_isNormalIn hN hu huN)

/-- **Fact 1, completeness.** With `N` finite and normal in `A`, every finite
`u ⊆ N` has a complete set of minimal upper bounds.

The set `S = {y ∈ N | y ∈ ub(u), y ⊑ x}` is finite and, by the "(why?)" step,
nonempty. Take `m` minimal in `S` below a member of `S`. Then `m` is minimal in
the *whole* of `upperBoundsIn A u`: any upper bound `y ⊑ m` is itself `⊑ x`, so
the "(why?)" step puts some `z ∈ S` below `y`, and minimality of `m` in `S` gives
`m ⊑ z ⊑ y`. Minimality within a finite complete set of upper bounds upgrades to
minimality outright — that is the whole trick. -/
theorem hasCompleteMub_of_isNormalIn (hfin : N.Finite) (hN : N ◁ A)
    (hu : u.Finite) (huN : u ⊆ N) : HasCompleteMub A u := by
  intro x hx
  obtain ⟨z, hzN, hzx, hzub⟩ := hN.exists_mem_le_of_finite hu huN hx
  set S : Set α := {y | y ∈ N ∧ y ∈ upperBounds u ∧ y ≤ x} with hSdef
  have hSfin : S.Finite := hfin.subset fun _ hy => hy.1
  obtain ⟨m, _, hmS, hmmin⟩ := hSfin.exists_le_minimal (a := z) ⟨hzN, hzub, hzx⟩
  refine ⟨m, ⟨⟨hN.subset hmS.1, hmS.2.1⟩, ?_⟩, hmS.2.2⟩
  intro y hy hym
  obtain ⟨z', hz'N, hz'y, hz'ub⟩ :=
    hN.exists_mem_le_of_finite hu huN (x := y) ⟨hy.1, hy.2⟩
  exact (hmmin ⟨hz'N, hz'ub, hz'y.trans (hym.trans hmS.2.2)⟩ (hz'y.trans hym)).trans hz'y

/-- **Fact 3.** `U^∞(u) ⊆ N` whenever `u ⊆ N ◁ A` — the paper's "if `u ⊆ N ◁ A`,
then `U(u) ⊆ N`. Hence, `Uⁿ(u) ⊆ N` for each `n`." Induction on `n`, the step
being `minimalUpperBounds_subset_of_isNormalIn`. -/
theorem mubClosure_subset_of_isNormalIn (hN : N ◁ A) (huN : u ⊆ N) :
    mubClosure A u ⊆ N := by
  refine Set.iUnion_subset fun n => ?_
  induction n with
  | zero => exact huN
  | succ n ih =>
    rintro m (hm | ⟨v, hvn, hvfin, hmv⟩)
    · exact ih hm
    · exact minimalUpperBounds_subset_of_isNormalIn hN hvfin (hvn.trans ih) hmv

/-! ### Plotkin's criterion -/

/-- **Plotkin's criterion.** `A` is a Plotkin order exactly when every finite
subset has a complete set of minimal upper bounds and a finite mub-closure.

Left to right is the paper's three facts: the normal witness `N` for `u` bounds
`U^∞(u)`, and it makes every finite subset of itself mub-complete. Right to left
is `isNormalIn_of_isMubClosed` applied to `N = U^∞(u)`, which is mub-closed by
construction and mub-complete because it is a subset of `A`.

The three configurations of Figure 3 are exactly the three ways the right-hand
side fails: (a) completeness fails, (b) `minimalUpperBounds A v` is infinite —
which by `minimalUpperBounds_subset` forces `mubClosure A v` infinite — and (c)
the closure is infinite though every single stage is finite. -/
theorem isPlotkinOrder_iff_mubClosure (A : Set α) :
    IsPlotkinOrder A ↔
      (∀ v : Set α, v.Finite → v ⊆ A → HasCompleteMub A v) ∧
        (∀ u : Set α, u.Finite → u ⊆ A → (mubClosure A u).Finite) := by
  constructor
  · intro h
    refine ⟨fun v hv hvA => ?_, fun u hu huA => ?_⟩
    · obtain ⟨N, hNfin, hN, hvN⟩ := h v hv hvA
      exact hasCompleteMub_of_isNormalIn hNfin hN hv hvN
    · obtain ⟨N, hNfin, hN, huN⟩ := h u hu huA
      exact hNfin.subset (mubClosure_subset_of_isNormalIn hN huN)
  · rintro ⟨hcomp, hfin⟩ u hu huA
    refine ⟨mubClosure A u, hfin u hu huA, ?_, subset_mubClosure⟩
    refine isNormalIn_of_isMubClosed (mubClosure_subset huA) (isMubClosed_mubClosure A u) ?_
    exact fun v hv hvfin => hcomp v hvfin (hv.trans (mubClosure_subset huA))

/-- The same criterion in the form the witness sets make available: a Plotkin
order is one in which every finite subset sits inside a finite, mub-closed,
mub-complete subset of `A`. This is the shape `isNormalIn_of_isMubClosed` and
`minimalUpperBounds_subset_of_isNormalIn` pair up into, and it is the statement
§6.2's later results consume. -/
theorem isPlotkinOrder_iff (A : Set α) :
    IsPlotkinOrder A ↔ ∀ u : Set α, u.Finite → u ⊆ A →
      ∃ N : Set α, N.Finite ∧ N ⊆ A ∧ u ⊆ N ∧ IsMubClosed A N ∧
        ∀ v : Set α, v ⊆ N → v.Finite → HasCompleteMub A v := by
  constructor
  · intro h u hu huA
    obtain ⟨N, hNfin, hN, huN⟩ := h u hu huA
    exact ⟨N, hNfin, hN.subset, huN,
      fun v hv hvfin => minimalUpperBounds_subset_of_isNormalIn hN hvfin hv,
      fun v hv hvfin => hasCompleteMub_of_isNormalIn hNfin hN hvfin hv⟩
  · intro h u hu huA
    obtain ⟨N, hNfin, hNA, huN, hcl, hcomp⟩ := h u hu huA
    exact ⟨N, hNfin, isNormalIn_of_isMubClosed hNA hcl hcomp, huN⟩

/-- **The Figure 3 dichotomy.** A poset that is not a Plotkin order exhibits one
of two defects: some finite subset has no complete set of minimal upper bounds
(Figure 3a), or some finite subset has an infinite mub-closure (Figures 3b and
3c). Figure 3b is the special case in which a single application of `U` is
already infinite; 3c is the case in which every application is finite but the
iteration does not stabilize.

This is the case split Smyth's proof of Theorem 18 runs, so it is stated here
rather than left implicit in the equivalence. -/
theorem exists_of_not_isPlotkinOrder {A : Set α} (h : ¬ IsPlotkinOrder A) :
    (∃ v : Set α, v.Finite ∧ v ⊆ A ∧ ¬ HasCompleteMub A v) ∨
      (∃ u : Set α, u.Finite ∧ u ⊆ A ∧ (mubClosure A u).Infinite) := by
  by_contra hcon
  refine h ((isPlotkinOrder_iff_mubClosure A).mpr ⟨fun v hv hvA => ?_, fun u hu huA => ?_⟩)
  · by_contra hn
    exact hcon (Or.inl ⟨v, hv, hvA, hn⟩)
  · by_contra hn
    exact hcon (Or.inr ⟨u, hu, huA, hn⟩)

/-- **Figure 3b, stated positively.** In a Plotkin order every finite subset has
only finitely many minimal upper bounds. Immediate from
`isPlotkinOrder_iff_mubClosure`, since `minimalUpperBounds A u ⊆ mubClosure A u`
whenever `u ⊆ A`. -/
theorem IsPlotkinOrder.minimalUpperBounds_finite {A : Set α} (h : IsPlotkinOrder A)
    (hu : u.Finite) (huA : u ⊆ A) : (minimalUpperBounds A u).Finite := by
  obtain ⟨N, hNfin, hN, huN⟩ := h u hu huA
  exact minimalUpperBounds_finite_of_isNormalIn hNfin hN hu huN

end PartialOrder

/-! ## Contact with §6: bifiniteness

`IsBifinite α` is `IsPlotkinOrder (compacts α)`, so the criterion transfers to
domains verbatim. This is the form Theorem 18 must produce and the form
Theorem 16 and Lemma 20 consume. -/

section Bifinite

variable [CompletePartialOrder α]

/-- Plotkin's criterion for a domain: `D` is bifinite exactly when every finite
set of compact elements has a complete set of minimal upper bounds in `K(D)` and
a finite mub-closure there. -/
theorem isBifinite_iff_mubClosure :
    IsBifinite α ↔
      (∀ v : Set α, v.Finite → v ⊆ compacts α → HasCompleteMub (compacts α) v) ∧
        (∀ u : Set α, u.Finite → u ⊆ compacts α → (mubClosure (compacts α) u).Finite) :=
  isPlotkinOrder_iff_mubClosure (compacts α)

end Bifinite

end ScottDomains
