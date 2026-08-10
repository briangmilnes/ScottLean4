import ScottDomains.Bifinite
import ScottDomains.IdealCompletion
import ScottDomains.MinimalUpperBounds
-- `Set.Finite.prod`, for the `|N| · 2^|N|` bound on `M(N)`; not reachable from
-- the ScottDomains imports above.
import Mathlib.Data.Finite.Prod

/-!
# §7.4: `M(A)`, `D⁺`, and Theorem 29

Gunter & Scott, *Semantic Domains*, §7.4, quoted from the source PDF
(`papers/Gunter Scott 1990.pdf`):

> The convex powerdomain `()♮` cannot be representable over `U` because it does
> not preserve bounded completeness. We construct a domain over which this
> operator can be represented as follows. Given a poset `A`, define `M(A)` to be
> the [set] of pairs `(x, u) ∈ A × Pf(A)` such that `x ⊑ z` for every `z ∈ u`.
> Define a pre-ordering on `M(A)` by setting `(x, u) ⊢ (y, v)` if and only if
> there is a `z ∈ u` such that `z ⊑ y`. Now, given a domain `D`, we define `D⁺`
> to be the domain of ideals over `⟨M(A), ⊢⟩`.

> **Theorem 29** If `D` is bifinite, then so is `D⁺`. Moreover, if `D ≅ D⁺` and
> `E` is any bifinite domain, then there is a projection `p : D → E`.

> A full proof of the theorem may be found in [Gun87]. We will attempt to offer
> some hint about how the desired fixed point is obtained. At the first step we
> take the domain `I = {⊥}` containing only the single point `⊥`. At the second
> step, `I⁺`, there are elements `a = (⊥, {⊥})` and `b = (⊥, ∅)` with `b ⊢ a`.
> At the third step there are five elements
> `(a, {a}), (a, {b}), (b, {b}), (b, ∅), (a, ∅)`
> which form the partially ordered set `I⁺⁺` pictured in Figure 4. Note that
> there is another element `(a, {a, b}) ∈ M(I⁺)` but this satisfies
> `(a, {a}) ⊢ (a, {a, b})` and `(a, {a, b}) ⊢ (a, {a})` so we have identified
> these elements in the picture. The next step `I⁺⁺⁺` has 20 elements (up to
> equivalence in the sense just mentioned) … It should be noted that each stage
> of the construction is embedded in the next one by the map `x ↦ (x, {x})`.

## What [Gun87] leaves deferred

[Gun87] is `C. A. Gunter. Sets and the semantics of bounded nondeterminism.
Manuscript, 1987` — unpublished, absent from Gunter's own publication list, and
not obtainable. §7.4 contains **no proof of Theorem 29**: it states the theorem,
cites that manuscript for the full proof, and offers in its place the
illustrative chain `I, I⁺, I⁺⁺, I⁺⁺⁺` above. Every step below is therefore
reconstructed, not transcribed.

The construction itself is *not* lost with the manuscript. Gunter, *Universal
Profinite Domains*, Information and Computation **72** (1987) 1–30, p. 23
(`papers/Gunter 1987 Universal Profinite Domains.pdf`) gives it, attributing it
to Scott:

> There is an even more explicit way of describing this operation which was
> remarked to the author by Dana Scott. Given a finite poset `A`, let `A⁺` be the
> set of pairs `⟨X, u⟩` such that `X ∈ A` and `u` is an **upwards closed** set of
> points from `A` such that `X ⊑ Y` for each `Y ∈ u`. Say that
> `⟨X, u⟩ ⊑ ⟨Y, v⟩` iff `Y ∈ u`. This more order-theoretic way of doing things
> helps in picturing the universal domain as the limit of the posets
> `A ⊴ A⁺ ⊴ A⁺⁺ ⊴ ⋯`.

Reading the two together fixes §7.4 exactly. `Pf(A)` is a *finite generating
set* for Gunter's upward-closed `u`, and the printed relation `∃ z ∈ u, z ⊑ y`
is Gunter's `Y ∈ u` transported along `u ↦ ↑u`. One thing is lost in transit,
and one is misprinted.

**Defect 1: the printed relation drops its reflexive part.**
`MPair.PaperLE` is the printed relation verbatim. Reflexivity at `(x, u)` demands
`∃ z ∈ u, z ⊑ x`, while membership in `M(A)` demands `x ⊑ z` for every `z ∈ u`;
together these force `x ∈ u`. The paper's own second-step element `b = (⊥, ∅)`
therefore fails `b ⊢ b` (`paperLE_irrefl_pointB`), and so does `(false, {true})`
over `Bool`, where the cover is non-empty (`paperLE_irrefl_boolPair`). Gunter's
form has the same gap — `⟨X, ∅⟩ ⊑ ⟨X, ∅⟩` would need `X ∈ ∅` — so in both the
relation printed is the *strict* part and the order is its reflexive closure. On
finite generating sets the reflexive part is exactly the identification the paper
performs by hand: `(x, u)` and `(x, v)` are the same element when `↑u = ↑v`.
`instPreorder` is the printed relation with that disjunct restored, and
`MPair.le_iff` says so.

**Defect 2: the worked example reverses its own definition.** The text asserts
`b ⊢ a`. The printed definition yields `a ⊢ b` and refutes `b ⊢ a`
(`paperLE_pointA_pointB`, `not_paperLE_pointB_pointA`), as does Gunter's, and the
rest of the example needs `a ⊑ b`: `(a, {b})` and `(a, {a, b})` are members of
`M(I⁺)` only if `a ⊑ b`.

## Why this repair and not the other one

A second repair is available — compare bases in `A` and covers in the Smyth
(upper) pre-order, `(x,u) ⊑ (y,v)` iff `x ⊑ y` and every `z ∈ v` is above some
`z' ∈ u` — and it is a pre-order containing the printed relation too. The
paper's own element counts discriminate the two. Enumerating `I, I⁺, I⁺⁺, I⁺⁺⁺`
under each (`scripts/mpair-stages.py`) gives

| # | reading | sizes |
| - | ------- | ----- |
| 1 | §7.4's stated counts | 1, 2, 5, **20** |
| 2 | printed relation + reflexive part (this file) | 1, 2, 5, **20** |
| 3 | Smyth order on covers | 1, 2, 5, **21** |

so the Smyth reading is refuted by the paper at the third step, and the reading
formalized here is the one Gunter and Scott intend. The two agree at stages 0–2;
they first differ on whether `(a, ∅) ⊑ (b, ∅)`, which the Smyth reading asserts
and this one denies.

## What is proved of Theorem 29, and what is not

`thm29` is the first sentence — `D` bifinite implies `D⁺` bifinite. It is a
Plotkin-order argument on the basis, transported twice:

1. `isPlotkinOrder_univ_subtype` — `K(D)` a Plotkin order as a subset of `D`
   gives `K(D)` a Plotkin order as a poset in its own right.
2. `isPlotkinOrder_MPair` — the content. Given a finite `S ⊆ M(A)`, take a finite
   `N ◁ A` containing every base and every cover element of `S`; then `M(N)` is
   finite, contains `S`, and is normal in `M(A)` (`MSub_isNormalIn`).
   Directedness is where the order is spent, and the repaired order makes it
   short: two members below `(y, v)` supply `z₁, z₂ ∈ N` below `y`, one
   application of `N ◁ A` at `y` joins them to `x₃ ∈ N`, and `(x₃, {x₃})` — a
   point of the *embedded copy* of `N` — is above both and below `(y, v)`.
3. `isPlotkinOrder_image` — a monotone order-reflecting map carries a Plotkin
   order to one, applied to `principal : M(K(D)) → D⁺`, whose range is `K(D⁺)`.

The second sentence — if `D ≅ D⁺` and `E` is bifinite then there is a projection
`p : D → E` — is **not** proved here, and neither is the fixed point `V` of
`D ↦ D⁺`. Both are what [Gun87] carries and §7.4 does not: the universality
argument, and the ω-colimit of `I ⊴ I⁺ ⊴ I⁺⁺ ⊴ ⋯` along the embeddings `eta`.
No `sorry` stands in for either.
-/

namespace ScottDomains.BifiniteUniversal

open ScottDomains

universe u v

/-! ## `M(A)` -/

section Basic

variable {A : Type u} [PartialOrder A]

/-- `M(A)`: pairs `(x, u)` with `u` a finite set of elements of `A` and `x` a
lower bound of `u`. The cover is a `Finset` — the paper's `Pf(A)`, whose own
§7.4 example uses `(⊥, ∅)`, so the empty cover is admitted — and it is a
generating set for Gunter 1987's upward-closed `u`, recovered as
`MPair.upper`. -/
@[ext] structure MPair (A : Type u) [PartialOrder A] where
  /-- The paper's `x`. -/
  base : A
  /-- The paper's `u`, a finite generating set. -/
  cover : Finset A
  /-- The paper's "`x ⊑ z` for every `z ∈ u`". -/
  base_le : ∀ z ∈ cover, base ≤ z

/-- `↑u`: Gunter 1987's upward-closed second component, generated by the paper's
finite `u`. Two pairs with the same base and the same `upper` are the elements
§7.4 identifies. -/
def MPair.upper (m : MPair A) : Set A := {y | ∃ z ∈ m.cover, z ≤ y}

theorem MPair.mem_upper {m : MPair A} {y : A} : y ∈ m.upper ↔ ∃ z ∈ m.cover, z ≤ y := Iff.rfl

/-- The pre-ordering **as printed** in §7.4: `(x, u) ⊢ (y, v)` iff `∃ z ∈ u` with
`z ⊑ y`, which is Gunter 1987's `y ∈ ↑u`. It is the strict part of the order,
not the order: see the module docstring. -/
def MPair.PaperLE (m n : MPair A) : Prop := n.base ∈ m.upper

/-- The order: the printed relation together with the reflexive part §7.4
supplies by hand ("we have identified these elements"). -/
instance instPreorder : Preorder (MPair A) where
  le m n := m.PaperLE n ∨ (m.base = n.base ∧ m.upper = n.upper)
  le_refl _ := Or.inr ⟨rfl, rfl⟩
  le_trans m n p h₁ h₂ := by
    rcases h₁ with ⟨z, hz, hzn⟩ | ⟨hb₁, hu₁⟩
    · rcases h₂ with ⟨z', hz', hz'p⟩ | ⟨hb₂, _⟩
      · exact Or.inl ⟨z, hz, hzn.trans ((n.base_le z' hz').trans hz'p)⟩
      · exact Or.inl ⟨z, hz, hb₂ ▸ hzn⟩
    · rcases h₂ with h | ⟨hb₂, hu₂⟩
      · refine Or.inl ?_
        show p.base ∈ m.upper
        rw [hu₁]
        exact h
      · exact Or.inr ⟨hb₁.trans hb₂, hu₁.trans hu₂⟩

theorem MPair.le_iff {m n : MPair A} :
    m ≤ n ↔ m.PaperLE n ∨ (m.base = n.base ∧ m.upper = n.upper) := Iff.rfl

/-- **The order contains the printed relation**: no instance of `⊢` is lost. -/
theorem MPair.le_of_paperLE {m n : MPair A} (h : m.PaperLE n) : m ≤ n := Or.inl h

/-- **§7.4's identification.** Two pairs with the same base and the same
generated up-set are equivalent — the step the paper takes when it writes
"`(a, {a}) ⊢ (a, {a, b})` and `(a, {a, b}) ⊢ (a, {a})` so we have identified
these elements". -/
theorem MPair.equiv_of_upper_eq {m n : MPair A} (hb : m.base = n.base)
    (hu : m.upper = n.upper) : m ≤ n ∧ n ≤ m :=
  ⟨Or.inr ⟨hb, hu⟩, Or.inr ⟨hb.symm, hu.symm⟩⟩

/-- The paper's embedding of each stage in the next, `x ↦ (x, {x})`. -/
def eta (x : A) : MPair A :=
  ⟨x, {x}, fun _z hz => le_of_eq (Finset.mem_singleton.mp hz).symm⟩

@[simp] theorem eta_base (x : A) : (eta x).base = x := rfl
@[simp] theorem eta_cover (x : A) : (eta x).cover = {x} := rfl

theorem mem_upper_eta {x y : A} : y ∈ (eta x).upper ↔ x ≤ y := by
  constructor
  · rintro ⟨z, hz, hzy⟩
    rw [Finset.mem_singleton.mp hz] at hzy
    exact hzy
  · exact fun h => ⟨x, Finset.mem_singleton_self x, h⟩

/-- `x ↦ (x, {x})` is an order embedding: the paper's "each stage of the
construction is embedded in the next one". -/
theorem eta_le_eta_iff {x y : A} : eta x ≤ eta y ↔ x ≤ y := by
  refine ⟨fun h => ?_, fun h => Or.inl (mem_upper_eta.mpr h)⟩
  rcases h with h | ⟨hb, _⟩
  · exact mem_upper_eta.mp h
  · exact le_of_eq hb

/-- `(⊥, {⊥})` — the paper's `a` at the second step — is the least element. -/
instance instOrderBot [OrderBot A] : OrderBot (MPair A) where
  bot := eta ⊥
  bot_le _ := Or.inl (mem_upper_eta.mpr bot_le)

@[simp] theorem bot_eq_eta_bot [OrderBot A] : (⊥ : MPair A) = eta ⊥ := rfl

instance instCountable [Countable A] : Countable (MPair A) :=
  Function.Injective.countable (f := fun m : MPair A => (m.base, m.cover))
    (by
      intro m n h
      exact MPair.ext (congrArg Prod.fst h) (congrArg Prod.snd h))

end Basic

/-! ## The two defects, kernel-checked

`PUnit` is the paper's `I = {⊥}`, so `MPair PUnit` is its `I⁺` and the two
elements below are its `a` and `b`. -/

section Defects

/-- The paper's `a = (⊥, {⊥})`. -/
def pointA : MPair PUnit := eta PUnit.unit

/-- The paper's `b = (⊥, ∅)`. -/
def pointB : MPair PUnit := ⟨PUnit.unit, ∅, by simp⟩

/-- **Defect 1.** The printed relation is not reflexive at the paper's own
element `b = (⊥, ∅)`: `∃ z ∈ ∅` is false. -/
theorem paperLE_irrefl_pointB : ¬ pointB.PaperLE pointB := by
  simp [MPair.PaperLE, MPair.upper, pointB]

/-- Defect 1 does not depend on the empty cover. Over `Bool` the pair
`(false, {true})` lies in `M(Bool)` and fails the printed relation at itself,
because reflexivity would need `true ⊑ false`. -/
def boolPair : MPair Bool := ⟨false, {true}, by simp⟩

theorem paperLE_irrefl_boolPair : ¬ boolPair.PaperLE boolPair := by
  simp [MPair.PaperLE, MPair.upper, boolPair]

/-- Hence the printed relation is not a pre-ordering: reflexivity fails. -/
theorem not_reflexive_paperLE : ¬ ∀ m : MPair PUnit, m.PaperLE m :=
  fun h => paperLE_irrefl_pointB (h pointB)

/-- **Defect 2.** The printed definition yields `a ⊢ b` … -/
theorem paperLE_pointA_pointB : pointA.PaperLE pointB :=
  mem_upper_eta.mpr le_rfl

/-- … and refutes the `b ⊢ a` the text asserts. -/
theorem not_paperLE_pointB_pointA : ¬ pointB.PaperLE pointA := by
  simp [MPair.PaperLE, MPair.upper, pointB]

/-- Under the repaired order the second step is the paper's picture with the
direction the element list requires: `a ≤ b` and not conversely. -/
theorem pointA_le_pointB : pointA ≤ pointB :=
  MPair.le_of_paperLE paperLE_pointA_pointB

theorem not_pointB_le_pointA : ¬ pointB ≤ pointA := by
  intro h
  rcases h with h | ⟨_, hu⟩
  · exact not_paperLE_pointB_pointA h
  · have hmem : PUnit.unit ∈ pointA.upper := mem_upper_eta.mpr le_rfl
    rw [← hu] at hmem
    exact absurd hmem (by simp [MPair.upper, pointB])

/-- `I⁺` has exactly the paper's two elements: a `Finset PUnit` is `∅` or
`{unit}`, so `M(I)` is `{a, b}`. -/
theorem mpair_punit_eq (m : MPair PUnit) : m = pointA ∨ m = pointB := by
  rcases Finset.eq_empty_or_nonempty m.cover with h | ⟨z, hz⟩
  · exact Or.inr (MPair.ext (Subsingleton.elim _ _) (by simpa [pointB] using h))
  · refine Or.inl (MPair.ext (Subsingleton.elim _ _) ?_)
    refine Finset.eq_singleton_iff_unique_mem.mpr ⟨?_, fun w _ => Subsingleton.elim _ _⟩
    simpa [Subsingleton.elim z PUnit.unit] using hz

end Defects

/-! ## `M(N) ◁ M(A)`, and `M` preserves Plotkin orders -/

section Plotkin

variable {A : Type u} [PartialOrder A] [OrderBot A]

/-- `M(N)` sitting inside `M(A)`: the pairs whose base and whose cover lie in
`N`. -/
def MSub (N : Set A) : Set (MPair A) := {m : MPair A | m.base ∈ N ∧ ↑m.cover ⊆ N}

omit [OrderBot A] in
/-- `M(N)` is finite when `N` is: it injects into `N × 𝒫(N)`. Cost is
`|N| · 2^|N|` pairs, the size of the finite normal subposet Theorem 29's proof
carries at each step. -/
theorem MSub_finite {N : Set A} (hN : N.Finite) : (MSub N).Finite := by
  classical
  have hpow : {s : Finset A | ↑s ⊆ N}.Finite := by
    refine Set.Finite.subset (Finset.finite_toSet hN.toFinset.powerset) ?_
    intro s hs
    rw [Finset.mem_coe, Finset.mem_powerset]
    intro x hx
    exact hN.mem_toFinset.mpr (hs (Finset.mem_coe.mpr hx))
  refine Set.Finite.of_finite_image (f := fun m : MPair A => (m.base, m.cover)) ?_ ?_
  · refine Set.Finite.subset (Set.Finite.prod hN hpow) ?_
    rintro _ ⟨m, hm, rfl⟩
    exact ⟨hm.1, hm.2⟩
  · intro m _ n _ h
    exact MPair.ext (congrArg Prod.fst h) (congrArg Prod.snd h)

/-- **`M(N) ◁ M(A)` whenever `N ◁ A`.** This is the step Theorem 29's first
sentence turns on.

*Nonempty*: `(⊥, {⊥})` lies in `M(N)` — `⊥ ∈ N` by Lemma 4.3 — and below
everything.

*Directed*: let `m₁, m₂ ∈ M(N)` be below `n`. If either is below `n` by the
reflexive disjunct then it is *equivalent* to `n` and the other is below it, so
it serves as the join. Otherwise each is below `n` by the printed relation,
supplying `z₁ ∈ m₁.cover` and `z₂ ∈ m₂.cover` with `zᵢ ⊑ n.base`; both lie in
`N`, so directedness of `N ∩ ↓n.base` joins them to a single `x₃ ∈ N` with
`x₃ ⊑ n.base`. Then `(x₃, {x₃}) = eta x₃` — a point of the copy of `N` embedded
by the paper's `x ↦ (x, {x})` — is in `M(N)`, is above `m₁` and `m₂`, and is
below `n`. The join never needs a cover richer than a singleton. -/
theorem MSub_isNormalIn {N : Set A} (hN : N ◁ (Set.univ : Set A)) :
    MSub N ◁ (Set.univ : Set (MPair A)) := by
  refine ⟨Set.subset_univ _, fun n _ => ⟨?_, ?_⟩⟩
  · refine ⟨⊥, ⟨⟨?_, ?_⟩, Set.mem_Iic.mpr bot_le⟩⟩
    · exact hN.bot_mem (Set.mem_univ _)
    · intro x hx
      rw [bot_eq_eta_bot] at hx
      simp only [eta_cover, Finset.coe_singleton, Set.mem_singleton_iff] at hx
      exact hx ▸ hN.bot_mem (Set.mem_univ _)
  · rintro m₁ ⟨hm₁, hm₁n⟩ m₂ ⟨hm₂, hm₂n⟩
    rcases hm₁n with ⟨z₁, hz₁, hz₁n⟩ | ⟨hb₁, hu₁⟩
    · rcases hm₂n with ⟨z₂, hz₂, hz₂n⟩ | ⟨hb₂, hu₂⟩
      · obtain ⟨x₃, ⟨hx₃N, hx₃n⟩, h₁₃, h₂₃⟩ :=
          hN.directedOn (Set.mem_univ n.base)
            z₁ ⟨hm₁.2 (Finset.mem_coe.mpr hz₁), hz₁n⟩
            z₂ ⟨hm₂.2 (Finset.mem_coe.mpr hz₂), hz₂n⟩
        refine ⟨eta x₃, ⟨⟨hx₃N, ?_⟩, Or.inl (mem_upper_eta.mpr hx₃n)⟩,
          Or.inl ⟨z₁, hz₁, h₁₃⟩, Or.inl ⟨z₂, hz₂, h₂₃⟩⟩
        intro w hw
        simp only [eta_cover, Finset.coe_singleton, Set.mem_singleton_iff] at hw
        exact hw ▸ hx₃N
      · exact ⟨m₂, ⟨hm₂, Or.inr ⟨hb₂, hu₂⟩⟩,
          le_trans (Or.inl ⟨z₁, hz₁, hz₁n⟩) (Or.inr ⟨hb₂.symm, hu₂.symm⟩), le_rfl⟩
    · exact ⟨m₁, ⟨hm₁, Or.inr ⟨hb₁, hu₁⟩⟩, le_rfl,
        le_trans hm₂n (Or.inr ⟨hb₁.symm, hu₁.symm⟩)⟩

omit [OrderBot A] in
/-- Membership in `M(N)` is exactly what a finite normal `N` above the bases and
covers of a finite `S ⊆ M(A)` delivers. -/
theorem mem_MSub_of_subset {N : Set A} {m : MPair A} (hb : m.base ∈ N)
    (hc : (↑m.cover : Set A) ⊆ N) : m ∈ MSub N := ⟨hb, hc⟩

/-- **`M` preserves Plotkin orders.** Every finite `S ⊆ M(A)` mentions finitely
many elements of `A`; a finite normal `N` above them makes `M(N)` a finite normal
subposet of `M(A)` containing `S`. -/
theorem isPlotkinOrder_MPair (h : IsPlotkinOrder (Set.univ : Set A)) :
    IsPlotkinOrder (Set.univ : Set (MPair A)) := by
  intro S hS _
  have hT : ((fun m : MPair A => m.base) '' S ∪ ⋃ m ∈ S, (↑m.cover : Set A)).Finite :=
    (hS.image _).union (hS.biUnion fun m _ => m.cover.finite_toSet)
  obtain ⟨N, hNfin, hN, hTN⟩ := h _ hT (Set.subset_univ _)
  refine ⟨MSub N, MSub_finite hNfin, MSub_isNormalIn hN, fun m hm => ⟨?_, ?_⟩⟩
  · exact hTN (Or.inl ⟨m, hm, rfl⟩)
  · intro x hx
    exact hTN (Or.inr (Set.mem_biUnion hm hx))

end Plotkin

/-! ## Transporting a Plotkin order -/

section Transport

variable {α : Type u} {β : Type v} [Preorder α] [Preorder β]

/-- A monotone order-**reflecting** map carries a Plotkin order to a Plotkin
order. The image of a finite normal subposet is normal in the image, because
`f '' (N ∩ ↓a) = (f '' N) ∩ ↓(f a)` — the inclusion that needs reflection is
`⊇`. -/
theorem isPlotkinOrder_image {f : α → β} (hf : ∀ a b : α, f a ≤ f b ↔ a ≤ b)
    {A : Set α} (h : IsPlotkinOrder A) : IsPlotkinOrder (f '' A) := by
  intro u hu huA
  haveI := hu.to_subtype
  choose g hgA hgf using fun y : ↥u => huA y.2
  obtain ⟨N, hNfin, hN, hgN⟩ :=
    h (Set.range g) (Set.finite_range g) (by rintro _ ⟨y, rfl⟩; exact hgA y)
  refine ⟨f '' N, hNfin.image f, ⟨Set.image_mono hN.subset, fun y hy => ⟨?_, ?_⟩⟩, ?_⟩
  · obtain ⟨a, haA, rfl⟩ := hy
    obtain ⟨n, hnN, hna⟩ := hN.nonempty haA
    exact ⟨f n, ⟨n, hnN, rfl⟩, (hf n a).mpr hna⟩
  · obtain ⟨a, haA, rfl⟩ := hy
    rintro _ ⟨⟨n₁, hn₁, rfl⟩, hle₁⟩ _ ⟨⟨n₂, hn₂, rfl⟩, hle₂⟩
    obtain ⟨n, ⟨hnN, hna⟩, h₁, h₂⟩ :=
      hN.directedOn haA n₁ ⟨hn₁, (hf n₁ a).mp hle₁⟩ n₂ ⟨hn₂, (hf n₂ a).mp hle₂⟩
    exact ⟨f n, ⟨⟨n, hnN, rfl⟩, (hf n a).mpr hna⟩, (hf n₁ n).mpr h₁, (hf n₂ n).mpr h₂⟩
  · intro y hy
    exact ⟨g ⟨y, hy⟩, hgN ⟨⟨y, hy⟩, rfl⟩, hgf ⟨y, hy⟩⟩

/-- A Plotkin order as a *subset* is a Plotkin order as a *poset*: the two
readings of `K(D)` that Theorem 29 has to move between. -/
theorem isPlotkinOrder_univ_subtype {A : Set α} (h : IsPlotkinOrder A) :
    IsPlotkinOrder (Set.univ : Set ↥A) := by
  intro u hu _
  obtain ⟨N, hNfin, hN, huN⟩ :=
    h (Subtype.val '' u) (hu.image _) (by rintro _ ⟨a, _, rfl⟩; exact a.2)
  refine ⟨Subtype.val ⁻¹' N, ?_, ⟨Set.subset_univ _, fun a _ => ⟨?_, ?_⟩⟩, ?_⟩
  · exact Set.Finite.preimage Subtype.val_injective.injOn hNfin
  · obtain ⟨n, hnN, hna⟩ := hN.nonempty a.2
    exact ⟨⟨n, hN.subset hnN⟩, hnN, hna⟩
  · rintro b₁ ⟨hb₁, hb₁a⟩ b₂ ⟨hb₂, hb₂a⟩
    obtain ⟨n, ⟨hnN, hna⟩, h₁, h₂⟩ :=
      hN.directedOn a.2 b₁.val ⟨hb₁, hb₁a⟩ b₂.val ⟨hb₂, hb₂a⟩
    exact ⟨⟨n, hN.subset hnN⟩, ⟨hnN, hna⟩, h₁, h₂⟩
  · intro a ha
    exact huN ⟨a, ha, rfl⟩

end Transport

/-! ## `D⁺` and Theorem 29 -/

section Plus

open IdealCompletion

variable {A : Type u} [Preorder A] [OrderBot A]

omit [OrderBot A] in
/-- `principal` reflects the order, which is what `isPlotkinOrder_image`
consumes. It is not injective — `M(A)` is a genuine pre-order, since `(x, {x})`
and `(x, {x, y})` are equivalent whenever `x ⊑ y` — so the image lemma, not an
embedding lemma, is the one that applies. -/
theorem principal_le_principal_iff {a b : A} :
    (principal a : IdealCompletion A) ≤ principal b ↔ a ≤ b := by
  rw [principal_le_iff]
  exact Order.Ideal.mem_principal

variable (D : Type u) [CompletePartialOrder D]

/-- **`D⁺`** (Gunter & Scott §7.4): the domain of ideals over `⟨M(K(D)), ⊢⟩`,
with `⊢` the repaired pre-ordering. The paper's `A` is `D`'s basis. -/
noncomputable abbrev Plus : Type u := IdealCompletion (MPair ↥(compacts D))

/-- `D⁺` is a domain when `D` is: `M(K(D))` is a countable pre-order with a least
element `(⊥, {⊥})`, which is exactly what **Theorem 11** (`instDomain`) consumes.
Stated as `Nonempty` because the instance is data and this file records only that
it resolves. -/
theorem nonempty_domain_plus [Domain D] : Nonempty (Domain (Plus D)) := ⟨inferInstance⟩

/-- **Theorem 29, first sentence: `D` bifinite implies `D⁺` bifinite.**

Two transports and one construction: `K(D)` becomes a Plotkin order in its own
right (`isPlotkinOrder_univ_subtype`), `M` preserves that
(`isPlotkinOrder_MPair`), and `principal` carries it onto
`K(D⁺) = im(principal)` (`isPlotkinOrder_image` with
`compacts_eq_range_principal`).

The second sentence of Theorem 29 — universality of a `D` with `D ≅ D⁺` — is not
proved; the paper defers its proof to [Gun87]. -/
theorem theorem_29 (h : IsBifinite D) : IsBifinite (Plus D) := by
  have h₂ : IsPlotkinOrder (Set.univ : Set (MPair ↥(compacts D))) :=
    isPlotkinOrder_MPair (isPlotkinOrder_univ_subtype h)
  have h₃ := isPlotkinOrder_image (f := (principal : MPair ↥(compacts D) → Plus D))
    (fun _ _ => principal_le_principal_iff) h₂
  rw [Set.image_univ] at h₃
  rw [IsBifinite, compacts_eq_range_principal]
  exact h₃

alias thm29 := theorem_29

end Plus

end ScottDomains.BifiniteUniversal
