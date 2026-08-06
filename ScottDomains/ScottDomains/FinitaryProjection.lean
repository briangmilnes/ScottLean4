import ScottDomains.Projection
import ScottDomains.NormalSubposet

/-!
# Lemma 5: the basis of `im(p)`

Gunter & Scott, *Semantic Domains*, §3.1:

> **Lemma 5** If `D` is a domain and `p : D → D` is a finitary projection, then
> the set of compact elements of `im(p)` is just `im(p) ∩ K(D)`. Moreover,
> `im(p) ∩ K(D) ◁ K(D)`.

## Where the hypotheses are actually spent

The first sentence needs **only that `p` is a projection** — neither `D` being a
domain nor `im(p)` being one is used. Both directions run on the two projection
equations:

* if `y ∈ im(p)` is compact in `D`, it is compact in `im(p)`, because a directed
  set of the subtype has the same least upper bound computed either way
  (`isLUB_val_image`);
* if `y` is compact in `im(p)`, it is compact in `D`, because a directed `s ⊆ D`
  can be pushed into `im(p)` by `p`, and `p x ≤ x` converts the witness back.

The second sentence is where **finitary** is spent: directedness of
`im(p) ∩ K(D) ∩ ↓x` comes from algebraicity of `im(p)`, applied to `p x`.

`isLUB_val_image` is worth isolating: an upper bound `v` of the image need not
lie in `im(p)`, but `p v` does, and `p v` is still an upper bound because `p`
fixes the image and is monotone. So the subtype's least upper bound is the
ambient one, with no completeness assumed.
-/

namespace ScottDomains

namespace ScottHom

variable {α : Type*} [CompletePartialOrder α] {p : ScottHom α α}

/-- A least upper bound in `im(p)` is a least upper bound in `D`. An upper bound
`v` of the image need not lie in `im(p)`, but `p v` does, and it is still an
upper bound; `p v ≤ v` then finishes it. -/
theorem IsProjection.isLUB_val_image (hp : IsProjection p) {s : Set ↥(Set.range ⇑p)}
    {u : ↥(Set.range ⇑p)} (hu : IsLUB s u) : IsLUB (Subtype.val '' s) u.val := by
  constructor
  · rintro _ ⟨a, ha, rfl⟩
    exact hu.1 ha
  · intro v hv
    have hpv : (⟨p v, Set.mem_range_self v⟩ : ↥(Set.range ⇑p)) ∈ upperBounds s := by
      intro a ha
      show a.val ≤ p v
      calc a.val = p a.val := (hp.apply_of_mem_range a.2).symm
        _ ≤ p v := p.monotone (hv ⟨a, ha, rfl⟩)
    exact le_trans (show u.val ≤ p v from hu.2 hpv) (hp.le v)

/-- **Lemma 5, first sentence.** The compact elements of `im(p)` are exactly the
elements of `im(p)` that are compact in `D`. Needs only that `p` is a projection. -/
theorem IsProjection.isCompactElement_iff (hp : IsProjection p)
    {y : ↥(Set.range ⇑p)} : IsCompactElement y ↔ IsCompactElement y.val := by
  constructor
  · -- compact in `im(p)` ⟹ compact in `D`: push `s` into `im(p)` by `p`.
    intro hy s u hne hs hlub hyu
    have hdir : DirectedOn (· ≤ ·) ((fun x => (⟨p x, Set.mem_range_self x⟩ :
        ↥(Set.range ⇑p))) '' s) := by
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      obtain ⟨c, hc, hac, hbc⟩ := hs a ha b hb
      exact ⟨⟨p c, Set.mem_range_self c⟩, ⟨c, hc, rfl⟩, p.monotone hac, p.monotone hbc⟩
    have hpu : IsLUB ((fun x => (⟨p x, Set.mem_range_self x⟩ : ↥(Set.range ⇑p))) '' s)
        ⟨p u, Set.mem_range_self u⟩ := by
      have hcont : IsLUB (⇑p '' s) (p u) := p.scottContinuous hne hs hlub
      constructor
      · rintro _ ⟨a, ha, rfl⟩
        exact p.monotone (hlub.1 ha)
      · intro v hv
        show p u ≤ v.val
        refine hcont.2 ?_
        rintro _ ⟨a, ha, rfl⟩
        exact hv ⟨a, ha, rfl⟩
    obtain ⟨_, ⟨x, hx, rfl⟩, hyx⟩ :=
      hy _ ⟨p u, Set.mem_range_self u⟩ (hne.image _) hdir hpu
        (show y.val ≤ p u from
          (hp.apply_of_mem_range y.2).symm.trans_le (p.monotone hyu))
    exact ⟨x, hx, (show y.val ≤ p x from hyx).trans (hp.le x)⟩
  · -- compact in `D` ⟹ compact in `im(p)`: the two least upper bounds agree.
    intro hy s u hne hs hlub hyu
    obtain ⟨_, ⟨a, ha, rfl⟩, hle⟩ :=
      hy (Subtype.val '' s) u.val (hne.image _) (directedOn_val_image hs)
        (hp.isLUB_val_image hlub) hyu
    exact ⟨a, ha, hle⟩

/-- The `Domain` structure that `IsFinitaryProjection` asserts on `im(p)`. -/
theorem IsFinitaryProjection.domain (hp : IsFinitaryProjection p) :
    @Domain _ (IsProjection.rangeCompletePartialOrder hp.isProjection) := hp.choose_spec

/-- **Lemma 5, second sentence.** `im(p) ∩ K(D)` is a normal subposet of `K(D)`.

This is where *finitary* is spent: given compact `a, b ∈ im(p)` below a compact
`x`, both lie below `p x` in `im(p)`, and algebraicity of `im(p)` makes the
compacts below `p x` directed, producing the common upper bound. It is compact in
`D` again by the first sentence, and below `x` because `p x ≤ x`. -/
theorem IsFinitaryProjection.isNormalIn_compacts (hp : IsFinitaryProjection p) :
    (Set.range ⇑p ∩ compacts α) ◁ compacts α := by
  letI : CompletePartialOrder ↥(Set.range ⇑p) :=
    IsProjection.rangeCompletePartialOrder hp.isProjection
  haveI : Domain ↥(Set.range ⇑p) := hp.domain
  have hproj := hp.isProjection
  refine ⟨Set.inter_subset_right, fun x hx => ⟨?_, ?_⟩⟩
  · exact ⟨⊥, ⟨hproj.bot_mem_range, isCompactElement_bot⟩, bot_le⟩
  · rintro a ⟨⟨haR, haK⟩, hax⟩ b ⟨⟨hbR, hbK⟩, hbx⟩
    -- Lift `a` and `b` into `im(p)`, where they are compact and below `p x`.
    set A : ↥(Set.range ⇑p) := ⟨a, haR⟩
    set B : ↥(Set.range ⇑p) := ⟨b, hbR⟩
    set X : ↥(Set.range ⇑p) := ⟨p x, Set.mem_range_self x⟩
    have hA : A ∈ compactsBelow X :=
      ⟨hproj.isCompactElement_iff.mpr haK,
        show a ≤ p x from (hproj.apply_of_mem_range haR).symm.trans_le (p.monotone hax)⟩
    have hB : B ∈ compactsBelow X :=
      ⟨hproj.isCompactElement_iff.mpr hbK,
        show b ≤ p x from (hproj.apply_of_mem_range hbR).symm.trans_le (p.monotone hbx)⟩
    obtain ⟨C, ⟨hCk, hCX⟩, hAC, hBC⟩ :=
      IsAlgebraic.directedOn_compactsBelow X A hA B hB
    exact ⟨C.val, ⟨⟨C.2, hproj.isCompactElement_iff.mp hCk⟩,
      (show C.val ≤ p x from hCX).trans (hproj.le x)⟩, hAC, hBC⟩

end ScottHom

end ScottDomains
