import ScottDomains.Domain

/-!
# Normal subposets and Lemma 4

Gunter & Scott, *Semantic Domains*, §3.1:

> **Definition:** Let `A` be a poset and suppose `N ⊆ A`. Then `N` is said to be
> **normal** in `A` (and we write `N ◁ A`) if, for every `x ∈ A`, the set
> `N ∩ ↓x` is directed.

> **Lemma 4** Let `C` be a poset with a least element and suppose `A` and `B` are
> subsets of `C`.
> 1. If `A ◁ B ◁ C` then `A ◁ C`.
> 2. If `A ⊆ B ⊆ C` and `A ◁ C` then `A ◁ B`.
> 3. If `A ◁ C`, then `⊥ ∈ A`.
> 4. `⟨P(C), ◁⟩` is a cpo with `{⊥}` as its least element.

## Nonemptiness is part of "directed"

Part 3 is **false** under Mathlib's `DirectedOn`, which holds vacuously on `∅`:
the empty set would be normal in everything and would not contain `⊥`. The
paper's *directed* asks every finite subset — including `∅` — for an upper bound
*in the set*, which forces nonemptiness. `IsNormalIn` carries that conjunct
explicitly, exactly as `WayBelow` does, and part 3 is what would fail without it.

## Part 4 without a subtype

"`⟨P(C), ◁⟩` is a cpo with `{⊥}` least" is recorded as the facts that constitute
it — `◁` is a partial order on normal subposets, a `◁`-directed family has `⋃` as
its `◁`-least upper bound, and `{⊥}` is `◁`-least — stated about sets directly.
That is the same content without the `SupSet`-totality plumbing a subtype
instance would need, and it is the form Lemma 5 and Theorem 6 cite.
-/

namespace ScottDomains

variable {α : Type*}

section Preorder

variable [Preorder α] {N A B C : Set α}

/-- `N ◁ A`: `N` is a subset of `A` whose elements below any `x ∈ A` form a
nonempty directed set. -/
def IsNormalIn (N A : Set α) : Prop :=
  N ⊆ A ∧ ∀ x ∈ A, (N ∩ Set.Iic x).Nonempty ∧ DirectedOn (· ≤ ·) (N ∩ Set.Iic x)

@[inherit_doc] scoped infix:50 " ◁ " => IsNormalIn

theorem IsNormalIn.subset (h : N ◁ A) : N ⊆ A := h.1

theorem IsNormalIn.nonempty (h : N ◁ A) {x : α} (hx : x ∈ A) :
    (N ∩ Set.Iic x).Nonempty := (h.2 x hx).1

theorem IsNormalIn.directedOn (h : N ◁ A) {x : α} (hx : x ∈ A) :
    DirectedOn (· ≤ ·) (N ∩ Set.Iic x) := (h.2 x hx).2

/-- Every set is normal in itself: `x` is its own upper bound in `N ∩ ↓x`. -/
theorem IsNormalIn.refl (N : Set α) : N ◁ N :=
  ⟨subset_rfl, fun x hx => ⟨⟨x, hx, le_rfl⟩, fun _ ha _ hb => ⟨x, ⟨hx, le_rfl⟩, ha.2, hb.2⟩⟩⟩

/-- **Lemma 4.1.** `A ◁ B ◁ C` implies `A ◁ C`. Given `a₁, a₂ ∈ A ∩ ↓x` with
`x ∈ C`, directedness of `B ∩ ↓x` produces `b ∈ B` above both, and then
directedness of `A ∩ ↓b` — available because `b ∈ B` — produces the witness,
which is below `x` because it is below `b`. -/
theorem IsNormalIn.trans (hAB : A ◁ B) (hBC : B ◁ C) : A ◁ C := by
  refine ⟨hAB.subset.trans hBC.subset, fun x hx => ⟨?_, ?_⟩⟩
  · obtain ⟨b, hbB, hbx⟩ := hBC.nonempty hx
    obtain ⟨a, haA, hab⟩ := hAB.nonempty hbB
    exact ⟨a, haA, hab.trans hbx⟩
  · rintro a₁ ⟨ha₁, hx₁⟩ a₂ ⟨ha₂, hx₂⟩
    obtain ⟨b, ⟨hbB, hbx⟩, h₁b, h₂b⟩ :=
      hBC.directedOn hx _ ⟨hAB.subset ha₁, hx₁⟩ _ ⟨hAB.subset ha₂, hx₂⟩
    obtain ⟨a, ⟨haA, hab⟩, h₁a, h₂a⟩ :=
      hAB.directedOn hbB _ ⟨ha₁, h₁b⟩ _ ⟨ha₂, h₂b⟩
    exact ⟨a, ⟨haA, hab.trans hbx⟩, h₁a, h₂a⟩

/-- **Lemma 4.2.** Normality passes to an intermediate subset: every `x ∈ B` is
already an `x ∈ C`. -/
theorem IsNormalIn.mono_right (hAB : A ⊆ B) (hBC : B ⊆ C) (hAC : A ◁ C) : A ◁ B :=
  ⟨hAB, fun x hx => hAC.2 x (hBC hx)⟩

end Preorder

section PartialOrder

variable [PartialOrder α] {A B C : Set α}

/-- `◁` is antisymmetric, being a refinement of `⊆`. -/
theorem IsNormalIn.antisymm (hAB : A ◁ B) (hBA : B ◁ A) : A = B :=
  Set.Subset.antisymm hAB.subset hBA.subset

end PartialOrder

section OrderBot

variable [PartialOrder α] [OrderBot α] {A B C : Set α} {M : Set (Set α)}

/-- **Lemma 4.3.** A normal subposet contains `⊥`. Taking `x := ⊥`, nonemptiness
of `A ∩ ↓⊥` produces some `y ∈ A` with `y ≤ ⊥`, and `le_bot_iff` makes it `⊥`.

This is the part that fails if "directed" is read without nonemptiness. -/
theorem IsNormalIn.bot_mem (hbot : (⊥ : α) ∈ C) (hAC : A ◁ C) : (⊥ : α) ∈ A := by
  obtain ⟨y, hyA, hy⟩ := hAC.nonempty hbot
  rwa [le_bot_iff.mp hy] at hyA

/-- `{⊥}` is normal in any set containing `⊥`. -/
theorem singleton_bot_isNormalIn (hbot : (⊥ : α) ∈ C) : ({⊥} : Set α) ◁ C := by
  refine ⟨Set.singleton_subset_iff.mpr hbot, fun x _ => ⟨⟨⊥, rfl, bot_le⟩, ?_⟩⟩
  rintro a ⟨rfl, _⟩ b ⟨rfl, _⟩
  exact ⟨⊥, ⟨rfl, bot_le⟩, le_rfl, le_rfl⟩

/-- **Lemma 4.4, least element.** `{⊥}` is `◁`-below every normal subposet of
`C`: it is contained in one by Lemma 4.3, and `⊥` is its own upper bound. -/
theorem singleton_bot_isNormalIn_of_isNormalIn (hbot : (⊥ : α) ∈ C) (hAC : A ◁ C) :
    ({⊥} : Set α) ◁ A := by
  refine ⟨Set.singleton_subset_iff.mpr (hAC.bot_mem hbot), fun x _ => ⟨⟨⊥, rfl, bot_le⟩, ?_⟩⟩
  rintro a ⟨rfl, _⟩ b ⟨rfl, _⟩
  exact ⟨⊥, ⟨rfl, bot_le⟩, le_rfl, le_rfl⟩

end OrderBot

section Union

variable [Preorder α] {C : Set α} {M : Set (Set α)}

/-- **Lemma 4.4, suprema exist.** The union of a `◁`-directed family of normal
subposets of `C` is normal in `C`. Needs no least element. -/
theorem isNormalIn_sUnion (hMne : M.Nonempty)
    (hM : ∀ N ∈ M, N ◁ C) (hdir : DirectedOn IsNormalIn M) : (⋃₀ M) ◁ C := by
  refine ⟨Set.sUnion_subset fun N hN => (hM N hN).subset, fun x hx => ⟨?_, ?_⟩⟩
  · obtain ⟨N, hN⟩ := hMne
    obtain ⟨y, hyN, hyx⟩ := (hM N hN).nonempty hx
    exact ⟨y, ⟨N, hN, hyN⟩, hyx⟩
  · rintro a₁ ⟨⟨N₁, hN₁, ha₁⟩, hx₁⟩ a₂ ⟨⟨N₂, hN₂, ha₂⟩, hx₂⟩
    obtain ⟨N, hN, h₁, h₂⟩ := hdir N₁ hN₁ N₂ hN₂
    obtain ⟨a, ⟨haN, hax⟩, hle₁, hle₂⟩ :=
      (hM N hN).directedOn hx _ ⟨h₁.subset ha₁, hx₁⟩ _ ⟨h₂.subset ha₂, hx₂⟩
    exact ⟨a, ⟨⟨N, hN, haN⟩, hax⟩, hle₁, hle₂⟩

/-- **Lemma 4.4, the union is an upper bound.** -/
theorem isNormalIn_sUnion_of_mem (hdir : DirectedOn IsNormalIn M)
    {N : Set α} (hN : N ∈ M) : N ◁ (⋃₀ M) := by
  refine ⟨fun a ha => ⟨N, hN, ha⟩, ?_⟩
  rintro x ⟨N', hN', hx⟩
  obtain ⟨N'', hN'', hNN'', hN'N''⟩ := hdir N hN N' hN'
  exact ⟨hNN''.nonempty (hN'N''.subset hx), hNN''.directedOn (hN'N''.subset hx)⟩

/-- **Lemma 4.4, the union is least.** Any `◁`-upper bound of the family is a
`◁`-upper bound of the union. -/
theorem isNormalIn_sUnion_le (hMne : M.Nonempty) (hdir : DirectedOn IsNormalIn M)
    {U : Set α} (hU : ∀ N ∈ M, N ◁ U) : (⋃₀ M) ◁ U := by
  refine ⟨Set.sUnion_subset fun N hN => (hU N hN).subset, fun x hx => ⟨?_, ?_⟩⟩
  · obtain ⟨N, hN⟩ := hMne
    obtain ⟨y, hyN, hyx⟩ := (hU N hN).nonempty hx
    exact ⟨y, ⟨N, hN, hyN⟩, hyx⟩
  · rintro a₁ ⟨⟨N₁, hN₁, ha₁⟩, hx₁⟩ a₂ ⟨⟨N₂, hN₂, ha₂⟩, hx₂⟩
    obtain ⟨N, hN, h₁, h₂⟩ := hdir N₁ hN₁ N₂ hN₂
    obtain ⟨a, ⟨haN, hax⟩, hle₁, hle₂⟩ :=
      (hU N hN).directedOn hx _ ⟨h₁.subset ha₁, hx₁⟩ _ ⟨h₂.subset ha₂, hx₂⟩
    exact ⟨a, ⟨⟨N, hN, haN⟩, hax⟩, hle₁, hle₂⟩

end Union

end ScottDomains
