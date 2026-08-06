import ScottDomains.ScottHom
import ScottDomains.Domain

/-!
# Embedding–projection pairs and projections

Gunter & Scott, *Semantic Domains*, §3.1:

> A pair of continuous functions `g : D → E` and `f : E → D` is said to be an
> **embedding–projection pair** (`g` is the embedding and `f` is the projection)
> if they satisfy `f ∘ g = id_D` and `g ∘ f ⊑ id_E`.

> … it is easy to see that a projection is a surjection (i.e. onto) and an
> embedding is an injection (i.e. one-to-one).

> Let `D` be a cpo. We say that a continuous function `p : D → D` is a
> **finitary projection** if `p ∘ p = p ⊑ id` and `im(p) = {p(x) | x ∈ D}` is a
> domain.

This file gives the two equational definitions and the surjection/injection
facts. The finitary condition — `im(p)` a domain — needs `im(p)` to carry a cpo
structure as a subtype, and is separate work.

## Pointwise rather than compositional

`f ∘ g = id` is stated as `∀ x, f (g x) = x` and `g ∘ f ⊑ id` as
`∀ y, g (f y) ≤ y`. The pointwise forms are equivalent — the order on `ScottHom`
*is* pointwise (`le_def`) — and they avoid needing a composition operation on
`ScottHom` before there is anything to say about one.
-/

namespace ScottDomains

namespace ScottHom

variable {α β : Type*}

section Defs

variable [Preorder α] [Preorder β]

/-- `(g, f)` is an **embedding–projection pair**: `f ∘ g = id` and `g ∘ f ⊑ id`.
`g` is the embedding, `f` the projection. -/
def IsEmbeddingProjectionPair (g : ScottHom α β) (f : ScottHom β α) : Prop :=
  (∀ x, f (g x) = x) ∧ ∀ y, g (f y) ≤ y

/-- A **projection**: idempotent and below the identity. -/
def IsProjection (p : ScottHom α α) : Prop :=
  (∀ x, p (p x) = p x) ∧ ∀ x, p x ≤ x

theorem IsProjection.idem {p : ScottHom α α} (h : IsProjection p) (x : α) : p (p x) = p x := h.1 x

theorem IsProjection.le {p : ScottHom α α} (h : IsProjection p) (x : α) : p x ≤ x := h.2 x

/-- A projection fixes its own image. -/
theorem IsProjection.apply_of_mem_range {p : ScottHom α α} (h : IsProjection p) {y : α}
    (hy : y ∈ Set.range p) : p y = y := by
  obtain ⟨x, rfl⟩ := hy
  exact h.idem x

end Defs

section EmbeddingProjection

variable [PartialOrder α] [Preorder β] {g : ScottHom α β} {f : ScottHom β α}

/-- The paper's "an embedding is an injection". Immediate from `f ∘ g = id`:
`g` has a left inverse. -/
theorem IsEmbeddingProjectionPair.injective_embedding (h : IsEmbeddingProjectionPair g f) :
    Function.Injective g := fun x y hxy => by rw [← h.1 x, ← h.1 y, hxy]

/-- The paper's "a projection is a surjection". Immediate from the same equation:
`f` has a right inverse. -/
theorem IsEmbeddingProjectionPair.surjective_projection (h : IsEmbeddingProjectionPair g f) :
    Function.Surjective f := fun x => ⟨g x, h.1 x⟩

/- UNUSED — commented out, kept for reading. That `g ∘ f` is a projection is a
real fact and the paper alludes to it ("one may well think of the image of an
embedding as a special kind of sub-cpo"), but nothing in this development needs
it: Theorem 6 goes through `p_N` and `im(p) ∩ K(D)`, never through a composite.

Note the workaround in the statement — there is no composition operation on
`ScottHom` yet, so the composite is passed in as `p` with a defining equation
`hp`. If §4 ever needs `ScottHom` composition, this is the first customer.

/-- The composite `g ∘ f` of an embedding–projection pair is a projection on `E`:
idempotent by the first equation, below the identity by the second. -/
theorem IsEmbeddingProjectionPair.isProjection_comp
    (h : IsEmbeddingProjectionPair g f) (p : ScottHom β β) (hp : ∀ y, p y = g (f y)) :
    IsProjection p := by
  refine ⟨fun y => ?_, fun y => ?_⟩
  · rw [hp, hp, h.1]
  · rw [hp]
    exact h.2 y
-/

end EmbeddingProjection

section RangeCpo

variable [CompletePartialOrder α] {p : ScottHom α α}

/-- A projection fixes `⊥`: `p ⊥ ≤ ⊥` from `p ⊑ id`, and `⊥ ≤ p ⊥` always. -/
theorem IsProjection.map_bot (hp : IsProjection p) : p ⊥ = ⊥ :=
  le_antisymm (hp.le ⊥) bot_le

theorem IsProjection.bot_mem_range (hp : IsProjection p) : (⊥ : α) ∈ Set.range ⇑p :=
  ⟨⊥, hp.map_bot⟩

/-- A directed set in the image has a directed image in the ambient order. -/
theorem directedOn_val_image {s : Set ↥(Set.range ⇑p)} (hs : DirectedOn (· ≤ ·) s) :
    DirectedOn (· ≤ ·) (Subtype.val '' s) := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  obtain ⟨c, hc, hac, hbc⟩ := hs a ha b hb
  exact ⟨c.val, ⟨c, hc, rfl⟩, hac, hbc⟩

/-- The image of a projection is closed under directed suprema: continuity moves
`p` inside, and `p` fixes its own image. The empty case is `p ⊥ = ⊥`, since
`sSup ∅` is a least element. -/
theorem IsProjection.apply_sSup_of_directed (hp : IsProjection p)
    {s : Set ↥(Set.range ⇑p)} (hs : DirectedOn (· ≤ ·) s) :
    p (sSup (Subtype.val '' s)) = sSup (Subtype.val '' s) := by
  rcases Set.eq_empty_or_nonempty s with rfl | hne
  · have hbot : sSup ((Subtype.val : ↥(Set.range ⇑p) → α) '' ∅) = ⊥ := by
      rw [Set.image_empty]
      exact le_antisymm (DirectedOn.sSup_le (by simp [DirectedOn]) (by simp)) bot_le
    rw [hbot, hp.map_bot]
  · have hdir := directedOn_val_image hs
    have hlub : IsLUB ((⇑p) '' (Subtype.val '' s)) (p (sSup (Subtype.val '' s))) :=
      p.scottContinuous (hne.image _) hdir hdir.isLUB_sSup
    have himg : (⇑p) '' (Subtype.val '' s) = Subtype.val '' s := by
      ext y
      constructor
      · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
        exact ⟨a, ha, (hp.apply_of_mem_range a.2).symm⟩
      · rintro ⟨a, ha, rfl⟩
        exact ⟨a.val, ⟨a, ha, rfl⟩, hp.apply_of_mem_range a.2⟩
    rw [himg] at hlub
    exact hlub.unique hdir.isLUB_sSup

/-- **The image of a projection is a cpo.** Suprema are computed in the ambient
order and pushed back through `p`, which lands in the range *by construction* —
so no case split on directedness is needed and the definition is free of
`Classical.choice`, unlike `ScottHom`'s. On a directed set the extra `p` is the
identity, which is what `lubOfDirected` records. -/
@[reducible] def IsProjection.rangeCompletePartialOrder (hp : IsProjection p) :
    CompletePartialOrder ↥(Set.range ⇑p) :=
  { (inferInstance : PartialOrder ↥(Set.range ⇑p)) with
    sSup := fun s => ⟨p (sSup (Subtype.val '' s)), Set.mem_range_self _⟩
    bot := ⟨⊥, hp.bot_mem_range⟩
    bot_le := fun _ => bot_le
    lubOfDirected := fun s hs => by
      constructor
      · intro a ha
        show a.val ≤ p (sSup (Subtype.val '' s))
        rw [hp.apply_sSup_of_directed hs]
        exact (directedOn_val_image hs).le_sSup ⟨a, ha, rfl⟩
      · intro u hu
        show p (sSup (Subtype.val '' s)) ≤ u.val
        rw [hp.apply_sSup_of_directed hs]
        refine (directedOn_val_image hs).sSup_le ?_
        rintro _ ⟨a, ha, rfl⟩
        exact hu ha }

/-- A **finitary projection**: a projection whose image is a domain.

The cpo structure on `im(p)` depends on the projection *proof*, so it cannot be
an instance; the `Domain` claim is applied to it explicitly. Proof irrelevance
makes the choice of `hp` immaterial. -/
def IsFinitaryProjection (p : ScottHom α α) : Prop :=
  ∃ hp : IsProjection p, @Domain _ (IsProjection.rangeCompletePartialOrder hp)

theorem IsFinitaryProjection.isProjection {p : ScottHom α α} (h : IsFinitaryProjection p) :
    IsProjection p := h.choose

end RangeCpo

end ScottHom

end ScottDomains
