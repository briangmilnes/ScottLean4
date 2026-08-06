import ScottDomains.ScottHom

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

/-- The composite `g ∘ f` of an embedding–projection pair is a projection on `E`:
idempotent by the first equation, below the identity by the second. -/
theorem IsEmbeddingProjectionPair.isProjection_comp
    (h : IsEmbeddingProjectionPair g f) (p : ScottHom β β) (hp : ∀ y, p y = g (f y)) :
    IsProjection p := by
  refine ⟨fun y => ?_, fun y => ?_⟩
  · rw [hp, hp, h.1]
  · rw [hp]
    exact h.2 y

end EmbeddingProjection

end ScottHom

end ScottDomains
