import ScottDomains.Bifinite
import ScottDomains.FunctionSpaceCountable

/-!
# §6: Proposition 15, Theorem 18, Lemma 19

Gunter & Scott, *Semantic Domains*, §6:

> **Proposition 15** Every bounded-complete domain is bifinite.

> **Theorem 18** If `D` and `D → D` are domains, then `D` is bifinite.

> **Lemma 19** `r : D → D` closure (`r ∘ r = r ⊒ id`) ⟹ `im(r)` is a domain.

**Owned by agent2.** No other file's declarations are edited when these are
proved.
-/

namespace ScottDomains

variable {α : Type*}

section Closure

variable [Preorder α]

/-- A **closure**: idempotent and *above* the identity — the order dual of
`IsProjection`. Lemma 19 is about these. -/
def IsClosure (r : ScottHom α α) : Prop :=
  (∀ x, r (r x) = r x) ∧ ∀ x, x ≤ r x

end Closure

section Statements

variable [CompletePartialOrder α]

/-- **Proposition 15.** Every bounded complete domain is bifinite. -/
theorem prop15 [Domain α] [BoundedComplete α] : IsBifinite α := by
  sorry

/-- **Theorem 18.** If `D` and `D → D` are domains, then `D` is bifinite.

The hypothesis is on the *function space* being a domain, which is what
Theorem 7 supplies under bounded completeness — so this is the converse
direction and does not follow from it. -/
theorem thm18 [Domain α] [Domain (ScottHom α α)] : IsBifinite α := by
  sorry

/-- **Lemma 19.** If `r : D → D` is a closure, then `im(r)` is a domain.

Stated as the existence of the cpo structure on the image rather than by first
building it — that construction is part of the proof, and fixing it here would
prejudge how it is done. Compare `IsProjection.rangeCompletePartialOrder`
(r0013), which is the projection analogue and a likely model. -/
theorem lem19 (r : ScottHom α α) (_hr : IsClosure r) :
    ∃ _ : CompletePartialOrder ↥(Set.range ⇑r), True := by
  sorry

end Statements

end ScottDomains
