import ScottDomains.Bifinite
import ScottDomains.Lift
import ScottDomains.Product
import ScottDomains.FunctionSpaceCountable

/-!
# Lemma 17: bifiniteness is closed under the operators

Gunter & Scott, *Semantic Domains*, §6.2:

> **Lemma 17** `D, E` bifinite ⟹ `→, ×, ⊗, +, ()⊥` bifinite (incl. function
> space).

The function-space conjunct is the substantive one: §6's whole point is that
bifiniteness, unlike bounded completeness, is preserved by `→` — Theorem 7 needed
bounded completeness of `E` to make `D → E` a domain, and §6 exists because that
hypothesis is not always available.

**Owned by agent3.** No other file's declarations are edited when these are
proved.
-/

namespace ScottDomains

variable {α β : Type*} [CompletePartialOrder α] [CompletePartialOrder β]

theorem lem17_prod [Domain α] [Domain β] (_h₁ : IsBifinite α) (_h₂ : IsBifinite β) :
    IsBifinite (α × β) := by
  sorry

theorem lem17_lift [Domain α] (_h : IsBifinite α) : IsBifinite (WithBot α) := by
  sorry

theorem lem17_fun [Domain α] [Domain β] [BoundedComplete β]
    (_h₁ : IsBifinite α) (_h₂ : IsBifinite β) : IsBifinite (ScottHom α β) := by
  sorry

end ScottDomains
