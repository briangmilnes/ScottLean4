import ScottDomains.Smash
import ScottDomains.Lift
import ScottDomains.StrictHom
import ScottDomains.Product
import ScottDomains.FunctionSpaceCountable

/-!
# Lemma 10: bounded completeness is closed under the operators

Gunter & Scott, *Semantic Domains*, §4.5:

> **Lemma 10** If `D` and `E` are bounded complete domains then so are the cpo's
> `D → E`, `D →⊥ E`, `D × E`, `D ⊗ E`, `D + E`, `D⊥`.

The `D → E` conjunct is **already proved** — it is Theorem 7's bounded-complete
half (`ScottHom`'s `BoundedComplete` instance, r0007) — so it is not restated
here. The remaining conjuncts are open, one statement each so they can be
discharged independently.

**Owned by agent1.** No other file's declarations are edited when these are
proved.
-/

namespace ScottDomains

variable {α β : Type*} [CompletePartialOrder α] [CompletePartialOrder β]

theorem lem10_prod [Domain α] [BoundedComplete α] [Domain β] [BoundedComplete β] :
    BoundedComplete (α × β) := by
  sorry

theorem lem10_smash [Domain α] [BoundedComplete α] [Domain β] [BoundedComplete β] :
    BoundedComplete (Smash α β) := by
  sorry

theorem lem10_lift [Domain α] [BoundedComplete α] : BoundedComplete (WithBot α) := by
  sorry

theorem lem10_strict [Domain α] [BoundedComplete α] [Domain β] [BoundedComplete β] :
    BoundedComplete (StrictHom α β) := by
  sorry

end ScottDomains
