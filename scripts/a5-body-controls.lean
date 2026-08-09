/-!
Controls for the r0044 Class-2 sweep in agent5's area. A zero is only a
measurement if the instrument is shown to fire on things that are vacuous and to
stay silent on things that are not, so both directions are exercised here.

**Positive controls** re-derive a flagged conclusion without the hypothesis the
instrument called free. If the kernel accepts, the hypothesis was free in fact.

**Negative control** takes the hypothesis the whole of Theorem 18 rests on —
`PropertyM`'s `IsAlgebraic (ScottHom D D)` — and asks the instrument's own
question of it. `IsAlgebraic` has eleven hypothesis-free providers in this
package, so the binder was *tested* and rejected, not skipped for want of a
candidate. The `example` below is expected to FAIL to elaborate; its error in the
log is the control's result. Leave it uncommented.
-/

open ScottDomains

namespace A5Control

/-! ### Positive control 1 — agent3's handoff lead, confirmed

`EffectivePresentation.countable_compacts` takes `(d : EffectivePresentation α)`
and concludes `(compacts α).Countable`, which `[Domain α]` already gives via
`Domain.countable_compacts`. Its own docstring concedes the point: "which the
`Domain` class already required, so this is a consistency check on the definition
rather than new information." The conclusion below is the same one, with `d`
gone. -/
theorem countable_compacts {α : Type u} [CompletePartialOrder α] [Domain α] :
    (compacts α).Countable :=
  Domain.countable_compacts

/-! ### Positive control 2 — the free hypotheses of Lemma 17's codomain -/

example {α β : Type} [CompletePartialOrder α] [CompletePartialOrder β]
    [Domain α] [Domain β] [BoundedComplete β] (h₁ : IsBifinite α) :
    IsBifinite (ScottHom α β) := lem17_fun h₁ prop15

/-! ### Positive control 3 — Theorem 27's hypothesis -/

example (D : Type) [CompletePartialOrder D] [Domain D] [BoundedComplete D] :
    ∃ (e : ScottHom D Dyadic.U) (p : ScottHom Dyadic.U D),
      ScottHom.IsEmbeddingProjectionPair e p :=
  Dyadic.thm27 D (Atomless.isNormallyRepresented _)

/-! ### Positive control 4 — Theorem 18's `hcor`, the one the plan asked about -/

example (D : Type) [CompletePartialOrder D] [Domain D] [Domain (ScottHom D D)] :
    IsBifinite D :=
  PropertyM.thm18_of_cor136 JungCor136.fixedPointOfCompactDeflationIsCompact

/-! ### Negative control — Theorem 18's load-bearing hypothesis

`PropertyM.hasCompleteMub_pair` is stated at `[CompletePartialOrder D]` alone and
takes `hAlgF : IsAlgebraic (ScottHom D D)` explicitly. If that hypothesis were
free the way `hcor` is, this would elaborate. It must not. -/
example {D : Type} [CompletePartialOrder D] {a₁ a₂ : D}
    (ha₁ : IsCompactElement a₁) (ha₂ : IsCompactElement a₂)
    (hCount : (compacts (ScottHom D D)).Countable) :
    HasCompleteMub (compacts D) {a₁, a₂} :=
  PropertyM.hasCompleteMub_pair inferInstance hCount ha₁ ha₂

end A5Control

#print axioms A5Control.countable_compacts
