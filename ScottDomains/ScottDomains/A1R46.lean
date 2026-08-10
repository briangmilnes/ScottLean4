import ScottDomains.A2Lemma28
import ScottDomains.Lemma30
import ScottDomains.Effective.FunctionSpace
-- `R49.Agent3.isStepEnumeration_scottHom`, which r0049's restatement of
-- `Effective.StepFunctionsDecidable` makes this file's `_of_unconditional` need.
import ScottDomains.Effective.A3StepDecidable

/-!
# r0046, agent1: two refuted universal closures and the record of one restatement

This file holds the two Lean-level obligations of r0046's agent1 stream. Both
exist so that a *bookkeeping* judgement is a kernel-checked fact rather than a
line in a report.

## 1. `Lemma30.Lemma30`'s universal closure is false

`scripts/a6-query.lean` scores a `def … : Prop` as undischarged when no package
theorem concludes it with no proof hypothesis. A refutation concludes `¬ D`,
whose head is `Not`, so a claim that has been *proved false* reads exactly like
one nobody has touched. r0045 refuted two of the ten claims on the list and both
stayed on it.

r0046 fixes the instrument (`REFUTEDBY` records, criterion and soundness argument
in `scripts/a6-query.lean`'s own docstring) and supplies the one refutation that
was argued in prose but never written down: `Lemma30`'s universal closure over
its carrier. It is one line, because Lemma 30 contains Lemma 28's nine conjuncts
and r0045's agent2 already refuted those.

**This is a fact about the parameterization, not about the paper.** Gunter &
Scott's Lemma 30 is a statement about §7.4's own `V`; the carrier is a parameter
here only so that the proposition and its instantiation are separate
declarations, exactly as `PRep.Lemma28` and `PRep.Lemma28AtU` are. The claim that
survives is `Lemma30.Lemma30AtV`, and it is `Lemma30` at `W := V`
definitionally.

## 2. The statement `Effective.StepFunctionsDecidable` used to have

r0046 restated that claim to the sentence the paper prints, under the round's
narrow authorization to do so. The condition on such a change is that the old
statement not vanish and that the direction of the change be checkable. Both are
met here: `StepFunctionsDecidableUnconditional` is the old statement, verbatim,
and `stepFunctionsDecidable_of_unconditional` is the kernel's check that the old
implies the new.

Nothing in this file is a claim of the paper. `StepFunctionsDecidableUnconditional`
is a **rejected transcription**, kept for citation; it must not be added to
`scripts/a6-claims.txt`.
-/

namespace ScottDomains.R46.Agent1

open ScottDomains.Effective

/-! ## `Lemma30`'s universal closure -/

/-- **The universal reading of `Lemma30.Lemma30` is false.** A theorem
discharging the `Lemma30` row in `a6-query.lean`'s sense would have this type.

The proof is projection: `Lemma30.lemma_30_iff_lemma28_and_plotkin` says
`Lemma30 W ↔ PRep.Lemma28 W ∧ IsPRepresentable W Lemma30.plotkinOp`, so a
universal `Lemma30` would give a universal `PRep.Lemma28`, which
`ScottDomains.R45.Agent2.not_forall_lemma28` refutes at `Flat Empty`. The tenth
conjunct `(·)♮` is not used and is not the reason the closure fails.

What this does **not** say: it says nothing against `Lemma30.Lemma30AtV`, which
is this proposition at `W := Colimit.V` and is open, nor against the paper, which
states Lemma 30 over `V` and not over an arbitrary carrier. -/
theorem not_forall_lemma30 :
    ¬ ∀ (W : Type) (inst : CompletePartialOrder W), @Lemma30.Lemma30 W inst :=
  fun h =>
    ScottDomains.R45.Agent2.not_forall_lemma28 fun W inst =>
      ((@Lemma30.lemma_30_iff_lemma28_and_plotkin W inst).mp (h W inst)).1

/-! ## The pre-r0046 statement of `StepFunctionsDecidable` -/

section StepFunctions

variable {α β : Type*} [CompletePartialOrder α] [Domain α]
  [CompletePartialOrder β] [Domain β] [BoundedComplete β]

/-- **`Effective.StepFunctionsDecidable` as it stood through r0045**, kept
verbatim so the restatement r0046 made is auditable against the thing it
replaced rather than against a paraphrase.

It asserts that the enumeration `scottHom d e` of `K(D → E)` is recursive for
**arbitrary** presentations `d` and `e` — including presentations whose own
ordering is not computable, which `Effective.nonempty_effectivePresentation`
shows every domain has. Theorem 7's proof sentence (printed p. 12) says
"…using the effective presentations of `D` and `E`", and §3.2's Definition
(printed p. 11) makes an effective presentation one whose two conditions are
*effectively decidable*. The antecedent was dropped in transcription; restoring
it is the whole of the r0046 change.

**Not a claim of the paper.** No sentence of Gunter & Scott asserts this, and it
must not be counted as an open result. r0045's agent1 gave a refutation sketch
for it, in three named steps, and that sketch is not kernel-checked; the case for
the restatement does not rest on it, because a transcription that drops a printed
antecedent is defective whether or not the over-strong reading happens to be
false. -/
def StepFunctionsDecidableUnconditional (d : EffectivePresentation α)
    (e : EffectivePresentation β) : Prop :=
  IsRecursive (scottHom d e)

/-- **The restatement is a weakening of the proposition and not of the paper.**

The kernel checks here that the pre-r0046 statement implies the post-r0046 one,
which is the direction that fixes what changed: two hypotheses were added, and
nothing else. The complementary check — that no bar was lowered — is that
`Effective.Theorem7ArrowRecursive`, the transcription of the sentence this one
serves, already carried `IsRecursive d → IsRecursive e →` and is untouched. The
claim now has exactly the hypotheses its consumer always had, which is why
`ScottDomains.R45.Agent1.theorem_7_arrowRecursive_of_stepFunctionsDecidable` can
now take the claim's own universal closure as its hypothesis instead of a
hand-strengthened variant of it.

**The statement is unchanged by r0049; the proof is not.**
`Effective.StepFunctionsDecidable` no longer names `Effective.scottHom d e`, so
the witness has to be supplied: `R49.Agent3.isStepEnumeration_scottHom` says the
enumeration this file's statement is about is one of those the restated claim
ranges over. The r0049 change therefore reaches this theorem as one extra
component of a pair and nothing else, which is the evidence that it was a
weakening — had it been a strengthening this proof would not exist. -/
theorem stepFunctionsDecidable_of_unconditional {d : EffectivePresentation α}
    {e : EffectivePresentation β} (h : StepFunctionsDecidableUnconditional d e) :
    StepFunctionsDecidable d e :=
  fun _ _ => ⟨scottHom d e, R49.Agent3.isStepEnumeration_scottHom d e, h⟩

end StepFunctions

end ScottDomains.R46.Agent1
