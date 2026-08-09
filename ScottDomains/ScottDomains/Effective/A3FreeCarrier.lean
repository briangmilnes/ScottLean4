import ScottDomains.Effective.FunctionSpace

/-!
# r0047, agent3: the pre-r0047 statement of `PreservesRecursivePresentation`, and
what the restatement bought

r0047 restated `Effective.PreservesRecursivePresentation` to the sentence the
paper prints, under the round's narrow authorization to change that one `def`.
The conditions on such a change are r0046's: the old statement does not vanish,
the direction of the change is kernel-checked, and the new statement is not
weaker at the paper's intent. All three are discharged here.

| # | Obligation | Discharged by |
| -- | --------- | ------------- |
| 1 | the old statement, verbatim | `PreservesRecursivePresentationFreeCarrier` |
| 2 | the direction of the change | `freeCarrier_of_preservesRecursivePresentation` — the new claim implies the old at every carrier the operator produces |
| 3 | no bar lowered | `preservesRecursivePresentation_arrowOp_iff` — the new claim at the arrow operator **is** `Effective.Theorem7ArrowRecursive`, which is untouched and open |
| 4 | the old form was trivially satisfiable | `ScottDomains.R45.Agent1.preservesRecursivePresentation_id`, retargeted to the name kept here |

Row 3 is the one that matters. The old docstring asserted "`Theorem7ArrowRecursive`
is this schema's instance at `γ = D → E`, universally quantified"; with a free
carrier that sentence could not be stated, still less proved, because the schema
had no way to say that the carrier is the operator's value at `α` and `β`. It is
now a theorem, at a single universe.

## What the schema is discharged at, and what it is open at

| # | Operator | Status |
| -- | ------- | ------ |
| 1 | `fstOp`, `(D, E) ↦ D` | discharged — and this is the honest home of the one-line proof that used to discharge the whole claim |
| 2 | `sndOp`, `(D, E) ↦ E` | discharged |
| 3 | `constOp C` for `C` carrying a recursive presentation | discharged; `ScottDomains.R45.Agent1.natBotRecursivePresentation` supplies such a `C` |
| 4 | `arrowOp`, `(D, E) ↦ D → E` | **open**, and exactly as open as `Effective.Theorem7ArrowRecursive` — row 3 above |
| 5 | `⊸`, `×`, `+`, `⊕`, `⊗`, the powerdomains | not stated; each needs its `Domain` instance packaged as a `DomainOperator`, which is mechanical, and then a proof, which is not |

Rows 1–3 are true instances of the schema, not vacuities: the projections and the
constant operators do preserve recursive presentability. The difference from the
old form is that they no longer *discharge the claim* — the claim is now a
predicate on the operator, so proving it at `fstOp` says something about `fstOp`
and nothing about `· → ·`.
-/

namespace ScottDomains.R47.Agent3

open ScottDomains.Effective

universe u

section FreeCarrier

variable {α β : Type*} [CompletePartialOrder α] [Domain α]
  [CompletePartialOrder β] [Domain β]

/-- **`Effective.PreservesRecursivePresentation` as it stood through r0046**, kept
verbatim so the restatement r0047 made is auditable against the thing it replaced
rather than against a paraphrase.

Its carrier `γ` is a parameter unrelated to `α` and `β`, and its conclusion
mentions neither `d` nor `e`. So the claim is satisfied by choosing `γ`:
`ScottDomains.R45.Agent1.preservesRecursivePresentation_id` takes `γ := α` and
returns its own hypothesis. No `Classical.dec` is involved — the vacuity is in
the quantifier structure, not in a field type, which is the second mechanism
`docs/StructuresVsTypeClassesVsPropsInLean4.md` records.

**Not a claim of the paper.** No sentence of Gunter & Scott asserts this, and it
must not be counted as an open result; it must not be added to
`scripts/a6-claims.txt`. It is kept for two purposes: citation, and as the
**positive control** for r0047's sweep for this vacuity mechanism — an instrument
that cannot flag the one known instance is not measuring anything. -/
def PreservesRecursivePresentationFreeCarrier (γ : Type*) [CompletePartialOrder γ]
    [Domain γ] (d : EffectivePresentation α) (e : EffectivePresentation β) : Prop :=
  IsRecursive d → IsRecursive e → ∃ f : EffectivePresentation γ, IsRecursive f

end FreeCarrier

/-- **The restatement is a strengthening.**

The kernel checks here that the post-r0047 statement implies the pre-r0047 one at
every carrier the operator actually produces, which is the direction that fixes
what changed: the carrier stopped being a free parameter and became the
operator's value at the arguments.

The converse fails, which is the point: the old form is provable at `γ := α`
(row 4 of the table above) while the new form at `arrowOp` is
`Effective.Theorem7ArrowRecursive`, open. So nothing the paper asserts has been
given up and something it asserts has been recovered. -/
theorem freeCarrier_of_preservesRecursivePresentation {F : DomainOperator.{u}}
    (h : Effective.PreservesRecursivePresentation F) {D E : Dom.{u}}
    (hDE : F.Defined D E) (d : EffectivePresentation D.carrier)
    (e : EffectivePresentation E.carrier) :
    PreservesRecursivePresentationFreeCarrier (F.obj D E hDE).carrier d e :=
  fun hd he => h D E hDE d e hd he

/-! ## The operators the schema is discharged at -/

/-- The first projection preserves recursive presentability, by returning the
presentation it was given. This is the one-line proof that used to discharge the
whole schema; stated about `fstOp` it is a true and unremarkable fact about the
first projection. -/
theorem preservesRecursivePresentation_fstOp :
    Effective.PreservesRecursivePresentation fstOp.{u} :=
  fun _ _ _ d _ hd _ => ⟨d, hd⟩

/-- The second projection preserves recursive presentability. -/
theorem preservesRecursivePresentation_sndOp :
    Effective.PreservesRecursivePresentation sndOp.{u} :=
  fun _ _ _ _ e _ he => ⟨e, he⟩

/-- A constant operator preserves recursive presentability exactly when its value
does, and the hypothesis here is that value's own recursive presentation.
`ScottDomains.R45.Agent1.isRecursive_natBot` supplies one at `N⊥`, so the schema
is discharged at a constant operator and not only at the projections. -/
theorem preservesRecursivePresentation_constOp {C : Dom.{u}}
    (f : EffectivePresentation C.carrier) (hf : IsRecursive f) :
    Effective.PreservesRecursivePresentation (constOp C) :=
  fun _ _ _ _ _ _ _ => ⟨f, hf⟩

/-! ## The arrow operator, and Theorem 7's second sentence -/

/-- **`· → ·` as a `DomainOperator`.** Defined where `E` is bounded complete,
which is Theorem 7's own hypothesis and what
`ScottHom.isBoundedCompleteDomain_scottHom` needs; the value's structure is the
`CompletePartialOrder` of `ScottHom.lean` and the `Domain` instance of
`FunctionSpaceCountable.lean`. -/
noncomputable def arrowOp : DomainOperator.{u} where
  Defined _ E := BoundedComplete E.carrier
  obj D E h :=
    haveI := h
    { carrier := ScottHom D.carrier E.carrier
      str := inferInstance
      isDomain := inferInstance }

/-- **The restated schema at the arrow operator is exactly Theorem 7's second
sentence at recursion-theoretic strength**, at a single universe.

This is the sentence the pre-r0047 docstring asserted and could not state: with a
free carrier there was no way to say that the carrier is `D → E`. Both directions
are one step — the bundling `Dom` performs is the only difference between the two
statements — which is the evidence that the restatement changed the quantifier
structure and nothing else.

Universes: `Effective.Theorem7ArrowRecursive` is polymorphic in the two carriers
separately, `Dom.{u}` fixes one universe, so the equivalence is stated at
`u = v`. The `→` direction therefore does not recover the mixed-universe
instances of `Theorem7ArrowRecursive`; nothing in the development uses them. -/
theorem preservesRecursivePresentation_arrowOp_iff :
    Effective.PreservesRecursivePresentation arrowOp.{u} ↔
      Effective.Theorem7ArrowRecursive.{u, u} := by
  constructor
  · intro h α β _ _ _ _ hbc d e hd he
    exact h ⟨α, inferInstance, inferInstance⟩ ⟨β, inferInstance, inferInstance⟩ hbc d e hd he
  · intro h D E hDE d e hd he
    haveI : BoundedComplete E.carrier := hDE
    exact h d e hd he

end ScottDomains.R47.Agent3
