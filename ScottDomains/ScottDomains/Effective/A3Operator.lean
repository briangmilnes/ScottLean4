import ScottDomains.Domain

/-!
# r0047, agent3: an operator on domains, as a value

`Effective.PreservesRecursivePresentation` renders §3.2's closing sentence
(Gunter & Scott, *Semantic Domains*, printed p. 12):

> In the remaining sections of the chapter we will discuss a great many operators
> like `· → ·` and `· ⊸ ·`. We will leave it to the reader to convince himself
> that all of these operators preserve the property of having an effective
> presentation.

The sentence quantifies over **operators**. Through r0046 the `def` quantified
instead over a carrier `γ` unrelated to the `α` and `β` it was stated about, and
a claim whose carrier is a free parameter is discharged by choosing the carrier:
`ScottDomains.R45.Agent1.preservesRecursivePresentation_id` closed it in one line
at `γ := α` by returning its own hypothesis. The defect is that the rendering
lost the dependence of the operator's value on its arguments, which is the entire
content of "preserve".

This file supplies the missing vehicle: an operator as a **value**, so that
"`F` preserves recursive presentability" is a predicate on `F` and cannot be
satisfied by picking a convenient carrier.

## Why the carrier has to be bundled

`ScottHom α β` takes the order structures of `α` and `β` as instance arguments,
so an operator is not a function `Type → Type → Type`. Two shapes were available:

| # | Shape | Why not / why |
| -- | ---- | ------------- |
| 1 | a type family with the value's `CompletePartialOrder` bound universally in the claim | rejected: `CompletePartialOrder` is `Type`-valued, so quantifying over it asks for a presentation with respect to *every* order structure on the carrier — a strengthening by artifact, which is r0044's dominant defect mode running in reverse |
| 2 | the operator **supplies** the value's structure | taken here: `Dom` bundles a carrier with its structure, `DomainOperator.obj` returns a `Dom` |

`ScottDomains.Cpo` (`UniversalDomain.lean`) is the same construction one class
lower — a carrier with its `CompletePartialOrder` — and is the precedent for
`attribute [instance]` on the projection. `Dom` is not defined as an extension of
it because `UniversalDomain.lean` sits far downstream of `Effective/`.

## Partiality is a field, not an omission

Most operators of §§4–7 are defined under a side condition: `D → E` is a domain
only when `E` is bounded complete (`Theorem 7`, and
`ScottHom.isBoundedCompleteDomain_scottHom` is where this development gets it).
`DomainOperator.Defined` records that condition, so the arrow *is* expressible as
a `DomainOperator` and `Effective.Theorem7ArrowRecursive` becomes a theorem about
one — see `Effective/A3FreeCarrier.lean`, where the two are proved equivalent at
a single universe.
-/

namespace ScottDomains.R47.Agent3

universe u

/-- A domain as a value: a carrier, its complete-partial-order structure, and the
`Domain` law. `ScottDomains.Cpo` is the same bundling without the last field. -/
structure Dom : Type (u + 1) where
  /-- The underlying type. -/
  carrier : Type u
  /-- Its complete-partial-order structure. -/
  str : CompletePartialOrder carrier
  /-- It is algebraic with a countable basis. -/
  isDomain : @Domain carrier str

attribute [instance] Dom.str Dom.isDomain

/-- **An operator on domains, as a value.** `obj` takes two domains to a domain,
on the sub-collection `Defined` where the operator is defined.

`Defined` is not bookkeeping. `· → ·` is a `DomainOperator` with
`Defined D E := BoundedComplete E.carrier`; without the field the arrow would not
be expressible, and §3.2's sentence is about the arrow above all. -/
structure DomainOperator : Type (u + 1) where
  /-- The pairs of domains at which the operator is defined. -/
  Defined : Dom.{u} → Dom.{u} → Prop
  /-- The operator's value. -/
  obj : (D E : Dom.{u}) → Defined D E → Dom.{u}

/-- The first projection `(D, E) ↦ D`, everywhere defined. -/
def fstOp : DomainOperator.{u} where
  Defined _ _ := True
  obj D _ _ := D

/-- The second projection `(D, E) ↦ E`, everywhere defined. -/
def sndOp : DomainOperator.{u} where
  Defined _ _ := True
  obj _ E _ := E

/-- The constant operator `(D, E) ↦ C`, everywhere defined. -/
def constOp (C : Dom.{u}) : DomainOperator.{u} where
  Defined _ _ := True
  obj _ _ _ := C

end ScottDomains.R47.Agent3
