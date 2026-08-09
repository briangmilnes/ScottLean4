# `structure`, `class`, and `Prop` in Lean 4

Three ways to package a collection of data and laws. They are easy to confuse
because two of them are *the same construct* and the third is a *universe*, not a
construct at all. This note separates them, gives the decision rule, and works
through the cases in this development — including the one where choosing wrongly
made two theorems say nothing.

## The short answer

| # | Question | Answer |
| -- | ------- | ------ |
| 1 | `structure` vs `class`? | **Is the value unique per type, and should Lean find it for you?** If yes, `class`. If there are many and the caller picks, `structure`. |
| 2 | `Prop` vs `Type`? | **Does the value carry information you will compute with?** If yes, `Type`. If it is only a claim, `Prop`. |

Question 1 is about *inference*. Question 2 is about *content*. They are
independent, which is why all four combinations occur — and all four occur in
this package.

## `class` is a `structure`

This is the fact that dissolves most of the confusion. In Lean 4,

    class Foo (α : Type) where
      bar : α → α

elaborates to the same inductive type as `structure Foo`, with the same
constructor and the same projections. The `class` keyword adds exactly one thing:
the type is registered for **typeclass resolution**, so a `[Foo α]` binder is
filled by an automatic search over declared `instance`s rather than by the caller
passing a value.

Consequences worth stating plainly:

* Anything you can do with a `structure` you can do with a `class`. There is no
  expressive difference.
* The cost of `class` is that resolution is a **search**. It must find a *unique*
  answer, so declaring two instances for the same type is a defect — resolution
  picks by priority and declaration order, not by what you meant.
* The cost of `structure` is that every use site names the value explicitly.

So the choice is not about power. It is about whether "the `Foo` for `α`" is a
well-posed phrase.

### Where this development draws the line

    class Domain (α : Type*) [CompletePartialOrder α] : Prop extends IsAlgebraic α

    structure ScottHom (α β : Type*) [Preorder α] [Preorder β] where
      toFun : α → β
      scottContinuous' : ScottContinuous toFun

`Domain` is a `class` because a type either is an algebraic cpo with a countable
basis or it is not — "the `Domain` structure on `α`" is well-posed, and we want
`[Domain α]` inferred everywhere.

`ScottHom` is a `structure` because there are **many** Scott-continuous functions
from `α` to `β`. Making it a class would ask resolution to find *the* continuous
function between two domains, which is not a question with an answer. Morphisms
are bundled data the caller supplies; properties of a type are inferred.

That is the rule in one line: **`class` for properties of a type, `structure` for
values of a type.**

## `Prop` is a universe, not a construct

`Prop` is `Sort 0`, the universe of propositions. A `structure` or `class` may
live in it:

    class IsAlgebraic (α : Type*) [CompletePartialOrder α] : Prop where …

What changes when it does:

| # | Property | `Type u` | `Prop` |
| -- | ------- | -------- | ------ |
| 1 | Proof irrelevance | no — `a b : Nat` may differ | **yes** — any two proofs of `p : Prop` are *definitionally* equal |
| 2 | Erased at compile time | no | **yes** — no runtime representation |
| 3 | Eliminate into `Type` | yes | **no**, except for subsingleton eliminators — and `Classical.choice` |
| 4 | Uniqueness of instances | must be arranged | **free**, by row 1 |

Row 1 is why `Prop`-valued classes are safe to be liberal with: two `Domain α`
instances cannot disagree, because they cannot differ at all. A diamond in a
`Prop`-valued hierarchy is harmless. A diamond in a `Type`-valued one is a real
bug, because the two paths can carry different data.

Row 3 is the barrier that `Classical.choice` breaks — `Nonempty α → α` takes a
`Prop` and returns data. That is the whole content of the axiom, and
`docs/AxiomFootprint.md` traces what it costs.

## The four combinations, with this package's examples

| # | Kind | Example here | Why |
| -- | ---- | ------------ | --- |
| 1 | `class` in `Prop` | `IsAlgebraic`, `Domain`, `IsSemilattice` | a **law** the type either satisfies or not; inferred; unique for free |
| 2 | `class` in `Type` | `Binop` (the `⋓` operation), `CompletePartialOrder` | **operations and data** attached to a type, inferred; uniqueness must be arranged |
| 3 | `structure` in `Type` | `ScottHom`, `EffectivePresentation` | a **value** with many inhabitants; the caller chooses |
| 4 | `structure`/`def` in `Prop` | `RecursiveLE` | a **claim about a given value**, not about a type, so nothing to infer from |

### The mixin pattern, row 1 against row 2

`ContinuousAlgebra.lean` shows the Mathlib convention exactly:

    class Binop (E : Type u) [CompletePartialOrder E] where …          -- data: ⋓

    class IsSemilattice (E : Type u) [CompletePartialOrder E] [Binop E] : Prop where
      op_assoc : ∀ r s t : E, (r ⋓ s) ⋓ t = r ⋓ (s ⋓ t)
      op_comm  : ∀ s t : E, s ⋓ t = t ⋓ s
      op_idem  : ∀ s : E, s ⋓ s = s

**Operations go in a `Type`-valued class; laws go in a separate `Prop`-valued
class that takes the operation class as a parameter.** The reasons are practical:

* A type may carry one operation satisfying several law-sets. Splitting lets you
  add `IsUpper` or `IsLower` without redefining `⋓`.
* The law class is proof-irrelevant, so it never causes a diamond.
* You can state a theorem needing only associativity without dragging in the rest.

Combining them into one `Type`-valued class with law fields would work and is
what a beginner writes. It fails at the third bullet, and at scale it produces
the diamond problems Mathlib's hierarchy is designed to avoid.

## `extends`, and what it actually does

    class Domain (α : Type*) [CompletePartialOrder α] : Prop extends IsAlgebraic α

    structure RecursivePresentation (γ : Type*) [CompletePartialOrder γ] [Domain γ]
        extends EffectivePresentation γ where
      recursiveLE : RecursiveLE toEffectivePresentation
      recursiveNormal : RecursiveNormal toEffectivePresentation

`extends` adds the parent as a field named `toParent`, and generates a projection
`RecursivePresentation.toEffectivePresentation`. Two consequences:

1. **The parent is available as a value**, which is why `recursiveLE` can be
   stated as `RecursiveLE toEffectivePresentation` — the new fields are
   predicates *about the inherited record*, not new data.
2. For a `class`, Lean also registers an instance `[Child α] → [Parent α]`, so
   `[Domain α]` satisfies any `[IsAlgebraic α]` binder automatically. This is
   what makes hierarchies usable, and what makes multiple inheritance a diamond
   risk in `Type` and harmless in `Prop`.

`RecursivePresentation` is the shape to imitate when you want "the same data,
plus a stronger guarantee": extend, and let the new fields talk about
`toParent`.

## Plain `def … : Prop` — the fourth option, and its hazard

Not every proposition needs a `structure`:

    def RecursiveLE (d : EffectivePresentation α) : Prop := …

Use a plain `def` returning `Prop` when the claim is **about a value you already
have**, not about a type. There is nothing to infer, so a class would be wrong;
there is one field, so a structure would be ceremony.

**The hazard:** a `Prop`-valued `def` is a *statement*, and stating is not
proving. It produces no `sorry`, no warning, and no build signal. The package
reports `sorry` 0 while `StepFunctionsDecidable` sits in it undischarged. `sorry`
counts holes in proofs; it cannot count a claim nobody attempted. If you write
one, either discharge it or record it where a count will find it.

## The mistake this development actually made

The sharpest illustration of why row 2 of the short answer matters.

`EffectivePresentation` is a `structure` in `Type`, and among its fields are two
carrying **decidability**:

    structure EffectivePresentation (α : Type*) [CompletePartialOrder α] [Domain α] where
      enum : ℕ → α
      enum_mem_compacts : ∀ n, IsCompactElement (enum n)
      enum_surjective : ∀ k, IsCompactElement k → ∃ n, enum n = k
      decidableLE : DecidablePred fun p : ℕ × ℕ => enum p.1 ≤ enum p.2
      decidableNormal : DecidablePred fun u : Finset ℕ => (enum '' ↑u) ◁ compacts α

`Decidable p` is **data** — it is an algorithm that decides `p`, living in
`Type`. That looks like exactly the right encoding for an *effective*
presentation. It is not, because of one fact:

    Classical.dec : (p : Prop) → Decidable p

`Classical.dec` produces a `Decidable` instance for **any** proposition, at no
cost, from the axiom of choice. So the two decidability fields can always be
filled classically, and `Effective.nonempty_effectivePresentation` proves that
*every* domain has an `EffectivePresentation`. The structure is vacuous.

The damage is not theoretical: two of the Theorem 7 rows that r0043 labelled
`S+P` — the development's strongest label — are proved through it with their
hypotheses unused. They are true, checked by the kernel, and establish nothing.

**The fix is to pick a predicate that is not free.** `Decidable` is data but
classically free; `ComputablePred` is a `Prop` with genuine content:

    ComputablePred p ↔ ∃ (_ : DecidablePred p), Computable fun a => decide (p a)

The `Computable` conjunct is not obtainable from `Classical.choice`.
`RecursivePresentation` above is the non-vacuous form, and it is deliberately
uninstantiated — an honest empty set rather than a full one that means nothing.

**The general lesson, which is not about Lean:** the question to ask of a
`structure` is not "does it have the right fields" but **"is it inhabited for
things that should not inhabit it."** A specification everything satisfies is not
a specification. Neither the type checker nor `#print axioms` will tell you —
both report success.

### A second mechanism, which has nothing to do with `Classical.dec`

r0045 found a vacuity that a reviewer following only the advice above would pass.
`Effective.PreservesRecursivePresentation` quantifies over a type `γ` that is
**unrelated to the `α` and `β` the claim is about**, so

    preservesRecursivePresentation_id : PreservesRecursivePresentation α d e

closes it in one line by returning its own hypothesis. Its closure over `γ` is
false by a counting argument, so the row is not merely weak — it is stated wrong.

The vacuity here lives in the **quantifier structure, not in a field type**. No
field is `Decidable`; nothing is filled by `Classical.dec`. Checking for the
first mechanism finds nothing.

So the check is two questions, not one:

| # | Ask | Catches |
| -- | --- | ------- |
| 1 | is any field freely inhabitable (`Decidable`, or anything `Classical.*` yields)? | the `EffectivePresentation` mechanism |
| 2 | is every bound variable actually *constrained* by the claim, or can one be instantiated to make the statement trivial? | the `PreservesRecursivePresentation` mechanism |

Question 2 generalizes: a hypothesis that is also the conclusion, at parameters
the claim never relates, is an identity function wearing a theorem's name.

## Cost

| # | Construct | Elaboration cost | Runtime cost |
| -- | -------- | ---------------- | ------------ |
| 1 | `structure` | none beyond the record | fields are real |
| 2 | `class` | a resolution **search** per binder; deep hierarchies dominate compile time | same as `structure` |
| 3 | anything in `Prop` | same as its `Type` counterpart | **zero** — erased |

Row 2 is the one that bites at scale. Each `[Foo α]` binder starts a search whose
cost grows with the instance graph, and Mathlib's graph is large. When a file
compiles slowly, an over-classed hierarchy is a standard cause; converting a
class the caller could just as well pass explicitly into a `structure` is a
standard fix.

## Checklist

| # | If … | then |
| -- | ---- | ---- |
| 1 | many inhabitants, caller chooses | `structure` |
| 2 | at most one per type, want it inferred | `class` |
| 3 | it is only a claim, no data to compute with | put it in `Prop` |
| 4 | laws over an existing operation | `Prop`-valued class taking the data class as a parameter |
| 5 | a claim about a *value* rather than a type | plain `def … : Prop` — and discharge it |
| 6 | "same data plus a stronger guarantee" | `extends`, with new fields predicating on `toParent` |
| 7 | a field is a `Decidable`, or anything `Classical.*` yields free | **stop** — check the structure is not inhabited for everything |
