import ScottDomains.NormalSubposet
import ScottDomains.ScottHom

/-!
# §3.2: effectively presented domains

Gunter & Scott, *Semantic Domains*, §3.2:

> **Definition:** Let `D` be a domain and suppose `d : ℕ → K(D)` is a surjection.
> Then `d` is an **effective presentation** of `D` if
> 1. the set `{(m, n) | dₘ ⊑ dₙ}` is effectively decidable, and
> 2. for any finite set `u ⊆ ℕ`, it is decidable whether `{dₙ | n ∈ u} ◁ K(D)`.

> If `⟨D, d⟩` and `⟨E, e⟩` are effectively presented domains, then a continuous
> function `f : D → E` is said to be **computable** (with respect to `d` and `e`)
> if and only if, for every `n ∈ ℕ`, the set `{m | eₘ ⊑ f(dₙ)}` is recursively
> enumerable.

## Reading "effectively decidable" as `Decidable`

A `Decidable` instance in Lean *is* a program that decides the proposition, so
`DecidablePred` is a faithful rendering of the paper's "effectively decidable"
for these two conditions. It is not the same as Mathlib's `ComputablePred`, which
additionally ties the decision procedure to a recursion-theoretic model; nothing
in the paper's use of conditions 1 and 2 needs that stronger reading, and the
weaker one is what makes the definition usable.

Both conditions live on `ℕ` and `Finset ℕ` — the *indices* — rather than on the
domain, which is the point of a presentation: it moves decidability questions
onto a countable index set where they can be asked at all.

## The computable function (r0031)

An earlier version of this docstring said the paper's **computable function**
could not be stated because "this Mathlib (v4.32.2) has no `RePred` or equivalent
under a ready name — a grep across the whole library finds no definition of r.e.
predicates". **That was wrong, and the error was the grep's capitalization.**
Mathlib spells it `REPred`, at `Mathlib/Computability/RE.lean:157`:
`REPred p := Partrec fun a => Part.assert (p a) fun _ => Part.some ()`, the domain
of a partial recursive function. `ComputablePred` sits beside it.

The definition is now in `ScottDomains/ComputableFunction.lean` (r0031). One
consequence for *this* structure, recorded here because it constrains callers:
`decidableLE` is too weak to prove anything computable, since a Lean `Decidable`
instance may be `Classical.dec`. A computability result needs a *recursiveness*
hypothesis on the enumeration — `RecursiveLE` in `ComputableFunction.lean` — and
whether that should instead become a field of this structure is an open decision.
-/

namespace ScottDomains

variable {α : Type*} [CompletePartialOrder α]

/-- An **effective presentation** of a domain: a surjective enumeration of the
basis whose order relation is decidable and whose finite normal subposets are
recognizable. -/
structure EffectivePresentation (α : Type*) [CompletePartialOrder α] [Domain α] where
  /-- The enumeration of the basis. -/
  enum : ℕ → α
  /-- Its values are compact. -/
  enum_mem_compacts : ∀ n, IsCompactElement (enum n)
  /-- It exhausts the basis. -/
  enum_surjective : ∀ k, IsCompactElement k → ∃ n, enum n = k
  /-- Condition 1: the ordering on the basis is decidable, read off the indices. -/
  decidableLE : DecidablePred fun p : ℕ × ℕ => enum p.1 ≤ enum p.2
  /-- Condition 2: it is decidable whether a finite set of basis elements is a
  normal subposet of `K(D)`. -/
  decidableNormal : DecidablePred fun u : Finset ℕ => (enum '' (↑u : Set ℕ)) ◁ compacts α

namespace EffectivePresentation

variable [Domain α] (d : EffectivePresentation α)

/-- The enumeration lands in `K(D)`. -/
theorem enum_mem (n : ℕ) : d.enum n ∈ compacts α := d.enum_mem_compacts n

/-- The enumeration's range is exactly the basis — the surjectivity condition,
stated as a set equality. -/
theorem range_enum : Set.range d.enum = compacts α := by
  ext k
  constructor
  · rintro ⟨n, rfl⟩
    exact d.enum_mem_compacts n
  · intro hk
    exact d.enum_surjective k hk

include d in
/-- A domain with an effective presentation has a countable basis — which the
`Domain` class already required, so this is a consistency check on the
definition rather than new information.

`include d` is needed because the conclusion does not mention `d`, so Lean's
automatic section-variable inclusion would otherwise drop it. -/
theorem countable_compacts : (compacts α).Countable := by
  rw [← d.range_enum]
  exact Set.countable_range d.enum

end EffectivePresentation

end ScottDomains
