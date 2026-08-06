import ScottDomains.CompactFunction

/-!
# `K(D → E)` is countable, and Theorem 7

The last conjunct of Gunter & Scott's Theorem 7:

> **Theorem 7** If `D` and `E` are bounded complete domains, then `D → E` is also
> a bounded complete domain.

`Domain` carries the paper's countable-basis condition, so the theorem needs
`K(D → E)` countable as well as algebraic. `CompactFunction.lean` supplies the
structural fact: a compact function is the join of *finitely many* step
functions. Each step function is named by a pair in `K(D) × K(E)`, so a compact
function is named by a finite subset of a countable set — and those form a
countable family (`Set.countable_setOf_finite_subset`, the same lemma `P N` used).

## The naming map

`ofPairs P` is the join of the step functions named by `P`. It is **total**: the
supremum on `ScottHom` is total, so `ofPairs` needs no hypothesis on `P` and no
proof term inside it. Junk values for bad `P` are harmless, because the argument
only ever needs `K(D → E) ⊆ range ofPairs` — an inclusion, not a bijection.

Going the other way, `stepPairOf g` chooses a pair naming `g` when one exists.
Choosing matters: without it, the set of *all* pairs naming a step function can
be infinite — every `k` names the constant-`⊥` function — and finiteness would be
lost.

## The hypotheses are weaker than the paper's

The paper assumes `D` and `E` are bounded complete domains. This formalization
never uses bounded completeness of `D`: the function space is a cpo for any
preordered `D`, algebraic for `D` algebraic, and bounded complete because `E` is.
`D` need only be a domain. See `isBoundedCompleteDomain_scottHom` below.
-/

namespace ScottDomains

namespace ScottHom

variable {α β : Type*}

section Naming

variable [CompletePartialOrder α] [CompletePartialOrder β]

/-- The step functions named by a set of pairs. -/
def stepsOf (P : Set (α × β)) : Set (ScottHom α β) := {g | ∃ p ∈ P, IsStepPair g p}

/-- The join of the step functions named by `P`. Total, because `sSup` on
`ScottHom` is. -/
noncomputable def ofPairs (P : Set (α × β)) : ScottHom α β := sSup (stepsOf P)

open Classical in
/-- A chosen pair naming `g`. The choice is what keeps the naming set finite:
the set of *all* pairs naming a given step function can be infinite — every `k`
names the constant-`⊥` function. -/
noncomputable def stepPairOf (g : ScottHom α β) : α × β :=
  if h : ∃ p, IsStepPair g p then h.choose else (⊥, ⊥)

theorem isStepPair_stepPairOf {g : ScottHom α β} (h : ∃ p, IsStepPair g p) :
    IsStepPair g (stepPairOf g) := by
  classical
  have hchoose : stepPairOf g = h.choose := by simp only [stepPairOf, dif_pos h]
  rw [hchoose]
  exact h.choose_spec

/-- Naming a set of step functions and reading it back is the identity. The
forward inclusion is where `IsStepPair` being stated through the coercion pays:
two step functions with the same chosen pair have the same underlying function,
hence are equal. -/
theorem stepsOf_image_stepPairOf {S : Set (ScottHom α β)}
    (hS : ∀ g ∈ S, ∃ p, IsStepPair g p) : stepsOf (stepPairOf '' S) = S := by
  ext g
  constructor
  · rintro ⟨_, ⟨h, hh, rfl⟩, hgp⟩
    have hh' := isStepPair_stepPairOf (hS h hh)
    have hgh : g = h := DFunLike.coe_injective (by rw [hgp.2.2, hh'.2.2])
    rw [hgh]
    exact hh
  · intro hg
    exact ⟨stepPairOf g, ⟨g, hg, rfl⟩, isStepPair_stepPairOf (hS g hg)⟩

end Naming

section Countable

variable [CompletePartialOrder α] [IsAlgebraic α]
variable [CompletePartialOrder β] [IsAlgebraic β] [BoundedComplete β]

/-- Every compact function is `ofPairs P` for a finite set `P` of compact pairs. -/
theorem exists_ofPairs_of_isCompactElement {g : ScottHom α β} (hg : IsCompactElement g) :
    ∃ P : Set (α × β), P.Finite ∧ P ⊆ compacts α ×ˢ compacts β ∧ g = ofPairs P := by
  obtain ⟨S, hfin, hsub, hlub⟩ := exists_finite_isLUB_of_isCompactElement hg
  refine ⟨stepPairOf '' S, hfin.image _, ?_, ?_⟩
  · rintro _ ⟨h, hh, rfl⟩
    have hp := isStepPair_stepPairOf (hsub hh).1
    exact ⟨hp.1, hp.2.1⟩
  · rw [ofPairs, stepsOf_image_stepPairOf fun h hh => (hsub hh).1]
    exact hlub.unique (isLUB_sSup_of_bddAbove ⟨g, hlub.1⟩)

end Countable

section CountableBasis

variable [CompletePartialOrder α] [Domain α]
variable [CompletePartialOrder β] [Domain β] [BoundedComplete β]

/-- **`K(D → E)` is countable.** A compact function is named by a finite subset of
`K(D) × K(E)`, and the finite subsets of a countable set form a countable
family. -/
theorem countable_compacts_scottHom : (compacts (ScottHom α β)).Countable := by
  have hT : ((compacts α) ×ˢ (compacts β)).Countable :=
    (Domain.countable_compacts (α := α)).prod (Domain.countable_compacts (α := β))
  refine Set.Countable.mono ?_ ((Set.countable_setOf_finite_subset hT).image ofPairs)
  intro g hg
  obtain ⟨P, hfin, hsub, hgP⟩ := exists_ofPairs_of_isCompactElement hg
  exact ⟨P, ⟨hfin, hsub⟩, hgP.symm⟩

/-- `D → E` is a domain. -/
noncomputable instance : Domain (ScottHom α β) :=
  { (inferInstance : IsAlgebraic (ScottHom α β)) with
    countable_compacts := countable_compacts_scottHom }

/-- **Theorem 7** (Gunter & Scott, *Semantic Domains*): if `D` and `E` are bounded
complete domains, then `D → E` is a bounded complete domain.

Proved under **weaker hypotheses than the paper states**: bounded completeness of
`D` is never used. The function space is a cpo for any preordered `D`
(`ScottHom.lean`), algebraic when `D` and `E` are (`FunctionSpaceDomain.lean`),
bounded complete because `E` is (`ScottHom.lean`), and countably based because
`D` and `E` are (above). So `D` need only be a domain. -/
theorem isBoundedCompleteDomain_scottHom :
    Domain (ScottHom α β) ∧ BoundedComplete (ScottHom α β) :=
  ⟨inferInstance, inferInstance⟩

end CountableBasis

end ScottHom

end ScottDomains
