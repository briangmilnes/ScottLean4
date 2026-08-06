import ScottDomains.FunctionSpaceDomain

/-!
# Every compact function is a finite join of step functions

The structure theorem behind the remaining conjunct of Gunter & Scott's
Theorem 7. The paper asserts that the step functions "form a basis for `D → E`";
`FunctionSpaceDomain.lean` proved the least-upper-bound half of that, and this
file proves the finiteness half — that a *compact* element of `D → E` is the join
of finitely many step functions.

Countability of `K(D → E)` follows, because such a join is named by a finite
subset of `K(D) × K(E)` and finite subsets of a countable set are countable.

## The argument

Write `finiteJoinsBelow f` for the elements that are a least upper bound of some
finite set of step functions below `f`. It is nonempty (`⊥` is the join of the
empty set), directed (the union of two finite subsets is finite and bounded by
`f`, so it has a join by `BoundedComplete (ScottHom α β)`), everything in it is
below `f`, and its least upper bound is `f` — the last by the argument of
`isLUB_compactsBelow_scottHom`, since every single step function below `f` is
already the join of a one-element set.

A compact `g` applied to this directed set therefore lands below some
`J ∈ finiteJoinsBelow g`, and `J ≤ g`, so `g = J`.

Note what this does **not** require: that a finite join of compact elements is
compact. That would be an induction over the finite set using
`isCompactElement_of_isLUB_pair`. It is unnecessary, because `J` turns out to
*be* `g`.
-/

namespace ScottDomains

namespace ScottHom

variable {α β : Type*}

section Steps

variable [PartialOrder α] [CompletePartialOrder β]

/-- The step functions with compact value lying below `f`. -/
def stepsBelow (f : ScottHom α β) : Set (ScottHom α β) :=
  {g | (∃ (k : α) (hk : IsCompactElement k) (e : β), IsCompactElement e ∧ g = step hk e) ∧ g ≤ f}

theorem le_of_mem_stepsBelow {f g : ScottHom α β} (h : g ∈ stepsBelow f) : g ≤ f := h.2

/-- The elements that are a least upper bound of a *finite* set of step functions
below `f`. -/
def finiteJoinsBelow (f : ScottHom α β) : Set (ScottHom α β) :=
  {g | ∃ S : Set (ScottHom α β), S.Finite ∧ S ⊆ stepsBelow f ∧ IsLUB S g}

/-- A finite join of step functions below `f` is itself below `f`, because `f`
bounds the set it is the least upper bound of. -/
theorem le_of_mem_finiteJoinsBelow {f g : ScottHom α β} (h : g ∈ finiteJoinsBelow f) :
    g ≤ f := by
  obtain ⟨S, _, hsub, hlub⟩ := h
  exact hlub.2 fun h hh => le_of_mem_stepsBelow (hsub hh)

/-- `⊥` is the join of the empty set of step functions, so the set of finite
joins is never empty. -/
theorem bot_mem_finiteJoinsBelow (f : ScottHom α β) : (⊥ : ScottHom α β) ∈ finiteJoinsBelow f :=
  ⟨∅, Set.finite_empty, Set.empty_subset _, isLUB_empty⟩

theorem finiteJoinsBelow_nonempty (f : ScottHom α β) : (finiteJoinsBelow f).Nonempty :=
  ⟨⊥, bot_mem_finiteJoinsBelow f⟩

end Steps

section Directed

variable [PartialOrder α] [CompletePartialOrder β] [BoundedComplete β]

/-- The finite joins below `f` are directed: the union of two finite subsets of
`stepsBelow f` is finite and bounded by `f`, so it has a least upper bound, which
dominates both joins. -/
theorem directedOn_finiteJoinsBelow (f : ScottHom α β) :
    DirectedOn (· ≤ ·) (finiteJoinsBelow f) := by
  rintro g₁ ⟨S₁, hfin₁, hsub₁, hlub₁⟩ g₂ ⟨S₂, hfin₂, hsub₂, hlub₂⟩
  have hbdd : BddAbove (S₁ ∪ S₂) := by
    refine ⟨f, ?_⟩
    rintro h (h₁ | h₂)
    · exact le_of_mem_stepsBelow (hsub₁ h₁)
    · exact le_of_mem_stepsBelow (hsub₂ h₂)
  have hlub := isLUB_sSup_of_bddAbove hbdd
  refine ⟨sSup (S₁ ∪ S₂),
    ⟨S₁ ∪ S₂, hfin₁.union hfin₂, Set.union_subset hsub₁ hsub₂, hlub⟩, ?_, ?_⟩
  · exact hlub₁.2 fun h hh => hlub.1 (Set.mem_union_left _ hh)
  · exact hlub₂.2 fun h hh => hlub.1 (Set.mem_union_right _ hh)

end Directed

section Structure

variable [CompletePartialOrder α] [IsAlgebraic α]
variable [CompletePartialOrder β] [IsAlgebraic β]

/-- `f` is the least upper bound of the finite joins of step functions below it.
Needs only algebraicity of both, not bounded completeness — the same split of
hypotheses that `FunctionSpaceDomain.lean` records.
The single step functions alone force this — the same argument as
`isLUB_compactsBelow_scottHom`, with `{step k e}` as the finite set. -/
theorem isLUB_finiteJoinsBelow (f : ScottHom α β) : IsLUB (finiteJoinsBelow f) f := by
  refine ⟨fun _ hg => le_of_mem_finiteJoinsBelow hg, ?_⟩
  intro u hu x
  dsimp only
  refine (IsAlgebraic.isLUB_compactsBelow (f x)).2 ?_
  rintro e ⟨he, hef⟩
  have hdir := IsAlgebraic.directedOn_compactsBelow (α := α) x
  have hfx : IsLUB (⇑f '' compactsBelow x) (f x) :=
    f.scottContinuous (compactsBelow_nonempty x) hdir (IsAlgebraic.isLUB_compactsBelow x)
  obtain ⟨_, ⟨k, hk, rfl⟩, hek⟩ :=
    he (⇑f '' compactsBelow x) (f x) ((compactsBelow_nonempty x).image _)
      (directedOn_image f hdir) hfx hef
  have hmem : step hk.1 e ∈ finiteJoinsBelow f := by
    refine ⟨{step hk.1 e}, Set.finite_singleton _, ?_, isLUB_singleton⟩
    rintro g rfl
    exact ⟨⟨k, hk.1, e, he, rfl⟩, (step_le_iff hk.1).mpr hek⟩
  have hle := hu hmem x
  dsimp only at hle
  rwa [coe_step, stepFun_of_le hk.2] at hle

variable [BoundedComplete β]

/-- **Every compact function is a finite join of step functions.**

Applying compactness of `g` to the directed set `finiteJoinsBelow g`, whose least
upper bound is `g`, produces a finite join `J` above `g`; and `J ≤ g`, so `g` *is*
that finite join. -/
theorem exists_finite_isLUB_of_isCompactElement {g : ScottHom α β}
    (hg : IsCompactElement g) :
    ∃ S : Set (ScottHom α β), S.Finite ∧ S ⊆ stepsBelow g ∧ IsLUB S g := by
  obtain ⟨J, hJ, hgJ⟩ :=
    hg (finiteJoinsBelow g) g (finiteJoinsBelow_nonempty g)
      (directedOn_finiteJoinsBelow g) (isLUB_finiteJoinsBelow g) le_rfl
  obtain ⟨S, hfin, hsub, hlub⟩ := hJ
  have hJg : J = g := le_antisymm (le_of_mem_finiteJoinsBelow ⟨S, hfin, hsub, hlub⟩) hgJ
  exact ⟨S, hfin, hsub, hJg ▸ hlub⟩

end Structure

end ScottHom

end ScottDomains
