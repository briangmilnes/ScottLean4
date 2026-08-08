import ScottDomains.Section62
import ScottDomains.SFP

/-!
# r0038 audit: the duplicate pairs in the projection stack, kernel-checked

Round r0038 classified the 184 live theorems of the projection/bifinite modules
(`Projection`, `FinitaryProjection`, `NormalSubposet`, `NormalProjection`,
`Theorem6`, `FinitaryProjectionPoset`, `FinitaryProjectionEmbedding`, `Bifinite`,
`MinimalUpperBounds`, `Section62`, `SFP`). Four pairs were read as stating the
same proposition under two names. "Read as" is not evidence, so this module
converts each reading into a kernel check: **each member of a pair is proved by
applying the other one**, which the elaborator accepts only if the two statements
really do coincide up to argument order and definitional unfolding.

Nothing here is used by the development, and nothing here is a paper property.
The module exists so that a later round acting on the audit can retire one member
of each pair with the equality already checked, rather than re-deriving it.

r0028 shipped a duplicate declaration that survived 971 green builds because
`lake build` cannot see one: two proofs of the same proposition are both correct,
so neither errors. This is the cheap detector for that failure mode.

## The four pairs

| # | Declaration | Partner | Difference |
| -- | ----------- | ------- | ---------- |
| 1 | `exists_mem_upperBounds_of_directedOn` (`MinimalUpperBounds`) | `exists_upperBound_mem_of_finite` (`Skeleton/Section6`) | none — same statement, same proof script, same namespace |
| 2 | `SFP.exists_upperBound_of_finite_subset` | `FpEmbedding.exists_upperBound_mem_of_finite` | argument order only |
| 3 | `SFP.exists_mem_isLUB_of_finite` | `FpEmbedding.isLUB_of_finite_directed` | binder name only |
| 4 | `SFP.range_toFp_eq` | `SFP.range_normalHom_of_finite` | `(toFp hN).val` unfolds to `normalHom hN`; also declared at `[Domain α]` where `[IsAlgebraic α]` suffices |

Pairs 1–3 are one fact at two strengths. `exists_mem_upperBounds_of_directedOn`
and `Skeleton/Section6`'s `exists_upperBound_mem_of_finite` take the hypothesis
"every `y ∈ t` is dominated by some `z ∈ s`"; pair 2's two take `t ⊆ s`, which
implies it. So the development holds **four** declarations of this lemma, in
three modules, of which two are strictly general and two are the special case.

Pair 1 was found by the elaborator rather than by grep. `MinimalUpperBounds.lean`
imports `Bifinite.lean`, which imports `NormalSubposet` and `Domain` and not
`Skeleton/Section6`, so the second copy could not see the first when it was
written. `Section62.lean` imports both and is the first module where the two
names are simultaneously in scope. This is exactly the masking that
`scripts/unused-theorems.sh` warns about in its header: two declarations sharing a
final name component in different namespaces hide each other from a name-based
count.
-/

namespace ScottDomains.Audit.Projections

open ScottDomains

variable {α : Type*}

/-! ## Pair 1: the general form, declared twice in one namespace -/

section Pair1

variable [Preorder α] {s t : Set α}

/-- `MinimalUpperBounds`'s copy proved by `Skeleton/Section6`'s copy. Both
arguments are passed through unchanged: the two statements are one statement. -/
theorem mub_general_of_skeleton (hd : DirectedOn (· ≤ ·) s) (hne : s.Nonempty)
    (ht : t.Finite) (hdom : ∀ y ∈ t, ∃ z ∈ s, y ≤ z) : ∃ z ∈ s, ∀ y ∈ t, y ≤ z :=
  ScottDomains.exists_upperBound_mem_of_finite hd hne ht hdom

/-- The converse direction, so neither copy is the stronger one. -/
theorem skeleton_general_of_mub (hd : DirectedOn (· ≤ ·) s) (hne : s.Nonempty)
    (ht : t.Finite) (hdom : ∀ y ∈ t, ∃ z ∈ s, y ≤ z) : ∃ z ∈ s, ∀ y ∈ t, y ≤ z :=
  ScottDomains.exists_mem_upperBounds_of_directedOn hd hne ht hdom

end Pair1

/-! ## Pair 2: the `t ⊆ s` special case, also declared twice -/

section Pair2

variable [Preorder α] {s t : Set α}

/-- `SFP.exists_upperBound_of_finite_subset` proved by
`FpEmbedding.exists_upperBound_mem_of_finite`. The proof is the other theorem
applied with its first two arguments swapped. -/
theorem sfp_upperBound_of_fpEmbedding (hne : s.Nonempty) (hdir : DirectedOn (· ≤ ·) s)
    (ht : t.Finite) (hts : t ⊆ s) : ∃ m ∈ s, ∀ y ∈ t, y ≤ m :=
  ScottDomains.FpEmbedding.exists_upperBound_mem_of_finite hdir hne ht hts

/-- The converse direction. -/
theorem fpEmbedding_upperBound_of_sfp (hdir : DirectedOn (· ≤ ·) s) (hne : s.Nonempty)
    (ht : t.Finite) (hts : t ⊆ s) : ∃ u ∈ s, ∀ y ∈ t, y ≤ u :=
  ScottDomains.SFP.exists_upperBound_of_finite_subset hne hdir ht hts

/-- Both of pair 2 are one step from either member of pair 1: a member of `t ⊆ s`
dominates itself. So all four declarations are the same lemma. -/
theorem subset_of_dominated (hdir : DirectedOn (· ≤ ·) s) (hne : s.Nonempty)
    (ht : t.Finite) (hts : t ⊆ s) : ∃ z ∈ s, ∀ y ∈ t, y ≤ z :=
  ScottDomains.exists_mem_upperBounds_of_directedOn hdir hne ht fun y hy => ⟨y, hts hy, le_rfl⟩

end Pair2

/-! ## Pair 3: a finite nonempty directed set attains its least upper bound -/

section Pair3

variable [Preorder α] {s : Set α}

/-- `SFP.exists_mem_isLUB_of_finite` proved by
`FpEmbedding.isLUB_of_finite_directed`. Here even the argument order agrees, so
the proof is the other theorem applied unchanged. -/
theorem sfp_isLUB_of_fpEmbedding (hfin : s.Finite) (hne : s.Nonempty)
    (hdir : DirectedOn (· ≤ ·) s) : ∃ m ∈ s, IsLUB s m :=
  ScottDomains.FpEmbedding.isLUB_of_finite_directed hfin hne hdir

/-- The converse direction. -/
theorem fpEmbedding_isLUB_of_sfp (hfin : s.Finite) (hne : s.Nonempty)
    (hdir : DirectedOn (· ≤ ·) s) : ∃ u ∈ s, IsLUB s u :=
  ScottDomains.SFP.exists_mem_isLUB_of_finite hfin hne hdir

end Pair3

/-! ## Pair 4: the image of a finite normal subposet's projection -/

section Pair4

variable [CompletePartialOrder α] [Domain α] {N : Set α}

/-- `SFP.range_toFp_eq` and `SFP.range_normalHom_of_finite` are the *same*
proposition: `toFp hN` is `normalHom hN` with its finitary-projection proof
attached, so `(toFp hN).val` unfolds to `normalHom hN` by `rfl` and the two
`Set.range` terms are definitionally equal.

`rfl` discharging this equality of propositions is the kernel check. The pair
differs only in that `range_toFp_eq` is declared at `[Domain α]` while
`range_normalHom_of_finite` needs only `[IsAlgebraic α]`. -/
theorem range_toFp_eq_statement (hN : N ◁ compacts α) :
    (Set.range ⇑(toFp hN).val = N) = (Set.range ⇑(normalHom hN) = N) := rfl

/-- The same fact as a term-level derivation, so the duplication is visible in
both directions the audit might act on. -/
theorem range_toFp_of_range_normalHom (hN : N ◁ compacts α) (hfin : N.Finite) :
    Set.range ⇑(toFp hN).val = N :=
  ScottDomains.SFP.range_normalHom_of_finite hN hfin

end Pair4

end ScottDomains.Audit.Projections
