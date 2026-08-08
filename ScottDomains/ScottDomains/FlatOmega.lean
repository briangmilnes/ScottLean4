import ScottDomains.Flat
import Mathlib.Data.ENat.Basic
-- `CompleteLinearOrder ℕ∞`, which is what makes `ω⊤` a cpo.
import Mathlib.Data.ENat.Lattice

/-!
# §2.1's other two example cpos: `ω` and `ω⊤`

Gunter & Scott, *Semantic Domains*, §2.1, printed p. 3–4. The section lists a
row of example cpos, of which `ScottDomains.Flat` supplies the flat ones. Two
more are stated here because they are the same kind of small concrete carrier and
r0040 recorded them as having no Lean statement:

> the ordinal `ω` … [is] not a cpo (printed p. 3)

> the function `f : ω⊤ → O` … is monotone, but it is not continuous
> (printed p. 4)

`ω` is `ℕ` under its usual order and `ω⊤` is `ℕ` with a top adjoined, which is
Mathlib's `ℕ∞`. `O` is the two-point chain, which in this development is `Prop`
— `Domain.lean` already uses it as its cheapest witness.

Both statements are refutations, so each is given as the concrete failing datum
rather than as a negated typeclass: `ω` fails because one nonempty directed
subset has no least upper bound, and `f` fails continuity at one directed set.
That is what the paper's sentences assert, and it does not require quantifying
over hypothetical `CompletePartialOrder` instances.
-/

namespace ScottDomains.Flat

open ScottDomains

/-! ## `ω` is not a cpo -/

theorem directedOn_univ_nat : DirectedOn (· ≤ ·) (Set.univ : Set ℕ) :=
  fun a _ b _ => ⟨max a b, trivial, Nat.le_max_left a b, Nat.le_max_right a b⟩

/-- **`ω` is not a cpo** (§2.1, printed p. 3). The whole of `ℕ` is a nonempty
directed subset of `ℕ` with no upper bound at all, hence no least one: any
candidate `u` is beaten by `u + 1`. -/
theorem not_exists_isLUB_univ_nat : ¬ ∃ u : ℕ, IsLUB (Set.univ : Set ℕ) u := by
  rintro ⟨u, hu⟩
  exact Nat.not_succ_le_self u (hu.1 (Set.mem_univ (u + 1)))

/-- The paper's reason, in one statement: a nonempty directed subset of `ω` with
no least upper bound. -/
theorem omega_not_cpo :
    (Set.univ : Set ℕ).Nonempty ∧ DirectedOn (· ≤ ·) (Set.univ : Set ℕ) ∧
      ¬ ∃ u : ℕ, IsLUB (Set.univ : Set ℕ) u :=
  ⟨⟨0, trivial⟩, directedOn_univ_nat, not_exists_isLUB_univ_nat⟩

/-! ## `ω⊤`, and a monotone function out of it that is not continuous -/

/-- `ω⊤`: the naturals with a top adjoined. Mathlib's `ℕ∞` is that order, and it
is a complete lattice, hence a cpo. -/
abbrev OmegaTop : Type := ℕ∞

noncomputable example : CompletePartialOrder OmegaTop := inferInstance

/-- The chain of finite elements of `ω⊤`. -/
def natRange : Set OmegaTop := Set.range ((↑) : ℕ → ℕ∞)

theorem natRange_nonempty : natRange.Nonempty := ⟨(0 : ℕ), ⟨0, rfl⟩⟩

theorem directedOn_natRange : DirectedOn (· ≤ ·) natRange := by
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
  refine ⟨((max a b : ℕ) : ℕ∞), ⟨max a b, rfl⟩, ?_, ?_⟩
  · exact Nat.cast_le.mpr (Nat.le_max_left a b)
  · exact Nat.cast_le.mpr (Nat.le_max_right a b)

/-- `⊤` is the least upper bound of the finite elements: an upper bound that is
not `⊤` would be some `↑m`, and `↑(m+1)` is above it. -/
theorem isLUB_natRange : IsLUB natRange (⊤ : ℕ∞) := by
  refine ⟨fun _ _ => le_top, fun u hu => ?_⟩
  by_contra hnle
  have hne : u ≠ ⊤ := fun h => hnle (le_of_eq h.symm)
  obtain ⟨m, rfl⟩ := WithTop.ne_top_iff_exists.mp hne
  exact Nat.not_succ_le_self m (Nat.cast_le.mp (hu ⟨m + 1, rfl⟩))

/-- The paper's `f : ω⊤ → O`: `⊥` on every finite element and `⊤` at the top. -/
def omegaTest : OmegaTop → Prop := fun x => x = ⊤

theorem monotone_omegaTest : Monotone omegaTest := by
  intro x y hxy hx
  exact top_le_iff.mp (le_trans (le_of_eq hx.symm) hxy)

/-- **`f : ω⊤ → O` is monotone but not continuous** (§2.1, printed p. 4). The
finite elements are a nonempty directed set with least upper bound `⊤`, but every
one of their images is the false proposition, so the image is bounded above by
`False` while `f ⊤` is `True`. -/
theorem not_scottContinuous_omegaTest : ¬ ScottContinuous omegaTest := by
  intro hcont
  have h := hcont natRange_nonempty directedOn_natRange isLUB_natRange
  have hub : (False : Prop) ∈ upperBounds (omegaTest '' natRange) := by
    rintro _ ⟨_, ⟨n, rfl⟩, rfl⟩ hn
    exact ENat.coe_ne_top n hn
  exact h.2 hub (rfl : (⊤ : ℕ∞) = ⊤)

/-- The paper's sentence, as one statement. -/
theorem omegaTop_monotone_not_continuous :
    Monotone omegaTest ∧ ¬ ScottContinuous omegaTest :=
  ⟨monotone_omegaTest, not_scottContinuous_omegaTest⟩

end ScottDomains.Flat
