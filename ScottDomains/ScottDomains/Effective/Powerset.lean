import ScottDomains.EffectivePresentation
import ScottDomains.Powerset
-- `Finset.equivBitIndices : ℕ ≃ Finset ℕ`, the binary-expansion bijection. Declared
-- in `Mathlib/Combinatorics/Colex.lean`; `Nat.mem_bitIndices` and `Nat.testBit_or`
-- are what make the two decision procedures below run on bit operations.
import Mathlib.Combinatorics.Colex

/-!
# §3.2 instantiated: an effective presentation of `P N`

Gunter & Scott, *Semantic Domains*, §3.2 (printed p. 11):

> **Definition:** Let `D` be a domain and suppose `d : ℕ → K(D)` is a surjection.
> Then `d` is an **effective presentation** of `D` if
> 1. the set `{(m, n) | dₘ ⊑ dₙ}` is effectively decidable, and
> 2. for any finite set `u ⊆ ℕ`, it is decidable whether `{dₙ | n ∈ u} ◁ K(D)`.

`EffectivePresentation.lean` (r0022) defined the structure and
`ComputableFunction.lean` (r0031) defined the computable functions between two of
them. **Neither file, nor any other, ever instantiated the structure at a type**
— measured in r0040: `EffectivePresentation \(` matches 0 declarations outside the
two §3.2 modules' own field lists. A structure with no instance is unfalsifiable:
an error in either decidability field would go undetected exactly as an error in
`IsAlgebraic`'s directedness conjunct would have gone undetected before
`Powerset.lean` supplied `P N`. This file is the missing instance, at the same
domain and for the same reason.

## Which enumeration, and why it matters

The obvious enumeration is Mathlib's `Denumerable (Finset ℕ)` instance
(`Mathlib/Logic/Equiv/Finset.lean`), which sorts a `Finset` and re-bases the
resulting list. It would discharge every field. It is the wrong choice here,
because the whole point of §3.2 is that the two conditions are decided by a
*program on indices*, and `Denumerable.ofNat (Finset ℕ)` routes both decisions
through `List.mergeSort`.

The enumeration used instead is the binary expansion,
`Finset.equivBitIndices : ℕ ≃ Finset ℕ`, sending `n` to `{i | n.testBit i}`. Under it
the two conditions collapse to arithmetic on the indices themselves:

| # | Paper's condition | This enumeration |
| -- | ----------------- | ---------------- |
| 1 | `dₘ ⊑ dₙ` | `m ||| n = n` (`powersetEnum_le_iff`) |
| 2 | `{dₙ | n ∈ u} ◁ K(P N)` | `0 ∈ u ∧ ∀ i j ∈ u, i ||| j ∈ u` (`isNormalIn_powersetEnum_image_iff`) |

Both right-hand sides are decided by bitwise-or and `Finset` membership, so the
`Decidable` instances built from them reduce in the kernel — the `example`s at the
end of the file are closed by `decide`, which a `Classical.dec` instance could not
do. That is the check that the two fields carry content.

## The mathematical content: condition 2 for `P N`

Condition 2 is not bookkeeping; it is a theorem about `P N`, proved here as
`isNormalIn_compacts_set_iff` for an arbitrary powerset:

> A set `N` of finite subsets of `X` is normal in `K(P X)` if and only if
> `∅ ∈ N` and `N` is closed under binary union.

Left to right is where the "for every `x`" of `IsNormalIn` is spent: given
`s, t ∈ N`, take `x := s ∪ t`, which is compact; directedness of `N ∩ ↓x`
produces `c ∈ N` with `s ∪ t ⊆ c ⊆ s ∪ t`, so the union itself is in `N`. Right to
left needs `∅` for nonemptiness and the union for directedness. In `P N` the least
upper bound of two compacts always exists, which is why the condition is this
simple; in a general bounded complete domain the corresponding test has to ask
whether the join exists at all, and that is the "tedious, but not difficult"
step Theorem 7's proof defers.

## What this presentation is *not*

It is not shown to be recursive in the sense of `ComputableFunction.RecursiveLE`
(`ComputablePred`, i.e. `Nat.Partrec`-backed). The decision procedure is
`fun p => p.1 ||| p.2 = p.2`, so this reduces to `Computable fun p : ℕ × ℕ =>
p.1 ||| p.2`; Mathlib v4.32.2 states no `Primrec`/`Computable` fact about
`Nat.lor`, `Nat.bitwise` or `Nat.testBit` (grep over `Mathlib/Computability/` for
`lor|nat_bitwise|bitwise` → 0 hits). Supplying it means deriving `Nat.bitwise`
from `Primrec.nat_strong_rec`, which is recursion theory rather than domain
theory. See `Effective/FunctionSpace.lean` for where that gap becomes load-bearing.
-/

namespace ScottDomains.Effective

/-! ## Condition 2 for a powerset -/

variable {X : Type*}

/-- **The finite normal subposets of `K(P X)`, characterized.** A family of finite
subsets is normal in the basis exactly when it contains `∅` and is closed under
binary union.

The forward direction instantiates `IsNormalIn`'s "for every `x ∈ K(P X)`" at
`x := s ∪ t`, which is legitimate because that set is finite, hence compact
(`isCompactElement_iff_finite`); directedness then hands back an element of `N`
squeezed between `s ∪ t` and itself. The reverse direction supplies `∅` for
nonemptiness — the conjunct `IsNormalIn` carries explicitly, per
`NormalSubposet.lean`'s note that Lemma 4.3 fails without it — and the union for
directedness. -/
theorem isNormalIn_compacts_set_iff {N : Set (Set X)} (hN : ∀ s ∈ N, s.Finite) :
    N ◁ compacts (Set X) ↔ (∅ : Set X) ∈ N ∧ ∀ s ∈ N, ∀ t ∈ N, s ∪ t ∈ N := by
  constructor
  · intro h
    refine ⟨?_, fun s hs t ht => ?_⟩
    · have hbot : (⊥ : Set X) ∈ compacts (Set X) := isCompactElement_bot
      simpa using h.bot_mem hbot
    · have hx : (s ∪ t) ∈ compacts (Set X) :=
        isCompactElement_iff_finite.mpr ((hN s hs).union (hN t ht))
      obtain ⟨c, ⟨hcN, hcx⟩, hsc, htc⟩ :=
        h.directedOn hx s ⟨hs, Set.subset_union_left⟩ t ⟨ht, Set.subset_union_right⟩
      have hc : c = s ∪ t := subset_antisymm hcx (Set.union_subset hsc htc)
      rwa [hc] at hcN
  · rintro ⟨hemp, hun⟩
    refine ⟨fun s hs => isCompactElement_iff_finite.mpr (hN s hs), fun x _ => ⟨⟨∅, hemp, ?_⟩, ?_⟩⟩
    · exact Set.empty_subset x
    · rintro s ⟨hs, hsx⟩ t ⟨ht, htx⟩
      exact ⟨s ∪ t, ⟨hun s hs t ht, Set.union_subset hsx htx⟩,
        Set.subset_union_left, Set.subset_union_right⟩

/-! ## The enumeration -/

/-- The enumeration of `K(P N)`: `n` names the set of positions of the `1` bits in
its binary expansion. A bijection onto `Finset ℕ` by `Finset.equivBitIndices`,
hence in particular a surjection onto the compact elements. -/
def powersetEnum (n : ℕ) : Set ℕ := ↑(Finset.equivBitIndices n)

@[simp] theorem mem_powersetEnum {i n : ℕ} : i ∈ powersetEnum n ↔ n.testBit i := by
  simp [powersetEnum]

theorem powersetEnum_finite (n : ℕ) : (powersetEnum n).Finite :=
  (Finset.equivBitIndices n).finite_toSet

theorem powersetEnum_isCompactElement (n : ℕ) : IsCompactElement (powersetEnum n) :=
  isCompactElement_iff_finite.mpr (powersetEnum_finite n)

@[simp] theorem powersetEnum_zero : powersetEnum 0 = (∅ : Set ℕ) := by
  ext i; simp

theorem powersetEnum_injective : Function.Injective powersetEnum := by
  intro a b hab
  refine Nat.eq_of_testBit_eq fun i => ?_
  have : a.testBit i ↔ b.testBit i := by
    rw [← mem_powersetEnum (n := a), ← mem_powersetEnum (n := b), hab]
  simpa using this

/-- Bitwise-or computes the union of two enumerated sets. This is the identity
that turns condition 2 into a `Finset` membership test. -/
theorem powersetEnum_or (a b : ℕ) :
    powersetEnum (a ||| b) = powersetEnum a ∪ powersetEnum b := by
  ext i
  simp [Nat.testBit_or]

/-- **Condition 1, as a bit test.** `dₘ ⊑ dₙ` holds exactly when `m ||| n = n`. -/
theorem powersetEnum_le_iff {a b : ℕ} : powersetEnum a ≤ powersetEnum b ↔ a ||| b = b := by
  constructor
  · intro h
    refine Nat.eq_of_testBit_eq fun i => ?_
    rw [Nat.testBit_or]
    by_cases ha : a.testBit i = true
    · have hb : b.testBit i = true := mem_powersetEnum.mp (h (mem_powersetEnum.mpr ha))
      simp [ha, hb]
    · simp only [Bool.not_eq_true] at ha
      simp [ha]
  · intro h i hi
    rw [mem_powersetEnum] at hi ⊢
    rw [← h, Nat.testBit_or, hi, Bool.true_or]

/-- Every compact element of `P N` — every finite set of naturals — is enumerated:
`n := ∑ i ∈ s, 2 ^ i` is the index, by `Finset.equivBitIndices`'s inverse. -/
theorem powersetEnum_surjective {k : Set ℕ} (hk : IsCompactElement k) :
    ∃ n, powersetEnum n = k := by
  classical
  have hfin : k.Finite := isCompactElement_iff_finite.mp hk
  refine ⟨Finset.equivBitIndices.symm hfin.toFinset, ?_⟩
  rw [powersetEnum, Equiv.apply_symm_apply, Set.Finite.coe_toFinset]

/-! ## The two decision procedures -/

instance decidablePowersetLE (a b : ℕ) :
    Decidable (powersetEnum a ≤ powersetEnum b) :=
  decidable_of_iff _ powersetEnum_le_iff.symm

/-- **Condition 2, as a `Finset` test.** A finite index set `u` names a normal
subposet of `K(P N)` exactly when `0 ∈ u` (the index of `∅`) and `u` is closed
under bitwise-or (the index of the union).

Both conjuncts are `isNormalIn_compacts_set_iff` read through the enumeration:
`powersetEnum` is injective, so `∅ ∈ dᵤ` forces the index `0`, and
`powersetEnum i ∪ powersetEnum j = powersetEnum (i ||| j)` forces the index
`i ||| j`. -/
theorem isNormalIn_powersetEnum_image_iff (u : Finset ℕ) :
    (powersetEnum '' (↑u : Set ℕ)) ◁ compacts (Set ℕ) ↔
      0 ∈ u ∧ ∀ i ∈ u, ∀ j ∈ u, i ||| j ∈ u := by
  rw [isNormalIn_compacts_set_iff (by rintro _ ⟨n, _, rfl⟩; exact powersetEnum_finite n)]
  constructor
  · rintro ⟨hemp, hun⟩
    refine ⟨?_, fun i hi j hj => ?_⟩
    · obtain ⟨n, hn, hne⟩ := hemp
      have : n = 0 := powersetEnum_injective (by rw [hne, powersetEnum_zero])
      rwa [← this, ← Finset.mem_coe]
    · obtain ⟨k, hk, hke⟩ :=
        hun _ ⟨i, Finset.mem_coe.mpr hi, rfl⟩ _ ⟨j, Finset.mem_coe.mpr hj, rfl⟩
      have : k = i ||| j := powersetEnum_injective (by rw [hke, powersetEnum_or])
      rwa [← this, ← Finset.mem_coe]
  · rintro ⟨h0, hor⟩
    refine ⟨⟨0, Finset.mem_coe.mpr h0, powersetEnum_zero⟩, ?_⟩
    rintro _ ⟨i, hi, rfl⟩ _ ⟨j, hj, rfl⟩
    exact ⟨i ||| j, Finset.mem_coe.mpr (hor i (Finset.mem_coe.mp hi) j (Finset.mem_coe.mp hj)),
      powersetEnum_or i j⟩

instance decidablePowersetNormal (u : Finset ℕ) :
    Decidable ((powersetEnum '' (↑u : Set ℕ)) ◁ compacts (Set ℕ)) :=
  decidable_of_iff _ (isNormalIn_powersetEnum_image_iff u).symm

/-! ## The presentation -/

/-- **`P N` has an effective presentation** — the first instantiation of
`EffectivePresentation` at any type in this development.

Both `Decidable` fields are the bit-test instances above, not `Classical.dec`; the
`example`s below check that by asking the kernel to run them. -/
def powersetPresentation : EffectivePresentation (Set ℕ) where
  enum := powersetEnum
  enum_mem_compacts := powersetEnum_isCompactElement
  enum_surjective _ hk := powersetEnum_surjective hk
  decidableLE p := decidablePowersetLE p.1 p.2
  decidableNormal u := decidablePowersetNormal u

/-! ### The decision procedures run

A `Decidable` instance built from `Classical.dec` is stuck under kernel reduction,
so a proof by `decide` is exactly the check that these two fields are programs.
Each `example` below is closed by the kernel evaluating the corresponding bit
test. -/

/-- `5 = 0b101`, so `d₅ = {0, 2}`. -/
example : Finset.equivBitIndices 5 = ({0, 2} : Finset ℕ) := by decide

/-- Condition 1 runs: `1 ||| 5 = 5`, so `d₁ ⊑ d₅`. -/
example : powersetEnum 1 ≤ powersetEnum 5 := by decide

example : ¬ (powersetEnum 2 ≤ powersetEnum 5) := by decide

/-- Condition 2 runs, positively: `{d₀, d₁} = {∅, {0}}` is normal in `K(P N)`. -/
example : (powersetEnum '' (↑({0, 1} : Finset ℕ) : Set ℕ)) ◁ compacts (Set ℕ) := by decide

/-- Condition 2 runs, negatively: `{d₁} = {{0}}` misses `∅`, so it is not normal —
this is Lemma 4.3 (`IsNormalIn.bot_mem`) decided by a program. -/
example : ¬ ((powersetEnum '' (↑({1} : Finset ℕ) : Set ℕ)) ◁ compacts (Set ℕ)) := by decide

/-- Condition 2 runs, negatively again: `{d₀, d₁, d₂} = {∅, {0}, {1}}` contains `∅`
but not `{0, 1} = d₃`, so it is not closed under joins. -/
example : ¬ ((powersetEnum '' (↑({0, 1, 2} : Finset ℕ) : Set ℕ)) ◁ compacts (Set ℕ)) := by decide

end ScottDomains.Effective
