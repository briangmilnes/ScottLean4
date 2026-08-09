import ScottDomains.PropertyM
import ScottDomains.Iwamura
import ScottDomains.Thm18

/-!
# Jung's Theorem 1.37 for algebraic dcpos, without Iwamura's lemma

`JungNets.lean` states Jung 1989's Theorem 1.37 — *a dcpo with continuous function
space is bicomplete* — as three unproved `Prop`-valued definitions:

| # | claim | statement |
| -- | ----- | --------- |
| 1 | `JungNets.Thm137 D` | `IsAlgebraic (ScottHom D D) → JungNets.IsBicomplete D` |
| 2 | `JungNets.Thm137Chains D` | `IsAlgebraic (ScottHom D D) → JungNets.HasChainInfima D` |
| 3 | `PropertyM.Thm137Omega D` | `IsAlgebraic (ScottHom D D) → PropertyM.HasOmegaOpInfima D` |

Five rounds attacked them through Jung's own route — Iwamura's lemma, a
transfinite retraction onto `A ∪ αᵒᵖ`, and his Proposition 1.22 — and
`Iwamura.lean` reduced all three to `IsAlgebraic (ScottHom D D) →
Iwamura.HasWellOrderedInfima D`, which nothing in the development supplies.

**This file does not take that route.** It observes that
`PropertyM.hasOmegaOpBoundsAbove_pair` — Spreen 2005's Lemma 5.8, already proved
and carrying no hypothesis on `D` beyond an algebraic function space — is exactly
the directedness condition the *compact* lower bounds of a descending sequence
need, and that in an algebraic dcpo the supremum of that directed set is the
infimum wanted.

## The construction

For `c ⊆ D` write `compactLowerBounds c = {k | IsCompactElement k ∧ k ∈ lowerBounds c}`.
In an algebraic dcpo two facts are immediate and hold for *every* `c`
(`isGLB_sSup_compactLowerBounds`):

* `sSup (compactLowerBounds c)` is a lower bound of `c`, because every `w ∈ c` is
  an upper bound of `compactLowerBounds c`;
* it is the greatest one, because any lower bound `w` satisfies
  `compactsBelow w ⊆ compactLowerBounds c` and `w = ⊔ compactsBelow w`.

Both need `compactLowerBounds c` to be **directed** for `sSup` to be its least
upper bound, and that single condition is the whole content. Spreen's lemma
supplies it:

* given compact `k₁, k₂` below every member of `c`, it produces `z` above both and
  still below every member;
* algebraicity converts `z` into a **compact** `q ≤ z` above both
  (`exists_compact_upperBound_le`, the `exists_mem_upperBounds_of_directedOn` step
  `PropertyM.hasCompleteMub_of_countable` already uses).

Spreen's lemma is stated for descending `ω`-sequences, so it gives directedness
for `c = Set.range y` outright (`directedOn_compactLowerBounds_range`), and hence
claim 3 with **no countability hypothesis at all**.

For a chain of arbitrary order type the sequence is manufactured. When `K(D)` is
countable, a chain `c` has a countable subset `c₀ ⊆ c` with the *same compact
lower bounds*: for each compact `k` that fails to be a lower bound, keep one
witness `w ∈ c` with `¬ k ≤ w`. `PropertyM.minPrefix` of an enumeration of `c₀` is
then a descending `ω`-sequence coinitial in `c₀`, and Spreen's lemma applies to it.
This is the step Jung takes with Iwamura's lemma; countability does it with one
finite minimum per index, exactly as `PropertyM.hasCompleteMub_of_countable`
already does inside `K(D)`.

## What is proved, and what is not

* `thm137Omega` discharges claim 3 for every `[CompletePartialOrder D]
  [IsAlgebraic D]`.
* `thm137Chains` and `thm137` discharge claims 2 and 1 for every
  `[CompletePartialOrder D] [Domain D]` — an `ω`-algebraic cpo, i.e. `IsAlgebraic`
  plus a countable basis, which is the setting Gunter & Scott's paper works in and
  the setting `Thm18` consumes them in.
* **Jung's theorem in full generality is still open**: an algebraic dcpo with an
  uncountable basis, and a fortiori a merely continuous dcpo, is not covered.
  `Iwamura.thm137Chains_of_wellOrderedInfima` remains the statement of what a
  general proof still owes.

Nothing here uses Iwamura's lemma, `Iwamura.HasWellOrderedInfima`, or Jung's
Proposition 1.22. The axiom footprint is `[propext, Classical.choice, Quot.sound]`,
from `Classical.choice` in `PropertyM.minPrefix`'s decidability branch, in the
witness selection below, and in Spreen's lemma.
-/

namespace ScottDomains.R45.Agent5

open ScottDomains

section Core

variable {D : Type*} [CompletePartialOrder D] [IsAlgebraic D]

/-- The compact elements below every member of `c`. In an algebraic dcpo the
supremum of this set is the infimum of `c` whenever it is directed; see
`isGLB_sSup_compactLowerBounds`. -/
def compactLowerBounds (c : Set D) : Set D :=
  {k | IsCompactElement k ∧ k ∈ lowerBounds c}

omit [IsAlgebraic D] in
theorem compactLowerBounds_nonempty (c : Set D) : (compactLowerBounds c).Nonempty :=
  ⟨⊥, isCompactElement_bot, fun _ _ => bot_le⟩

/-- **A compact upper bound of a compact pair, below a common bound.** `k₁` and `k₂`
both lie in the directed set `compactsBelow z`, so a single member of that set
dominates them.

This is the `exists_mem_upperBounds_of_directedOn` step of
`PropertyM.hasCompleteMub_of_countable`, isolated because both directedness proofs
below need it. -/
theorem exists_compact_upperBound_le {k₁ k₂ z : D} (h₁ : IsCompactElement k₁)
    (h₂ : IsCompactElement k₂) (hz₁ : k₁ ≤ z) (hz₂ : k₂ ≤ z) :
    ∃ q, IsCompactElement q ∧ q ≤ z ∧ k₁ ≤ q ∧ k₂ ≤ q := by
  obtain ⟨q, hq, hqub⟩ :=
    exists_mem_upperBounds_of_directedOn (IsAlgebraic.directedOn_compactsBelow z)
      (compactsBelow_nonempty z) (Set.toFinite ({k₁, k₂} : Set D))
      (by
        intro y hy
        rcases Set.mem_insert_iff.mp hy with h | h
        · exact ⟨k₁, ⟨h₁, hz₁⟩, h.le⟩
        · exact ⟨k₂, ⟨h₂, hz₂⟩, (Set.mem_singleton_iff.mp h).le⟩)
  exact ⟨q, hq.1, hq.2, hqub _ (Set.mem_insert _ _), hqub _ (Set.mem_insert_of_mem _ rfl)⟩

/-- **The supremum of the compact lower bounds is the infimum**, for any set `c`
whose compact lower bounds are directed.

Both halves are algebraicity. Lower bound: every `w ∈ c` is an upper bound of
`compactLowerBounds c`, so the least upper bound of that set is below `w`.
Greatest: a lower bound `w` has `compactsBelow w ⊆ compactLowerBounds c`, and
`IsAlgebraic.isLUB_compactsBelow` makes `w` the least upper bound of the smaller
set. -/
theorem isGLB_sSup_compactLowerBounds {c : Set D}
    (hd : DirectedOn (· ≤ ·) (compactLowerBounds c)) :
    IsGLB c (sSup (compactLowerBounds c)) := by
  have hlub : IsLUB (compactLowerBounds c) (sSup (compactLowerBounds c)) := hd.isLUB_sSup
  constructor
  · intro w hw
    exact hlub.2 fun k hk => hk.2 hw
  · intro w hw
    refine (IsAlgebraic.isLUB_compactsBelow w).2 fun k hk => hlub.1 ⟨hk.1, ?_⟩
    exact fun z hz => hk.2.trans (hw hz)

end Core

/-! ## Claim 3: infima of descending `ω`-sequences -/

section Omega

variable {D : Type*} [CompletePartialOrder D] [IsAlgebraic D]

/-- **Spreen's Lemma 5.8 is a directedness statement.** Given compact `k₁, k₂`
below every term of the descending sequence `y`, `PropertyM.hasOmegaOpBoundsAbove_pair`
produces `z` above both and below every `y n`, and
`exists_compact_upperBound_le` makes it compact. -/
theorem directedOn_compactLowerBounds_range (hAlgF : IsAlgebraic (ScottHom D D))
    {y : ℕ → D} (hy : Antitone y) :
    DirectedOn (· ≤ ·) (compactLowerBounds (Set.range y)) := by
  rintro k₁ ⟨hk₁c, hk₁l⟩ k₂ ⟨hk₂c, hk₂l⟩
  obtain ⟨z, hzub, hzle⟩ :=
    PropertyM.hasOmegaOpBoundsAbove_pair hAlgF hk₁c hk₂c y hy
      (fun n => by
        rintro w (rfl | rfl)
        · exact hk₁l ⟨n, rfl⟩
        · exact hk₂l ⟨n, rfl⟩)
  obtain ⟨q, hqc, hqz, hq₁, hq₂⟩ :=
    exists_compact_upperBound_le hk₁c hk₂c (hzub (Set.mem_insert _ _))
      (hzub (Set.mem_insert_of_mem _ rfl))
  exact ⟨q, ⟨hqc, by rintro _ ⟨n, rfl⟩; exact hqz.trans (hzle n)⟩, hq₁, hq₂⟩

/-- **Infima of descending `ω`-sequences, from an algebraic function space alone.**
No countability hypothesis; the sequence is already indexed by `ℕ`. -/
theorem hasOmegaOpInfima (hAlgF : IsAlgebraic (ScottHom D D)) :
    PropertyM.HasOmegaOpInfima D :=
  fun _ hy => ⟨_, isGLB_sSup_compactLowerBounds (directedOn_compactLowerBounds_range hAlgF hy)⟩

end Omega

/-- **Claim 3 discharged** for every algebraic dcpo: `PropertyM.Thm137Omega D` is
`IsAlgebraic (ScottHom D D) → PropertyM.HasOmegaOpInfima D`, and that is
`hasOmegaOpInfima`. -/
theorem thm137Omega (D : Type*) [CompletePartialOrder D] [IsAlgebraic D] :
    PropertyM.Thm137Omega D :=
  fun hAlgF => hasOmegaOpInfima hAlgF

/-! ## Claims 1 and 2: infima of chains, over a countable basis -/

section Chains

variable {D : Type*} [CompletePartialOrder D] [IsAlgebraic D]

omit [IsAlgebraic D] in
/-- **A countable subchain with the same compact lower bounds.**

For each compact `k` that is not a lower bound of `c`, keep one witness `w ∈ c`
with `¬ k ≤ w`. There are at most `|K(D)|` of them, so the resulting `c₀ ⊆ c` is
countable, and a compact element below every member of `c₀` is below every member
of `c` — otherwise its own witness would be in `c₀` and refute it.

This is what replaces Iwamura's lemma. Jung reduces an arbitrary chain to a
well-ordered one by well-ordering it in order type `|D|`; here the chain is
reduced to a countable one by counting the constraints instead, and countably many
constraints are then met by a single `ω`-sequence. -/
theorem exists_countable_subset_compactLowerBounds (hK : (compacts D).Countable)
    {c : Set D} (hne : c.Nonempty) :
    ∃ c₀ ⊆ c, c₀.Countable ∧ c₀.Nonempty ∧
      ∀ q, IsCompactElement q → q ∈ lowerBounds c₀ → q ∈ lowerBounds c := by
  classical
  obtain ⟨w₀, hw₀⟩ := hne
  have hex : ∀ k : D, k ∉ lowerBounds c → ∃ w ∈ c, ¬ k ≤ w := by
    intro k hk
    by_contra h
    refine hk fun w hw => ?_
    by_contra hkw
    exact h ⟨w, hw, hkw⟩
  choose! wit hwitc hwit using hex
  refine ⟨insert w₀ (wit '' {k | IsCompactElement k ∧ k ∉ lowerBounds c}), ?_, ?_,
    ⟨w₀, Set.mem_insert _ _⟩, ?_⟩
  · rintro w (rfl | ⟨k, hk, rfl⟩)
    · exact hw₀
    · exact hwitc k hk.2
  · exact ((hK.mono fun k hk => hk.1).image wit).insert w₀
  · intro q hqc hq
    by_contra hqn
    exact hwit q hqn (hq (Set.mem_insert_of_mem _ ⟨q, ⟨hqc, hqn⟩, rfl⟩))

/-- **Directedness of the compact lower bounds of a chain**, over a countable
basis.

The chain is replaced by a countable subset with the same compact lower bounds,
that subset is enumerated, and `PropertyM.minPrefix` turns the enumeration into a
descending `ω`-sequence coinitial in it (`PropertyM.minPrefix_le`, the only step
using the chain hypothesis). Spreen's lemma applies to that sequence, and
`exists_compact_upperBound_le` and the previous theorem carry the answer back to
`c`. -/
theorem directedOn_compactLowerBounds_of_isChain (hK : (compacts D).Countable)
    (hAlgF : IsAlgebraic (ScottHom D D)) {c : Set D} (hne : c.Nonempty)
    (hc : IsChain (· ≤ ·) c) :
    DirectedOn (· ≤ ·) (compactLowerBounds c) := by
  classical
  obtain ⟨c₀, hc₀sub, hc₀count, hc₀ne, hc₀key⟩ :=
    exists_countable_subset_compactLowerBounds hK hne
  obtain ⟨f, hf⟩ := hc₀count.exists_eq_range hc₀ne
  have hrangesub : Set.range f ⊆ c := by rw [← hf]; exact hc₀sub
  have hchain : IsChain (· ≤ ·) (Set.range f) := IsChain.mono hrangesub hc
  have hmem : ∀ n, PropertyM.minPrefix f n ∈ c₀ := by
    intro n
    rw [hf]
    exact PropertyM.minPrefix_mem_range f n
  rintro k₁ ⟨hk₁c, hk₁l⟩ k₂ ⟨hk₂c, hk₂l⟩
  obtain ⟨z, hzub, hzle⟩ :=
    PropertyM.hasOmegaOpBoundsAbove_pair hAlgF hk₁c hk₂c _ (PropertyM.antitone_minPrefix f)
      (fun n => by
        rintro w (rfl | rfl)
        · exact hk₁l (hc₀sub (hmem n))
        · exact hk₂l (hc₀sub (hmem n)))
  obtain ⟨q, hqc, hqz, hq₁, hq₂⟩ :=
    exists_compact_upperBound_le hk₁c hk₂c (hzub (Set.mem_insert _ _))
      (hzub (Set.mem_insert_of_mem _ rfl))
  refine ⟨q, ⟨hqc, hc₀key q hqc ?_⟩, hq₁, hq₂⟩
  intro w hw
  rw [hf] at hw
  obtain ⟨n, rfl⟩ := hw
  exact (hqz.trans (hzle n)).trans (PropertyM.minPrefix_le hchain n)

/-- **Infima of nonempty chains**, from an algebraic function space and a countable
basis. This is `JungNets.HasChainInfima D`, the conclusion `JungNets.Thm137Chains`
asks for. -/
theorem hasChainInfima (hK : (compacts D).Countable) (hAlgF : IsAlgebraic (ScottHom D D)) :
    JungNets.HasChainInfima D :=
  fun _ hne hc =>
    ⟨_, isGLB_sSup_compactLowerBounds (directedOn_compactLowerBounds_of_isChain hK hAlgF hne hc)⟩

end Chains

/-- **Claim 2 discharged** for every `ω`-algebraic cpo. `Domain` is `IsAlgebraic`
together with `Set.Countable (compacts D)`, so both hypotheses of `hasChainInfima`
are instances. -/
theorem thm137Chains (D : Type*) [CompletePartialOrder D] [Domain D] :
    JungNets.Thm137Chains D :=
  fun hAlgF => hasChainInfima Domain.countable_compacts hAlgF

/-- **Claim 1 discharged** for every `ω`-algebraic cpo: `Iwamura.thm137_of_thm137Chains`
is the order dual of Markowsky's theorem, which upgrades infima of chains to
infima of filtered sets. -/
theorem thm137 (D : Type*) [CompletePartialOrder D] [Domain D] : JungNets.Thm137 D :=
  Iwamura.thm137_of_thm137Chains (thm137Chains D)

/-- Bicompleteness of an `ω`-algebraic cpo whose function space is algebraic,
stated directly — `thm137` with its hypothesis supplied. -/
theorem isBicomplete (D : Type*) [CompletePartialOrder D] [Domain D]
    [IsAlgebraic (ScottHom D D)] : JungNets.IsBicomplete D :=
  thm137 D inferInstance

/-- **Cross-check, not a new result.** `Thm18.thm18_of_thm137Chains_and_cor136`
was written against `JungNets.Thm137Chains α` as an open hypothesis; feeding it
`thm137Chains` leaves Corollary 1.36 as the only remaining hypothesis, which is
what `PropertyM.thm18_of_cor136` already proves by the route that bypasses
Theorem 1.37 entirely.

This declaration exists so the kernel checks that the two routes agree: the
`Thm137Chains` discharged here is strong enough to drive the Theorem 18 assembly
that five rounds built around it, and not merely strong enough for its own
statement. -/
theorem thm18_of_cor136_via_thm137Chains {α : Type*} [CompletePartialOrder α]
    [Domain α] [Domain (ScottHom α α)]
    (hcor : JungFinite.FixedPointOfCompactDeflationIsCompact α) : IsBifinite α :=
  Thm18.thm18_of_thm137Chains_and_cor136 (thm137Chains α) hcor

end ScottDomains.R45.Agent5
