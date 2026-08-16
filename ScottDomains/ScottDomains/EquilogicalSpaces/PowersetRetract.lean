import ScottDomains.EquilogicalSpaces.Extension
import ScottDomains.Powerset

/-!
# Every algebraic lattice is a continuous retract of a powerset

The lemma Theorem 3.12's *fullness* half needs, and the one the paper alludes to
when it remarks after Theorem 3.7:

> Scott noticed the above theorems in 1970/71 and also pointed out that it in
> fact holds for all the continuous retracts of the powerset spaces — these are
> the continuous lattices — but for our purposes here, the above suffices.

Theorem 3.7 as proved in `Extension.lean` extends a continuous map into a
**powerset**. Theorem 3.12 needs the wider form the paper states in its proof —
"continuous functions between `T₀`-spaces can be extended to any algebraic
lattices embedding them". Bridging the two is exactly a retraction

    L  --compactsEmbed-->  𝒫 (K L)  --compactsRetract-->  L

with `compactsRetract ∘ compactsEmbed = id`, both maps Scott-continuous.

## The three facts, and what each costs

| Fact | What it spends |
| ---- | -------------- |
| `compactsRetract_compactsEmbed` | **algebraicity** — `x` is the supremum of its compact approximants |
| `scottContinuous_compactsEmbed` | **compactness** — `k ≤ ⨆ d` for directed `d` already gives `k ≤ y` for some `y ∈ d` |
| `scottContinuous_compactsRetract` | nothing but that suprema commute |

That the middle one is exactly the definition of a compact element is the point
of the construction: the embedding is continuous *because* its values are cut out
by compact elements, and no other choice of index set would work.

Stated for complete lattices, which is the `ALat` setting; `sSup` is then a least
upper bound of every subset, not only of the directed ones.
-/

universe u

namespace ScottDomains.EquilogicalSpaces

open ScottDomains

section Retract

variable {L : Type u} [CompleteLattice L]

/-- The embedding of an algebraic lattice into the powerset of its compact
    elements: `x ↦ { k ∈ K L | k ≤ x }`. -/
def compactsEmbed (x : L) : Set ↥(compacts L) := { k | (k : L) ≤ x }

/-- The retraction back: take the supremum. -/
def compactsRetract (S : Set ↥(compacts L)) : L := sSup (Subtype.val '' S)

theorem coe_image_compactsEmbed (x : L) :
    Subtype.val '' compactsEmbed x = compactsBelow x := by
  ext y
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k.2, hk⟩
  · rintro ⟨hc, hle⟩
    exact ⟨⟨y, hc⟩, hle, rfl⟩

/-- **The embedding is Scott-continuous**, and this is exactly compactness: for
    directed `d` with supremum `a`, a compact `k ≤ a` already satisfies `k ≤ y`
    for some `y ∈ d`, which says precisely that `compactsEmbed a` is covered by
    the `compactsEmbed y`. -/
theorem scottContinuous_compactsEmbed :
    ScottContinuous (compactsEmbed : L → Set ↥(compacts L)) := by
  intro d hne hd a hlub
  constructor
  · rintro _ ⟨y, hy, rfl⟩
    exact fun k hk => le_trans hk (hlub.1 hy)
  · intro T hT k hk
    obtain ⟨y, hy, hky⟩ := k.2 d a hne hd hlub hk
    exact hT ⟨y, hy, rfl⟩ hky

/-- **The retraction is Scott-continuous.** Nothing but the commutation of
    suprema; neither compactness nor algebraicity is used. -/
theorem scottContinuous_compactsRetract :
    ScottContinuous (compactsRetract : Set ↥(compacts L) → L) := by
  intro D hne hD T hlub
  constructor
  · rintro _ ⟨S, hS, rfl⟩
    exact sSup_le_sSup (Set.image_mono (hlub.1 hS))
  · intro b hb
    refine sSup_le ?_
    rintro _ ⟨k, hkT, rfl⟩
    have hTsup : T = sSup D := ((isLUB_sSup D).unique hlub).symm
    rw [hTsup, Set.sSup_eq_sUnion] at hkT
    obtain ⟨S, hSD, hkS⟩ := hkT
    exact le_trans (le_sSup (Set.mem_image_of_mem Subtype.val hkS))
      (hb (Set.mem_image_of_mem compactsRetract hSD))

variable [ScottDomains.IsAlgebraic L]

/-- **The retraction identity.** This is where algebraicity is spent, and it is
    the only place: `x` is the least upper bound of its compact approximants, so
    taking the supremum undoes the embedding.

    Note what the section structure records — `compactsEmbed`, `compactsRetract`
    and both continuity proofs need *no* algebraicity at all. They are facts
    about any complete lattice. Algebraicity enters exactly once, here, and it is
    precisely what makes the pair a retraction rather than merely an adjunction. -/
theorem compactsRetract_compactsEmbed (x : L) :
    compactsRetract (compactsEmbed x) = x := by
  rw [compactsRetract, coe_image_compactsEmbed]
  exact (isLUB_sSup _).unique (ScottDomains.IsAlgebraic.isLUB_compactsBelow x)

end Retract

end ScottDomains.EquilogicalSpaces
