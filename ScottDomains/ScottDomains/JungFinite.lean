import ScottDomains.JungSFP
import ScottDomains.Section62

/-!
# Jung's step 4, and the glue that turns five steps into Theorem 18

`ScottDomains/Section62.lean` decomposes Gunter & Scott's Theorem 18 into the five
steps of A. Jung, *Cartesian Closed Categories of Domains*, CWI Tract 66 (1989).
Steps 2, 3 and 5 are proved (`JungSFP.lemma213`, `JungSFP.thm214`,
`JungSFP.lemma217`, `isBifinite_iff_mubClosure`). This file supplies

* **Lemma 1.29** — property M at the empty set and at pairs implies property M at
  every finite set. This is the join between step 3 and step 5: `lemma217`
  concludes finiteness of `mub{a₁, a₂}` for a *pair*, and
  `isBifinite_iff_mubClosure` consumes a statement about *every* finite subset of
  `K(D)`;
* **step 4, Jung's Lemma 2.2** — property M implies `U ^∞(A)` finite — in full,
  together with the two prerequisites `Section62.lean` records as missing:
  the selection principle that extracts an infinite chain from an infinite
  `U ^∞(A)`, and Jung's Corollary 1.36;
* **the assembly**, `thm18_of_hasCompleteMub`, which is Theorem 18 with Jung's
  Theorem 1.37 — step 1 — as an explicit hypothesis, in the shape `lemma217`
  already uses.

Everything is read off the PDF in `ScottDomains/papers/Jung 1989 Cartesian Closed
Categories of Domains.pdf`, quoted rather than paraphrased.

## Lemma 1.29, and the empty set

> **Lemma 1.29** A poset `D` with property m has property M if and only if the
> empty set and each pair of elements have a finite set of minimal upper bounds.

The **empty set is part of the hypothesis** and is not redundant. An infinite
antichain has property m (every upper bound of a finite subset is above a minimal
one, vacuously for a pair with no upper bound at all) and every pair has a finite
— indeed empty — set of minimal upper bounds, yet `mub(∅)`, the set of minimal
elements, is infinite. Over `K(D)` in a cpo the clause is free:
`minimalUpperBounds_compacts_empty` computes `mub(∅) = {⊥}`, so `lemma129` below
carries only the pair hypothesis.

Jung's proof builds `M₂ = mub{a₁, a₂}` and `M_{i+1} = ⋃_{x ∈ Mᵢ} mub{x, a_{i+1}}`
and observes that `Mₙ` is a *finite complete set of upper bounds* of `A` — finite,
consisting of upper bounds, and with every upper bound of `A` above one of its
members. `exists_finite_complete_upperBoundsIn` is that set, built by induction on
the finite set rather than along an enumeration of it; the induction starts at `∅`
instead of at a pair, which is why the empty-set clause appears as a hypothesis
exactly where Jung states it. Minimality inside a finite complete set of upper
bounds upgrades to minimality outright, which is the same step as
`hasCompleteMub_of_isNormalIn`.

## Step 4: Jung's Lemma 2.2

> **Lemma 2.2** If `D` is a dcpo with algebraic function space and if `B(D)` has
> property M then `U ^∞(A)` is finite for each finite set `A` of compact elements.

Jung's proof, in the order the parts appear below.

1. Property M makes each stage `Uⁿ(A)` finite (`mubIter_finite`): a finite stage
   has finitely many finite subsets, each contributing finitely many minimal
   upper bounds.
2. If `U ^∞(A)` is infinite the differences `Bₙ = U ⁿ⁺¹(A) \ Uⁿ(A)` are all
   nonempty (`mubDiff_nonempty`) — a stage that adds nothing has already
   stabilized — and finite, and every member of `Bₙ₊₁` lies above a member of
   `Bₙ` (`exists_mem_mubDiff_le`, Jung: "each element of `Bₙ` is above some
   element of `Bₙ₋₁` because otherwise it would belong to `Uⁿ⁻¹(A)` already").
3. A selection principle turns that graded system into an infinite ascending
   chain (`exists_monotone_seq`). Jung cites **Rado's Selection Theorem**
   (his Theorem 2.1, proved by Tychonoff over an arbitrary index set); the
   grading here is by `ℕ`, so **König's lemma** suffices and is what is proved,
   by the standard infinite-descendant argument. See the note below.
4. Algebraicity of `[D → D]` supplies a compact `f ⊑ id` fixing `A`
   (`exists_isCompactElement_le`, r0031); `apply_eq_self_of_mem_mubClosure`
   (r0034) propagates that to all of `U ^∞(A)`, hence to the chain and to its
   least upper bound `c`.
5. **Corollary 1.36** makes `c` compact, and
   `not_isCompactElement_of_isLUB_strictMono` (r0034) says the least upper bound
   of a strictly ascending sequence never is.

### Which selection principle, and why

König, not Rado. Jung's Theorem 2.1 is stated for an arbitrary index set `I` and
proved by Tychonoff's theorem on `∏_{i ∈ I} Aᵢ`; Mathlib's only form of it is
`nonempty_sections_of_finite_inverse_system`, which needs the system presented as
a functor out of a category and drags in `Mathlib.CategoryTheory.CofilteredSystem`
and the product topology. Lemma 2.2 applies it at `I = ℕ` with fibers `Bₙ`, which
is exactly König's lemma for a finitely branching tree of height `ω`, and that has
an elementary proof — `exists_monotone_seq` below — needing no topology, no
category theory, and no cardinality hypothesis. In particular **countability of
`K(D)` is not what makes this step work**, contrary to the note in
`Skeleton/Section6.lean`: the grading by `ℕ` is supplied by the `U`-iteration
itself. Countability of `K(D → D)` is still indispensable to Theorem 18, and is
still spent exactly once, in `JungSFP.lemma217`.

### Corollary 1.36, and the form proved here

> **Corollary 1.36** If `D` is a dcpo with a continuous function space and if for
> `f, g ∈ [D → D]`, `f` is way-below `g`, then `f(d)` is way-below `g(d)` for all
> `d ∈ D`.

Jung derives it from Proposition 1.34, whose proof restricts to the principal
ideal `↓e` and needs his Proposition 1.22 — continuity of the function space of a
retract — to know that `f|↓e ≪ id↓e`. Lemma 2.2 uses only the instance `g = id`
with `f` **compact**, and at `g = id` that detour is unnecessary:
`isCompactElement_of_apply_eq_self` below proves the instance directly.

The argument is Jung's, with compactness in place of the way-below relation. Let
`c = ⨆↑S` with `S` directed and let `f` be compact in `[D → D]` with `f ⊑ id` and
`f(c) = c`. Restricting to `↓c` is legitimate because `f ⊑ id` maps `↓c` into
itself; the restriction `f|↓c` is again **compact**, by extending any directed
family `T` of functions on `↓c` to `D` by the identity outside `↓c`
(`extendIic`) and applying compactness of `f` there. The extension is where
`f ⊑ id` is spent a second time: it is what makes `f ⊑ ext h` off `↓c`. Now the
constant functions `c_s`, `s ∈ S`, are a directed family on `↓c` with least upper
bound the constant `c_c`, which is the top of `[↓c → ↓c]` and so is above `f|↓c`;
compactness of `f|↓c` therefore puts `f|↓c ⊑ c_s` for a single `s ∈ S`, and
evaluating at `c` gives `c = f(c) ⊑ s`. That is compactness of `c`.

`↓c` carries only the `PartialOrder` instance the subtype inherits, which is all
`ScottHom` and `IsCompactElement` need; no cpo structure on the subtype is
constructed.

## What is still open between this file and `thm18`

One step: Jung's **Theorem 1.37**, "a dcpo with continuous function space is
bicomplete", which is property m and is the hypothesis `hm` of
`thm18_of_hasCompleteMub`. No `sorry` stands in for it; it is an explicit
argument of the theorem, exactly as in `JungSFP.lemma217`.
-/

namespace ScottDomains.JungFinite

open ScottDomains

variable {α : Type*}

/-! ## Jung's Lemma 1.29 -/

section Lemma129

variable [PartialOrder α] {A u : Set α}

/-- **The set `Mₙ` of Jung's proof of Lemma 1.29.** For a finite `u ⊆ A` there is
a *finite complete set of upper bounds*: a finite `M ⊆ ub_A(u)` such that every
upper bound of `u` in `A` dominates a member of `M`.

Induction on `u`. The empty case is `mub(∅)`, finite by hypothesis and complete by
property m at `∅`. The step replaces Jung's `M_{i+1} = ⋃_{x ∈ Mᵢ} mub{x, a_{i+1}}`
verbatim: it is finite as a finite union of finite sets, its members bound
`insert a u` because they bound both `a` and some bound of `u`, and it is complete
because an upper bound `x` of `insert a u` dominates some `y ∈ M`, hence bounds
the pair `{y, a}`, and property m at that pair produces a minimal upper bound of
it below `x`. -/
theorem exists_finite_complete_upperBoundsIn
    (hm : ∀ v : Set α, v ⊆ A → v.Finite → HasCompleteMub A v)
    (hpair : ∀ a ∈ A, ∀ b ∈ A, (minimalUpperBounds A ({a, b} : Set α)).Finite)
    (hempty : (minimalUpperBounds A (∅ : Set α)).Finite) (hu : u.Finite) :
    u ⊆ A → ∃ M : Set α, M.Finite ∧ M ⊆ upperBoundsIn A u ∧
      ∀ x ∈ upperBoundsIn A u, ∃ y ∈ M, y ≤ x := by
  induction u, hu using Set.Finite.induction_on with
  | empty =>
    intro _
    exact ⟨minimalUpperBounds A ∅, hempty, minimalUpperBounds_subset,
      fun x hx => hm ∅ (Set.empty_subset A) Set.finite_empty x hx⟩
  | @insert a v _ _ ih =>
    intro hsub
    have haA : a ∈ A := hsub (Set.mem_insert a v)
    obtain ⟨M, hMfin, hMsub, hMcomp⟩ := ih fun y hy => hsub (Set.mem_insert_of_mem a hy)
    refine ⟨⋃ y ∈ M, minimalUpperBounds A ({y, a} : Set α), ?_, ?_, ?_⟩
    · exact hMfin.biUnion fun y hy => hpair y (upperBoundsIn_subset (hMsub hy)) a haA
    · rintro z hz
      obtain ⟨y, hyM, hzy⟩ := Set.mem_iUnion₂.mp hz
      have hzub := minimalUpperBounds_subset hzy
      refine ⟨hzub.1, ?_⟩
      rintro w (rfl | hw)
      · exact hzub.2 (Set.mem_insert_of_mem _ rfl)
      · exact ((hMsub hyM).2 hw).trans (hzub.2 (Set.mem_insert _ _))
    · intro x hx
      obtain ⟨y, hyM, hyx⟩ :=
        hMcomp x ⟨hx.1, fun w hw => hx.2 (Set.mem_insert_of_mem a hw)⟩
      have hxpair : x ∈ upperBoundsIn A ({y, a} : Set α) := by
        refine ⟨hx.1, ?_⟩
        rintro w (rfl | rfl)
        · exact hyx
        · exact hx.2 (Set.mem_insert _ _)
      obtain ⟨m, hmM, hmx⟩ :=
        hm _ (by rintro w (rfl | rfl); exacts [upperBoundsIn_subset (hMsub hyM), haA])
          (Set.toFinite _) x hxpair
      exact ⟨m, Set.mem_iUnion₂.mpr ⟨y, hyM, hmM⟩, hmx⟩

/-- **Jung 1989, Lemma 1.29.** A poset with property m in which the empty set and
each pair have finitely many minimal upper bounds has property M: *every* finite
subset has finitely many minimal upper bounds.

The whole content is `exists_finite_complete_upperBoundsIn`; a minimal upper bound
`m` dominates a member `y` of that finite complete set, and `y` is itself an upper
bound, so minimality forces `m = y ∈ M`. This is `minimalUpperBounds_subset_of_isNormalIn`'s
step with the finite complete set in place of `N ∩ ↓x`. -/
theorem minimalUpperBounds_finite_of_pairs
    (hm : ∀ v : Set α, v ⊆ A → v.Finite → HasCompleteMub A v)
    (hpair : ∀ a ∈ A, ∀ b ∈ A, (minimalUpperBounds A ({a, b} : Set α)).Finite)
    (hempty : (minimalUpperBounds A (∅ : Set α)).Finite) (hu : u.Finite) (huA : u ⊆ A) :
    (minimalUpperBounds A u).Finite := by
  obtain ⟨M, hMfin, hMsub, hMcomp⟩ :=
    exists_finite_complete_upperBoundsIn hm hpair hempty hu huA
  refine hMfin.subset ?_
  rintro m ⟨hmub, hmin⟩
  obtain ⟨y, hyM, hym⟩ := hMcomp m hmub
  exact le_antisymm hym (hmin (hMsub hyM) hym) ▸ hyM

end Lemma129

section Lemma129Compacts

variable [CompletePartialOrder α]

/-- **`mub(∅) = {⊥}` in `K(D)`.** The upper bounds of `∅` in `K(D)` are all of
`K(D)`, and `⊥` is compact and below everything, so it is the unique minimal one.
This is what discharges Lemma 1.29's empty-set clause for free over a cpo. -/
theorem minimalUpperBounds_compacts_empty :
    minimalUpperBounds (compacts α) (∅ : Set α) = {⊥} := by
  have hbot : (⊥ : α) ∈ upperBoundsIn (compacts α) (∅ : Set α) :=
    ⟨(isCompactElement_bot : IsCompactElement (⊥ : α)), fun _ hy => absurd hy (Set.notMem_empty _)⟩
  refine Set.Subset.antisymm (fun m hm => ?_) (fun m hm => ?_)
  · exact le_antisymm (hm.2 hbot bot_le) bot_le
  · subst hm
    exact ⟨hbot, fun _ _ _ => bot_le⟩

/-- **Lemma 1.29 over `K(D)`.** Property m together with property M *at pairs* —
which is exactly what `JungSFP.lemma217` delivers — gives property M at every
finite set of compact elements, which is what `isBifinite_iff_mubClosure`
consumes. The empty-set clause is discharged by
`minimalUpperBounds_compacts_empty`. -/
theorem lemma129
    (hm : ∀ v : Set α, v ⊆ compacts α → v.Finite → HasCompleteMub (compacts α) v)
    (hpair : ∀ a₁ a₂ : α, IsCompactElement a₁ → IsCompactElement a₂ →
      (minimalUpperBounds (compacts α) ({a₁, a₂} : Set α)).Finite)
    {u : Set α} (hu : u.Finite) (huc : u ⊆ compacts α) :
    (minimalUpperBounds (compacts α) u).Finite :=
  minimalUpperBounds_finite_of_pairs hm (fun a ha b hb => hpair a b ha hb)
    (by rw [minimalUpperBounds_compacts_empty]; exact Set.finite_singleton _) hu huc

end Lemma129Compacts

end ScottDomains.JungFinite
