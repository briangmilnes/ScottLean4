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

/-! ## König's lemma for an `ℕ`-graded system

Jung's Theorem 2.1 is Rado's Selection Theorem, stated for an arbitrary index set
and proved by Tychonoff. Lemma 2.2 applies it only at index set `ℕ`, where the
elementary argument below suffices: choose one parent per node, call `x` *fat* if
it has infinitely many descendants, and observe that each level contains a fat
node and that every fat node has a fat child. -/

section Konig

/-- The `k`-fold parent of `x`, taken from level `n + k` down to level `n`, for a
level-indexed parent map `p`.

The recursion peels **from the bottom** — `p n` is applied last — which is what
makes `desc_subset_insert_biUnion` hold: a descendant of `x` at distance `k + 1`
is a descendant at distance `k` of one of `x`'s immediate children. -/
def climbDown (p : ℕ → α → α) : ℕ → ℕ → α → α
  | 0, _, x => x
  | k + 1, n, x => p n (climbDown p k (n + 1) x)

/-- The descendants of `x ∈ B n`: the members of the later levels whose iterated
parent at level `n` is `x`. -/
def desc (p : ℕ → α → α) (B : ℕ → Set α) (n : ℕ) (x : α) : Set α :=
  {z | ∃ k, z ∈ B (n + k) ∧ climbDown p k n z = x}

variable {p : ℕ → α → α} {B : ℕ → Set α}

section Preorder

variable [Preorder α]

/-- Iterated parents stay in the graded family: `climbDown p k n` maps `B (n + k)`
into `B n`. -/
theorem climbDown_mem (hp : ∀ n, ∀ x ∈ B (n + 1), p n x ∈ B n ∧ p n x ≤ x) :
    ∀ k n, ∀ x ∈ B (n + k), climbDown p k n x ∈ B n := by
  intro k
  induction k with
  | zero => intro n x hx; exact hx
  | succ k ih =>
    intro n x hx
    rw [show n + (k + 1) = (n + 1) + k by omega] at hx
    exact (hp n _ (ih (n + 1) x hx)).1

/-- Iterated parents lie below the node they came from, by transitivity of the
single-step inequality. -/
theorem climbDown_le (hp : ∀ n, ∀ x ∈ B (n + 1), p n x ∈ B n ∧ p n x ≤ x) :
    ∀ k n, ∀ x ∈ B (n + k), climbDown p k n x ≤ x := by
  intro k
  induction k with
  | zero => intro n x _; exact le_rfl
  | succ k ih =>
    intro n x hx
    rw [show n + (k + 1) = (n + 1) + k by omega] at hx
    exact ((hp n _ (climbDown_mem hp k (n + 1) x hx)).2).trans (ih (n + 1) x hx)

/-- Every node of a later level is a descendant of some node of level `n`, namely
of its own iterated parent. This is what makes the finitely many descendant sets
at level `n` cover the whole tail. -/
theorem subset_biUnion_desc (hp : ∀ n, ∀ x ∈ B (n + 1), p n x ∈ B n ∧ p n x ≤ x)
    (n : ℕ) : (⋃ k, B (n + k)) ⊆ ⋃ x ∈ B n, desc p B n x := by
  rintro z hz
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hz
  exact Set.mem_iUnion₂.mpr ⟨climbDown p k n z, climbDown_mem hp k n z hk, k, hk, rfl⟩

/-- **The decomposition König's lemma turns on.** A descendant of `x` is either
`x` itself or a descendant of one of `x`'s immediate children. Since the children
form a subset of the finite level `B (n + 1)`, a node all of whose children have
finitely many descendants has finitely many descendants. -/
theorem desc_subset_insert_biUnion (hp : ∀ n, ∀ x ∈ B (n + 1), p n x ∈ B n ∧ p n x ≤ x)
    (n : ℕ) (x : α) :
    desc p B n x ⊆ insert x (⋃ y ∈ {y ∈ B (n + 1) | p n y = x}, desc p B (n + 1) y) := by
  rintro z ⟨k, hzk, hzx⟩
  cases k with
  | zero => rw [show z = x from hzx]; exact Set.mem_insert _ _
  | succ k =>
    rw [show n + (k + 1) = (n + 1) + k by omega] at hzk
    exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_iUnion₂.mpr
      ⟨climbDown p k (n + 1) z, ⟨climbDown_mem hp k (n + 1) z hzk, hzx⟩, k, hzk, rfl⟩))

end Preorder

section Main

variable [Preorder α]

/-- **König's lemma, graded by `ℕ`.** A family of finite nonempty levels whose
union is infinite, in which every node of level `n + 1` lies above some node of
level `n`, contains a monotone transversal — a sequence `x` with `x n ∈ B n` and
`x` monotone.

This is the instance of Jung's Theorem 2.1 (Rado's Selection Theorem) that
Lemma 2.2 uses, and unlike Rado's general form it needs no compactness argument:
the index set is `ℕ`, so the standard finitely-branching-tree proof applies. Note
that the levels being finite is used twice — once to make some node of each level
have infinitely many descendants, once to make some child of such a node inherit
that property — and that no cardinality hypothesis on `α` appears.

`hne` is used only to supply a junk value when totalizing the parent choice; it is
not otherwise needed, since infiniteness of the union already forces every level
to be nonempty. -/
theorem exists_monotone_seq (hfin : ∀ n, (B n).Finite) (hne : ∀ n, (B n).Nonempty)
    (hinf : (⋃ n, B n).Infinite)
    (hpar : ∀ n, ∀ x ∈ B (n + 1), ∃ y ∈ B n, y ≤ x) :
    ∃ x : ℕ → α, (∀ n, x n ∈ B n) ∧ Monotone x := by
  classical
  -- a total parent map at each level
  have hpar' : ∀ n : ℕ, ∃ q : α → α, ∀ x ∈ B (n + 1), q x ∈ B n ∧ q x ≤ x := by
    intro n
    obtain ⟨b, hb⟩ := hne n
    refine ⟨fun x => if h : ∃ y ∈ B n, y ≤ x then h.choose else b, fun x hx => ?_⟩
    have h : ∃ y ∈ B n, y ≤ x := hpar n x hx
    simp only [dif_pos h]
    exact ⟨h.choose_spec.1, h.choose_spec.2⟩
  choose q hq using hpar'
  -- the tail above any level is still infinite
  have htail : ∀ n, (⋃ k, B (n + k)).Infinite := by
    intro n hfinTail
    refine hinf (Set.Finite.subset (Set.Finite.union
      ((Set.finite_Iio n).biUnion fun m _ => hfin m) hfinTail) ?_)
    rintro z hz
    obtain ⟨m, hm⟩ := Set.mem_iUnion.mp hz
    by_cases h : m < n
    · exact Or.inl (Set.mem_iUnion₂.mpr ⟨m, h, hm⟩)
    · refine Or.inr (Set.mem_iUnion.mpr ⟨m - n, ?_⟩)
      rwa [show n + (m - n) = m by omega]
  -- the nodes with infinitely many descendants
  set Good : ℕ → Set α := fun n => {x ∈ B n | (desc q B n x).Infinite} with hGoodDef
  have hGoodne : ∀ n, (Good n).Nonempty := by
    intro n
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    refine htail n (Set.Finite.subset ((hfin n).biUnion fun x hx => ?_)
      (subset_biUnion_desc hq n))
    by_contra hnf
    exact Set.eq_empty_iff_forall_notMem.mp hemp x ⟨hx, hnf⟩
  have hstep : ∀ n : ℕ, ∀ x ∈ Good n, ∃ y ∈ Good (n + 1), x ≤ y := by
    intro n x hx
    by_contra hno
    have hno' : ∀ y, y ∈ Good (n + 1) → ¬ x ≤ y := fun y hy hxy => hno ⟨y, hy, hxy⟩
    refine hx.2 (Set.Finite.subset (Set.Finite.insert x
      (((hfin (n + 1)).subset fun y hy => hy.1).biUnion fun y hy => ?_))
      (desc_subset_insert_biUnion hq n x))
    by_contra hnf
    exact hno' y ⟨hy.1, hnf⟩ (hy.2 ▸ (hq n y hy.1).2)
  -- totalize the successor choice and iterate it
  have hstep' : ∀ n : ℕ, ∃ F : α → α, ∀ x ∈ Good n, F x ∈ Good (n + 1) ∧ x ≤ F x := by
    intro n
    obtain ⟨b, hb⟩ := hGoodne (n + 1)
    refine ⟨fun x => if h : ∃ y ∈ Good (n + 1), x ≤ y then h.choose else b, fun x hx => ?_⟩
    have h : ∃ y ∈ Good (n + 1), x ≤ y := hstep n x hx
    simp only [dif_pos h]
    exact ⟨h.choose_spec.1, h.choose_spec.2⟩
  choose F hF using hstep'
  obtain ⟨x₀, hx₀⟩ := hGoodne 0
  set g : ℕ → α := fun n => Nat.rec x₀ (fun m y => F m y) n with hgDef
  have hgsucc : ∀ n, g (n + 1) = F n (g n) := fun _ => rfl
  have hgmem : ∀ n, g n ∈ Good n := by
    intro n
    induction n with
    | zero => exact hx₀
    | succ n ih => rw [hgsucc n]; exact (hF n (g n) ih).1
  exact ⟨g, fun n => (hgmem n).1, monotone_nat_of_le_succ fun n =>
    (hgsucc n) ▸ (hF n (g n) (hgmem n)).2⟩

end Main

end Konig

/-! ## Step 4, part 1: the stages of `U`, and the chain inside an infinite `U ^∞(A)`

> Since the base of `D` has property M each set `Uⁿ(A)` is finite and contains
> elements which are not in `Uⁿ⁻¹(A)` already. So for each `n ∈ ℕ` we have the
> finite nonempty set `Bₙ = Uⁿ(A) \ Uⁿ⁻¹(A)`. Each element of `Bₙ` is above some
> element of `Bₙ₋₁` because otherwise it would belong to `Uⁿ⁻¹(A)` already.

`mubDiff A u n` is Jung's `Bₙ₊₁`, indexed from `0` so that no truncated
subtraction appears. -/

section Stages

variable [PartialOrder α] {A N u : Set α}

/-- **Property M preserves finiteness under one application of `U`.** A finite
`N ⊆ A` has finitely many finite subsets, and property M gives each of them
finitely many minimal upper bounds. -/
theorem mubStep_finite
    (hM : ∀ v : Set α, v ⊆ A → v.Finite → (minimalUpperBounds A v).Finite)
    (hN : N.Finite) (hNA : N ⊆ A) : (mubStep A N).Finite := by
  refine hN.union (Set.Finite.subset (hN.finite_subsets.biUnion
    fun v hv => hM v (Set.Subset.trans hv hNA) (hN.subset hv)) ?_)
  rintro m ⟨v, hvN, _, hmv⟩
  exact Set.mem_iUnion₂.mpr ⟨v, hvN, hmv⟩

/-- Every stage `Uⁿ(u)` of a finite `u` is finite, under property M. -/
theorem mubIter_finite
    (hM : ∀ v : Set α, v ⊆ A → v.Finite → (minimalUpperBounds A v).Finite)
    (hu : u.Finite) (huA : u ⊆ A) : ∀ n, (mubIter A u n).Finite
  | 0 => hu
  | n + 1 => mubStep_finite hM (mubIter_finite hM hu huA n) (mubIter_subset huA n)

/-- Jung's `Bₙ₊₁ = Uⁿ⁺¹(u) \ Uⁿ(u)`: the elements the `n`-th application of `U`
adds. -/
def mubDiff (A u : Set α) (n : ℕ) : Set α := mubIter A u (n + 1) \ mubIter A u n

theorem mubDiff_subset_mubClosure {n : ℕ} : mubDiff A u n ⊆ mubClosure A u :=
  fun _ hx => mubIter_subset_mubClosure A u (n + 1) hx.1

theorem mubDiff_finite (hstage : ∀ n, (mubIter A u n).Finite) (n : ℕ) :
    (mubDiff A u n).Finite := (hstage (n + 1)).subset fun _ hx => hx.1

/-- **A stage that adds nothing has stabilized.** If `Uⁿ⁺¹(u) = Uⁿ(u)` then every
later stage is contained in `Uⁿ(u)`, so `U ^∞(u)` is finite. Contrapositively, an
infinite mub-closure makes every difference `Bₙ₊₁` nonempty. -/
theorem mubDiff_nonempty (hstage : ∀ n, (mubIter A u n).Finite)
    (hinf : (mubClosure A u).Infinite) (n : ℕ) : (mubDiff A u n).Nonempty := by
  by_contra hemp
  rw [Set.not_nonempty_iff_eq_empty] at hemp
  have hsub : mubIter A u (n + 1) ⊆ mubIter A u n := fun x hx => by
    by_contra hxn
    exact Set.eq_empty_iff_forall_notMem.mp hemp x ⟨hx, hxn⟩
  have key : ∀ m, mubIter A u m ⊆ mubIter A u n := by
    intro m
    induction m with
    | zero => exact mubIter_mono A u (Nat.zero_le n)
    | succ m ih => exact (mubStep_mono ih).trans hsub
  exact hinf ((hstage n).subset (Set.iUnion_subset key))

/-- **Jung's descent step.** A member of `Bₙ₊₂` lies above a member of `Bₙ₊₁`: it
is a minimal upper bound of a finite `v ⊆ Uⁿ⁺¹(u)`, and if every member of `v`
were already in `Uⁿ(u)` then it would itself lie in `Uⁿ⁺¹(u)`. -/
theorem exists_mem_mubDiff_le (n : ℕ) {x : α} (hx : x ∈ mubDiff A u (n + 1)) :
    ∃ y ∈ mubDiff A u n, y ≤ x := by
  obtain ⟨hx1, hx2⟩ := hx
  rcases hx1 with h | ⟨v, hvN, hvfin, hmv⟩
  · exact absurd h hx2
  · by_contra hno
    refine hx2 (Or.inr ⟨v, fun y hy => ?_, hvfin, hmv⟩)
    by_contra hyn
    exact hno ⟨y, ⟨hvN hy, hyn⟩, (minimalUpperBounds_subset hmv).2 hy⟩

/-- Consecutive differences are disjoint, which turns the monotone transversal
König's lemma produces into a **strictly** ascending one. -/
theorem mubDiff_ne {n : ℕ} {x y : α} (hx : x ∈ mubDiff A u n)
    (hy : y ∈ mubDiff A u (n + 1)) : x ≠ y := fun h => hy.2 (h ▸ hx.1)

/-- **The chain of Jung's Lemma 2.2.** Under property M an infinite `U ^∞(u)`
contains an infinite strictly ascending sequence.

This is where Jung invokes Rado's Selection Theorem; `exists_monotone_seq` — König's
lemma graded by `ℕ` — is applied instead, to the family `Bₙ₊₁ = Uⁿ⁺¹(u) \ Uⁿ(u)`.
Its four hypotheses are the four facts above; the union of the differences is
infinite because it misses only `u`, which is finite. -/
theorem exists_strictMono_mem_mubClosure
    (hM : ∀ v : Set α, v ⊆ A → v.Finite → (minimalUpperBounds A v).Finite)
    (hu : u.Finite) (huA : u ⊆ A) (hinf : (mubClosure A u).Infinite) :
    ∃ x : ℕ → α, (∀ n, x n ∈ mubClosure A u) ∧ StrictMono x := by
  classical
  have hstage := mubIter_finite hM hu huA
  have hsub : mubClosure A u ⊆ u ∪ ⋃ n, mubDiff A u n := by
    intro z hz
    by_cases h0 : z ∈ mubIter A u 0
    · exact Or.inl h0
    · have hex : ∃ m, z ∈ mubIter A u m := Set.mem_iUnion.mp hz
      have hzk : z ∈ mubIter A u (Nat.find hex) := Nat.find_spec hex
      have hkpos : Nat.find hex ≠ 0 := fun h => h0 (h ▸ hzk)
      obtain ⟨j, hj⟩ : ∃ j, Nat.find hex = j + 1 := ⟨Nat.find hex - 1, by omega⟩
      exact Or.inr (Set.mem_iUnion.mpr ⟨j, hj ▸ hzk, Nat.find_min hex (by omega)⟩)
  have hUinf : (⋃ n, mubDiff A u n).Infinite := fun hfinU =>
    hinf (Set.Finite.subset (hu.union hfinU) hsub)
  obtain ⟨x, hxmem, hxmono⟩ := exists_monotone_seq (B := mubDiff A u)
    (mubDiff_finite hstage) (mubDiff_nonempty hstage hinf) hUinf
    fun n _ hx => exists_mem_mubDiff_le n hx
  exact ⟨x, fun n => mubDiff_subset_mubClosure (hxmem n),
    strictMono_nat_of_lt_succ fun n =>
      lt_of_le_of_ne (hxmono (Nat.le_succ n)) (mubDiff_ne (hxmem n) (hxmem (n + 1)))⟩

end Stages

end ScottDomains.JungFinite
