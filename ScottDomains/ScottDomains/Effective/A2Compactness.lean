import ScottDomains.Effective.FunctionSpace
import ScottDomains.Effective.A1FlatRecursive
import ScottDomains.Effective.A3StrictRecursive

/-!
# r0047, agent2: the boundedness of a finite set of step functions

r0046's agent1 measured `Effective.StepFunctionsDecidable`,
`Effective.Theorem7ArrowRecursive` and `Effective.Theorem7StrictRecursive` as
blocked on a single item — item 3 of the table in `Effective/FunctionSpace.lean`:

> a decision procedure for `IsCompactElement (ofPairs Q)` — the boundedness test
> `scottHomEnum` performs classically.

with items 2 and 4 of the same table reducing to it. This module proves the
domain theory that item stands for, and measures the one place where the
development's own transcription of the test does **not** coincide with it.

## What is proved

Everything below is stated for the ambient structures the claims carry — no
added instance binder, no `Decidable` hypothesis.

Part 1, general facts about a bounded complete cpo, none of which the
development had:

| # | Result | Content |
| -- | ------ | ------- |
| 1 | `isCompactElement_of_isLUB_finite` | a least upper bound of a **finite** set of compacts is compact. Needs no completeness at all — the finite-subset bound `exists_mem_ub_of_finite` inside a directed set is the whole proof |
| 2 | `isNormalIn_compacts_iff` | `N ◁ K(D)` **iff** `⊥ ∈ N` and `N` is closed under those binary least upper bounds that exist. This is item 4 of the table, in general form |
| 3 | `isNormalIn_joinClosure`, `finite_joinClosure` | every finite set of compacts lies in a **finite** normal subposet, its join closure |
| 4 | `bddAbove_iff_exists_mem_upperBounds` | inside a normal subposet, boundedness of a finite subset is witnessed **in that subposet** |
| 5 | `bddAbove_iff_exists_normal` | so boundedness of a finite set of compacts is equivalent to an existential over finite normal subposets: §3.2's condition 2 decides it, by a search that always terminates |

Row 5 is the shape the recursion theory needs. It says the boundedness test is
not an extra assumption on `d` — it is condition 2 of `d` plus condition 1 of
`d`, run under an unbounded search that row 3 proves terminates.

Part 2, the step functions, at `P` a finite set of compact pairs:

| # | Result | Content |
| -- | ------ | ------- |
| 6 | `bddAbove_stepsOf_iff` | **the fact.** `stepsOf P` is bounded above in `D → E` **iff** `Consistent P`: for every `S ⊆ P`, if the sources of `S` are bounded in `D` then the values of `S` are bounded in `E` |
| 7 | `ofPairs_apply` | `ofPairs P` evaluated pointwise: `(ofPairs P) x = ⨆{b | (a,b) ∈ P, a ⊑ x}`. This is item 2 of the table, which the file called "missing, and it is item 3 in disguise" |
| 8 | `ofPairs_le_iff` | `ofPairs P ≤ g ↔ ∀ (a,b) ∈ P, b ≤ g a`. Item 1, which the file called "half available" |
| 9 | `ofPairs_le_ofPairs_iff` | items 1 and 2 composed: the order on the enumeration, as a finite condition on the two index sets |
| 10 | `isCompactElement_ofPairs_of_consistent` | consistency implies the guard `scottHomEnum` tests |

## What is refuted: the guard is not the boundedness test

Row 10 has **no converse**. `ScottHom`'s `sSup` is total, and on a set that is
not bounded above it returns a value no axiom constrains — `CompletePartialOrder`
pins `sSup` down on directed sets only, and `BoundedComplete` on bounded sets
only. So `ofPairs P` on an inconsistent `P` is a junk value, and a junk value can
be compact.

`not_consistent_badPairs` and `isCompactElement_ofPairs_badPairs` exhibit this at
`α = β = N⊥` with two step functions that have no upper bound whatever, and whose
`ofPairs` is nonetheless a compact step function. `R45.Agent1.natBotPresentation`
is `IsRecursive`, so the counterexample sits inside the hypotheses
`StepFunctionsDecidable` is stated under.

The consequence is stated as `not_forall_isCompactElement_ofPairs_iff_bddAbove`:
**no theorem of the form `IsCompactElement (ofPairs P) ↔ (a condition on `P`, `d`
and `e`)` is available**, because the left side depends on the ambient `SupSet`
instance's behaviour off the bounded sets, which an effective presentation does
not see. `Effective.scottHomEnum` tests the left side. That is where
`StepFunctionsDecidable` stands, and it is a defect in this development's
transcription of the enumeration, not in Gunter & Scott's Theorem 7 — the paper's
`scottHomEnum` is indexed by the finite *joins that exist*, which is row 6.

## What the refutation does not block

`Effective.Theorem7ArrowRecursive` and `Effective.Theorem7StrictRecursive` ask
for **some** `f : EffectivePresentation (…)` with `IsRecursive f`; neither names
`Effective.scottHom d e`. Only `Effective.StepFunctionsDecidable` does. So the
defect is confined to one of the three claims, and part 4 routes the other two
around it: `consistentEnum` is the same enumeration with `Consistent` in place of
the compactness test, `scottHomC` and `strictHomC` are the resulting effective
presentations, and

* `theorem_7_arrowRecursive_of_scottHomC`
* `theorem_7_strictRecursive_of_strictHomC`

reduce the two theorems to `IsRecursive (scottHomC d e)` and `IsRecursive
(strictHomC d e)` — recursion theory over a guard that `d` and `e` determine.
Both reductions carry exactly the claims' own binder lists.

## Status of the three claims

Reduced, not discharged. No theorem in this module concludes any of the three,
and none is stated with an added instance binder. What remains for all three is
recursion theory: the `Primrec` facts for the `Denumerable (Finset (ℕ × ℕ))`
coding (item 5 of the table, "missing but known feasible"), and the μ-search
`bddAbove_iff_exists_normal` licenses. For `StepFunctionsDecidable` there is the
further, and different, problem that its subject's guard is not determined by its
hypotheses.
-/

namespace ScottDomains.R47.Agent2

open ScottDomains ScottDomains.Effective

/-! ## 0. A finite subset of a directed set is bounded inside it

Used four times below and stated nowhere in Mathlib: `DirectedOn` gives an upper
bound for *pairs*, and every argument here needs one for a finite set. -/

/-- A finite subset of a nonempty directed set has an upper bound **in the set**.
Induction on the finite set; the empty case is where nonemptiness is spent. -/
theorem exists_mem_ub_of_finite {γ : Type*} [Preorder γ] {d : Set γ}
    (hne : d.Nonempty) (hd : DirectedOn (· ≤ ·) d) {F : Set γ} (hfin : F.Finite) :
    F ⊆ d → ∃ z ∈ d, ∀ y ∈ F, y ≤ z := by
  induction F, hfin using Set.Finite.induction_on with
  | empty =>
      intro _
      obtain ⟨z, hz⟩ := hne
      exact ⟨z, hz, by simp⟩
  | @insert a S _ _ ih =>
      intro hsub
      obtain ⟨z, hzd, hz⟩ := ih fun x hx => hsub (Set.mem_insert_of_mem _ hx)
      obtain ⟨w, hwd, haw, hzw⟩ := hd a (hsub (Set.mem_insert _ _)) z hzd
      refine ⟨w, hwd, fun y hy => ?_⟩
      rcases Set.mem_insert_iff.mp hy with rfl | hy
      · exact haw
      · exact (hz y hy).trans hzw

/-! ## 1. Bounded complete cpos: normality, join closure, and boundedness -/

section General

variable {γ : Type*} [CompletePartialOrder γ]

/-- **A least upper bound of a finite set of compact elements is compact.**

Note what is *not* assumed: no bounded completeness, no algebraicity, no lattice
structure. The proof is the finite-set version of `isCompactElement_of_isLUB_pair`
and runs directly: each member of `S` is caught inside the directed set, and
`exists_mem_ub_of_finite` catches all of them at once. -/
theorem isCompactElement_of_isLUB_finite {S : Set γ} (hfin : S.Finite)
    (hS : ∀ x ∈ S, IsCompactElement x) {c : γ} (hc : IsLUB S c) : IsCompactElement c := by
  intro s u hne hd hlub hcu
  have hchoice : ∀ x ∈ S, ∃ y ∈ s, x ≤ y := fun x hx =>
    hS x hx s u hne hd hlub ((hc.1 hx).trans hcu)
  choose! φ hφ using hchoice
  obtain ⟨z, hzs, hz⟩ :=
    exists_mem_ub_of_finite hne hd (hfin.image φ) (by rintro _ ⟨x, hx, rfl⟩; exact (hφ x hx).1)
  exact ⟨z, hzs, hc.2 fun x hx => ((hφ x hx).2).trans (hz _ ⟨x, hx, rfl⟩)⟩

/-- **Normality in `K(D)`, for a bounded complete cpo, is closure under joins.**

`N ◁ K(D)` says every `N ∩ ↓x` is nonempty and directed. Over a bounded complete
cpo that collapses to two conditions on `N` alone: it contains `⊥`, and whenever
two of its members have a least upper bound, that bound is again in `N`.

The forward direction takes `x` to be the join itself, which is compact by
`isCompactElement_of_isLUB_pair`; directedness then produces a member of `N`
between the pair and its join, which must *be* the join. The backward direction
is where bounded completeness is spent: a pair below a common `x` is bounded, so
its join exists.

This is item 4 of `Effective/FunctionSpace.lean`'s table — "a characterization of
`IsNormalIn` for a finite set of compact functions" — in the general form, of
which the function space is the instance. `R45.Agent1.isNormalIn_compacts_flat_iff`
is the flat-cpo case, where no pair of distinct non-`⊥` elements is bounded and
the second condition is vacuous. -/
theorem isNormalIn_compacts_iff [BoundedComplete γ] {N : Set γ} :
    N ◁ compacts γ ↔ N ⊆ compacts γ ∧ (⊥ : γ) ∈ N ∧
      ∀ a ∈ N, ∀ b ∈ N, ∀ c : γ, IsLUB ({a, b} : Set γ) c → c ∈ N := by
  constructor
  · intro h
    refine ⟨h.subset, h.bot_mem isCompactElement_bot, ?_⟩
    intro a ha b hb c hc
    have hcc : IsCompactElement c :=
      isCompactElement_of_isLUB_pair (h.subset ha) (h.subset hb) hc
    obtain ⟨w, ⟨hwN, hwc⟩, haw, hbw⟩ :=
      h.directedOn hcc a ⟨ha, Set.mem_Iic.mpr (hc.1 (Set.mem_insert _ _))⟩
        b ⟨hb, Set.mem_Iic.mpr (hc.1 (Set.mem_insert_of_mem _ rfl))⟩
    have hcw : c ≤ w := hc.2 (by rintro z hz
                                 rcases Set.mem_insert_iff.mp hz with rfl | rfl
                                 · exact haw
                                 · exact hbw)
    rwa [le_antisymm (Set.mem_Iic.mp hwc) hcw] at hwN
  · rintro ⟨hsub, hbot, hclosed⟩
    refine ⟨hsub, fun x _ => ⟨⟨⊥, hbot, Set.mem_Iic.mpr bot_le⟩, ?_⟩⟩
    rintro a ⟨haN, hax⟩ b ⟨hbN, hbx⟩
    have hbdd : BddAbove ({a, b} : Set γ) := by
      refine ⟨x, fun z hz => ?_⟩
      rcases Set.mem_insert_iff.mp hz with rfl | rfl
      · exact Set.mem_Iic.mp hax
      · exact Set.mem_Iic.mp hbx
    have hlub := isLUB_sSup_of_bddAbove hbdd
    refine ⟨sSup ({a, b} : Set γ), ⟨hclosed a haN b hbN _ hlub, Set.mem_Iic.mpr (hlub.2 ?_)⟩,
      hlub.1 (Set.mem_insert _ _), hlub.1 (Set.mem_insert_of_mem _ rfl)⟩
    rintro z hz
    rcases Set.mem_insert_iff.mp hz with rfl | rfl
    · exact Set.mem_Iic.mp hax
    · exact Set.mem_Iic.mp hbx

/-- `sSup` of a singleton, over a bare `CompletePartialOrder`. A singleton is
directed, so the total `sSup` takes its intended value there; Mathlib states this
only for `CompleteLattice`. -/
theorem sSup_singleton_cpo (a : γ) : sSup ({a} : Set γ) = a := by
  refine (DirectedOn.isLUB_sSup ?_).unique isLUB_singleton
  rintro x hx y hy
  rw [Set.mem_singleton_iff] at hx hy
  exact ⟨a, rfl, le_of_eq hx, le_of_eq hy⟩

/-- The **join closure** of a set: every least upper bound of a subset of it. In
a bounded complete cpo this is the normal subposet generated by the set, and for
a finite set it is finite — at most one element per subset. -/
def joinClosure (S : Set γ) : Set γ := {c | ∃ T ⊆ S, IsLUB T c}

theorem subset_joinClosure (S : Set γ) : S ⊆ joinClosure S :=
  fun a ha => ⟨{a}, Set.singleton_subset_iff.mpr ha, isLUB_singleton⟩

theorem bot_mem_joinClosure (S : Set γ) : (⊥ : γ) ∈ joinClosure S :=
  ⟨∅, Set.empty_subset _, isLUB_empty⟩

/-- **The join closure of a finite set is finite.** Each member is the join of a
subset, and a join is unique, so the closure is the image of the (finite) power
set under `sSup`. -/
theorem finite_joinClosure [BoundedComplete γ] {S : Set γ} (hS : S.Finite) :
    (joinClosure S).Finite := by
  refine Set.Finite.subset (hS.finite_subsets.image sSup) ?_
  rintro c ⟨T, hTS, hT⟩
  exact ⟨T, hTS, (isLUB_sSup_of_bddAbove ⟨c, hT.1⟩).unique hT⟩

/-- The join closure of a finite set of compacts consists of compacts, by
`isCompactElement_of_isLUB_finite`. -/
theorem joinClosure_subset_compacts {S : Set γ} (hS : S.Finite) (hcpt : S ⊆ compacts γ) :
    joinClosure S ⊆ compacts γ := by
  rintro c ⟨T, hTS, hT⟩
  exact isCompactElement_of_isLUB_finite (hS.subset hTS) (fun x hx => hcpt (hTS hx)) hT

/-- **Every finite set of compacts lies in a finite normal subposet.** The
witness is its join closure: closure under existing binary joins holds because
the join of two joins is the join of the union.

This is the fact that turns §3.2's condition 2 from a test one can run into a
test one can *search with*: the search for a normal superset always succeeds. -/
theorem isNormalIn_joinClosure [BoundedComplete γ] {S : Set γ} (hS : S.Finite)
    (hcpt : S ⊆ compacts γ) : joinClosure S ◁ compacts γ := by
  refine isNormalIn_compacts_iff.mpr
    ⟨joinClosure_subset_compacts hS hcpt, bot_mem_joinClosure S, ?_⟩
  rintro a ⟨T₁, hT₁, hA⟩ b ⟨T₂, hT₂, hB⟩ c hc
  refine ⟨T₁ ∪ T₂, Set.union_subset hT₁ hT₂, ⟨?_, ?_⟩⟩
  · rintro z (hz | hz)
    · exact (hA.1 hz).trans (hc.1 (Set.mem_insert _ _))
    · exact (hB.1 hz).trans (hc.1 (Set.mem_insert_of_mem _ rfl))
  · intro u hu
    refine hc.2 ?_
    rintro z hz
    rcases Set.mem_insert_iff.mp hz with rfl | rfl
    · exact hA.2 fun t ht => hu (Or.inl ht)
    · exact hB.2 fun t ht => hu (Or.inr ht)

/-- **Inside a normal subposet, boundedness is witnessed in the subposet.**

If `v ⊆ u` is finite and `u ◁ K(D)`, then `v` is bounded above in `D` exactly
when some member of `u` bounds it. The forward direction needs the join of `v` to
be *compact*, which `isCompactElement_of_isLUB_finite` supplies; normality is
then applied at that compact, and `exists_mem_ub_of_finite` extracts a single
member of `u` above all of `v`.

This is the step that makes the boundedness test finite: the search space for the
bound is `u`, not `K(D)`. -/
theorem bddAbove_iff_exists_mem_upperBounds [BoundedComplete γ] {u v : Set γ}
    (hu : u ◁ compacts γ) (hv : v ⊆ u) (hvfin : v.Finite) :
    BddAbove v ↔ ∃ b ∈ u, b ∈ upperBounds v := by
  constructor
  · intro hbdd
    have hlub : IsLUB v (sSup v) := isLUB_sSup_of_bddAbove hbdd
    have hcpt : IsCompactElement (sSup v) :=
      isCompactElement_of_isLUB_finite hvfin (fun x hx => hu.subset (hv hx)) hlub
    obtain ⟨z, hzmem, hz⟩ :=
      exists_mem_ub_of_finite (hu.nonempty hcpt) (hu.directedOn hcpt) hvfin
        (fun x hx => ⟨hv hx, Set.mem_Iic.mpr (hlub.1 hx)⟩)
    exact ⟨z, hzmem.1, fun y hy => hz y hy⟩
  · rintro ⟨b, _, hb⟩
    exact ⟨b, hb⟩

/-- **Boundedness of a finite set of compacts, as an existential over finite
normal subposets.** Composing the previous two: the closure supplies the normal
superset, and normality supplies the bound inside it.

The right-hand side is the shape §3.2's two conditions decide. Condition 2
recognizes the normal `u`; condition 1 tests `b ∈ upperBounds v`; the search over
`u` terminates because `isNormalIn_joinClosure` guarantees a witness exists. So
"is this finite set of compacts bounded?" is not an extra hypothesis on an
effective presentation — it is a consequence of the two the paper states. -/
theorem bddAbove_iff_exists_normal [BoundedComplete γ] {v : Set γ} (hvfin : v.Finite)
    (hcpt : v ⊆ compacts γ) :
    BddAbove v ↔ ∃ u : Set γ, u.Finite ∧ v ⊆ u ∧ u ◁ compacts γ ∧
      ∃ b ∈ u, b ∈ upperBounds v := by
  constructor
  · intro hbdd
    exact ⟨joinClosure v, finite_joinClosure hvfin, subset_joinClosure v,
      isNormalIn_joinClosure hvfin hcpt,
      (bddAbove_iff_exists_mem_upperBounds (isNormalIn_joinClosure hvfin hcpt)
        (subset_joinClosure v) hvfin).mp hbdd⟩
  · rintro ⟨_, _, _, _, b, _, hb⟩
    exact ⟨b, hb⟩

end General

/-! ## 2. Step functions: when is a finite set of them bounded above? -/

section StepFunctions

variable {α β : Type*} [CompletePartialOrder α] [CompletePartialOrder β] [BoundedComplete β]

/-- The pairs of `P` whose source lies below `x`. `ofPairs P` evaluated at `x` is
the join of their values — see `ofPairs_apply`. -/
def belowSet (P : Set (α × β)) (x : α) : Set (α × β) := {p ∈ P | p.1 ≤ x}

omit [CompletePartialOrder β] [BoundedComplete β] in
theorem mem_belowSet {P : Set (α × β)} {x : α} {p : α × β} :
    p ∈ belowSet P x ↔ p ∈ P ∧ p.1 ≤ x := Iff.rfl

omit [CompletePartialOrder β] [BoundedComplete β] in
theorem belowSet_subset (P : Set (α × β)) (x : α) : belowSet P x ⊆ P := fun _ hp => hp.1

/-- **The consistency condition on a set of compact pairs.** For every subset
whose sources are bounded in `D`, the values are bounded in `E`.

This is the condition Gunter & Scott's "the poset of step functions" is cut out
by, and `bddAbove_stepsOf_iff` proves it is exactly boundedness of the step
functions in `D → E`. It is a condition on `P`, `D` and `E` alone — no reference
to the function space and none to `sSup`. -/
def Consistent (P : Set (α × β)) : Prop :=
  ∀ S ⊆ P, BddAbove (Prod.fst '' S) → BddAbove (Prod.snd '' S)

omit [BoundedComplete β] in
/-- `stepsOf P` is finite when `P` is: a step function is determined by its
underlying function, and there is one underlying function per pair. -/
theorem finite_stepsOf {P : Set (α × β)} (hP : P.Finite) :
    (ScottHom.stepsOf P).Finite := by
  refine Set.Finite.of_finite_image (f := fun g : ScottHom α β => ⇑g) ?_ ?_
  · refine Set.Finite.subset (hP.image fun p => ScottHom.stepFun p.1 p.2) ?_
    rintro _ ⟨g, ⟨p, hp, hstep⟩, rfl⟩
    exact ⟨p, hp, hstep.2.2.symm⟩
  · intro g _ h _ hgh
    exact DFunLike.coe_injective hgh

/-- The candidate upper bound, as a function: `x ↦ ⨆{b | (a,b) ∈ P, a ⊑ x}`. -/
noncomputable def pairSup (P : Set (α × β)) (x : α) : β := sSup (Prod.snd '' belowSet P x)

omit [BoundedComplete β] in
theorem bddAbove_snd_belowSet {P : Set (α × β)} (hc : Consistent P) (x : α) :
    BddAbove (Prod.snd '' belowSet P x) :=
  hc (belowSet P x) (belowSet_subset P x) ⟨x, by rintro _ ⟨p, hp, rfl⟩; exact hp.2⟩

theorem isLUB_pairSup {P : Set (α × β)} (hc : Consistent P) (x : α) :
    IsLUB (Prod.snd '' belowSet P x) (pairSup P x) :=
  isLUB_sSup_of_bddAbove (bddAbove_snd_belowSet hc x)

theorem monotone_pairSup {P : Set (α × β)} (hc : Consistent P) : Monotone (pairSup P) := by
  intro x y hxy
  refine (isLUB_pairSup hc x).2 fun b hb => (isLUB_pairSup hc y).1 ?_
  obtain ⟨p, hp, rfl⟩ := hb
  exact ⟨p, ⟨hp.1, hp.2.trans hxy⟩, rfl⟩

/-- **The candidate upper bound is Scott continuous.** Compactness of the sources
is what makes it so, and finiteness of `P` is what lets all of them be caught in
one member of the directed set: `belowSet P (⨆d) ⊆ belowSet P z` for a single
`z ∈ d`, so the value at `⨆d` is already attained at `z`. -/
theorem scottContinuous_pairSup {P : Set (α × β)} (hP : P.Finite)
    (hcpt : ∀ p ∈ P, IsCompactElement p.1) (hc : Consistent P) :
    ScottContinuous (pairSup P) := by
  intro d hne hd u hu
  refine ⟨?_, fun w hw => ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact monotone_pairSup hc (hu.1 hx)
  · have hchoice : ∀ p ∈ belowSet P u, ∃ y ∈ d, p.1 ≤ y := fun p hp =>
      hcpt p hp.1 d u hne hd hu hp.2
    choose! ψ hψ using hchoice
    obtain ⟨z, hzd, hz⟩ :=
      exists_mem_ub_of_finite hne hd ((hP.subset (belowSet_subset P u)).image ψ)
        (by rintro _ ⟨p, hp, rfl⟩; exact (hψ p hp).1)
    have hsub : belowSet P u ⊆ belowSet P z := fun p hp =>
      ⟨hp.1, (hψ p hp).2.trans (hz _ ⟨p, hp, rfl⟩)⟩
    refine le_trans ?_ (hw ⟨z, hzd, rfl⟩)
    refine (isLUB_pairSup hc u).2 ?_
    rintro _ ⟨p, hp, rfl⟩
    exact (isLUB_pairSup hc z).1 ⟨p, hsub hp, rfl⟩

/-- The candidate upper bound as an element of `D → E`. -/
noncomputable def pairSupHom {P : Set (α × β)} (hP : P.Finite)
    (hcpt : ∀ p ∈ P, IsCompactElement p.1) (hc : Consistent P) : ScottHom α β :=
  ⟨pairSup P, scottContinuous_pairSup hP hcpt hc⟩

theorem pairSupHom_apply {P : Set (α × β)} (hP : P.Finite)
    (hcpt : ∀ p ∈ P, IsCompactElement p.1) (hc : Consistent P) (x : α) :
    pairSupHom hP hcpt hc x = pairSup P x := rfl

/-- **The candidate is the least upper bound of the step functions.** Being an
upper bound is a pointwise check against `stepFun`; being least is
`ScottHom.step_le_iff` together with monotonicity of the competitor. -/
theorem isLUB_stepsOf_pairSupHom {P : Set (α × β)} (hP : P.Finite)
    (hcptP : P ⊆ compacts α ×ˢ compacts β) (hc : Consistent P) :
    IsLUB (ScottHom.stepsOf P) (pairSupHom hP (fun _ hp => (hcptP hp).1) hc) := by
  constructor
  · rintro g ⟨p, hp, hstep⟩ x
    show g x ≤ pairSup P x
    rw [show g x = ScottHom.stepFun p.1 p.2 x from congrFun hstep.2.2 x]
    by_cases hle : p.1 ≤ x
    · rw [ScottHom.stepFun_of_le hle]
      exact (isLUB_pairSup hc x).1 ⟨p, ⟨hp, hle⟩, rfl⟩
    · rw [ScottHom.stepFun_of_not_le hle]
      exact bot_le
  · intro f hf x
    show pairSup P x ≤ f x
    refine (isLUB_pairSup hc x).2 ?_
    rintro _ ⟨p, hp, rfl⟩
    have hmem : ScottHom.step (hcptP hp.1).1 p.2 ∈ ScottHom.stepsOf P :=
      ⟨p, hp.1, ⟨(hcptP hp.1).1, (hcptP hp.1).2, rfl⟩⟩
    exact ((ScottHom.step_le_iff _).mp (hf hmem)).trans (f.monotone hp.2)

/-- **The fact.** A finite set of step functions named by compact pairs is
bounded above in `D → E` **exactly when** `P` is consistent: every subset of `P`
whose sources are bounded in `D` has its values bounded in `E`.

Forward, an upper bound `f` supplies the bound `f x` for the values, where `x`
bounds the sources — this is `ScottHom.step_le_iff` and monotonicity, and nothing
else. Backward, `pairSupHom` is the bound.

This is item 3 of `Effective/FunctionSpace.lean`'s table, in the form the paper
uses it: boundedness in the function space is reduced to boundedness in `D` and
in `E`, which `bddAbove_iff_exists_normal` shows §3.2's own two conditions
decide. -/
theorem bddAbove_stepsOf_iff {P : Set (α × β)} (hP : P.Finite)
    (hcptP : P ⊆ compacts α ×ˢ compacts β) :
    BddAbove (ScottHom.stepsOf P) ↔ Consistent P := by
  constructor
  · rintro ⟨f, hf⟩ S hSP ⟨x, hx⟩
    refine ⟨f x, ?_⟩
    rintro _ ⟨p, hp, rfl⟩
    have hmem : ScottHom.step (hcptP (hSP hp)).1 p.2 ∈ ScottHom.stepsOf P :=
      ⟨p, hSP hp, ⟨(hcptP (hSP hp)).1, (hcptP (hSP hp)).2, rfl⟩⟩
    exact ((ScottHom.step_le_iff _).mp (hf hmem)).trans (f.monotone (hx ⟨p, hp, rfl⟩))
  · intro hc
    exact ⟨_, (isLUB_stepsOf_pairSupHom hP hcptP hc).1⟩

/-- On a consistent `P`, `ofPairs P` is the least upper bound of the step
functions it names — the total `sSup` takes its intended value. -/
theorem isLUB_stepsOf_ofPairs {P : Set (α × β)} (hP : P.Finite)
    (hcptP : P ⊆ compacts α ×ˢ compacts β) (hc : Consistent P) :
    IsLUB (ScottHom.stepsOf P) (ScottHom.ofPairs P) :=
  isLUB_sSup_of_bddAbove ((bddAbove_stepsOf_iff hP hcptP).mpr hc)

/-- **`ofPairs` evaluated pointwise**: `(ofPairs P) x = ⨆{b | (a,b) ∈ P, a ⊑ x}`.

This is item 2 of the table, which `Effective/FunctionSpace.lean` records as
"missing, and it is item 3 in disguise: `sSup` on `ScottHom` is pointwise only on
directed sets, and `stepsOf Q` is not directed". Consistency replaces
directedness: `pairSupHom` *is* the least upper bound, and it is pointwise by
construction. -/
theorem ofPairs_apply {P : Set (α × β)} (hP : P.Finite)
    (hcptP : P ⊆ compacts α ×ˢ compacts β) (hc : Consistent P) (x : α) :
    ScottHom.ofPairs P x = sSup (Prod.snd '' belowSet P x) := by
  have h := (isLUB_stepsOf_ofPairs hP hcptP hc).unique (isLUB_stepsOf_pairSupHom hP hcptP hc)
  rw [h]
  rfl

/-- **`ofPairs P ≤ g` is a finite condition.** Item 1 of the table, which the file
calls "half available": `ScottHom.step_le_iff` gives one direction and leastness
of `ofPairs P` the other. -/
theorem ofPairs_le_iff {P : Set (α × β)} (hP : P.Finite)
    (hcptP : P ⊆ compacts α ×ˢ compacts β) (hc : Consistent P) {g : ScottHom α β} :
    ScottHom.ofPairs P ≤ g ↔ ∀ p ∈ P, p.2 ≤ g p.1 := by
  constructor
  · intro h p hp
    have hmem : ScottHom.step (hcptP hp).1 p.2 ∈ ScottHom.stepsOf P :=
      ⟨p, hp, ⟨(hcptP hp).1, (hcptP hp).2, rfl⟩⟩
    exact (ScottHom.step_le_iff _).mp (((isLUB_stepsOf_ofPairs hP hcptP hc).1 hmem).trans h)
  · intro h
    refine (isLUB_stepsOf_ofPairs hP hcptP hc).2 ?_
    rintro f ⟨p, hp, hstep⟩ x
    show f x ≤ g x
    rw [show f x = ScottHom.stepFun p.1 p.2 x from congrFun hstep.2.2 x]
    by_cases hle : p.1 ≤ x
    · rw [ScottHom.stepFun_of_le hle]
      exact (h p hp).trans (g.monotone hle)
    · rw [ScottHom.stepFun_of_not_le hle]
      exact bot_le

/-- **The order on the enumeration, as a condition on the two index sets.** Items
1 and 2 composed: `ofPairs P ≤ ofPairs Q` holds exactly when each value of `P` is
below the join of the values of `Q` whose sources lie below the corresponding
source of `P`.

Every quantifier on the right ranges over `P` and `Q`, which are finite, and the
`sSup` is a join in `E` of a finite set of compacts. -/
theorem ofPairs_le_ofPairs_iff {P Q : Set (α × β)} (hP : P.Finite) (hQ : Q.Finite)
    (hcptP : P ⊆ compacts α ×ˢ compacts β) (hcptQ : Q ⊆ compacts α ×ˢ compacts β)
    (hcP : Consistent P) (hcQ : Consistent Q) :
    ScottHom.ofPairs P ≤ ScottHom.ofPairs Q ↔
      ∀ p ∈ P, p.2 ≤ sSup (Prod.snd '' belowSet Q p.1) := by
  rw [ofPairs_le_iff hP hcptP hcP]
  exact forall₂_congr fun p _ => by rw [ofPairs_apply hQ hcptQ hcQ]

/-- **Consistency implies the guard `scottHomEnum` tests.** `ofPairs P` is then a
least upper bound of a finite set of compact step functions, so
`isCompactElement_of_isLUB_finite` applies.

There is no converse; see `not_forall_isCompactElement_ofPairs_iff_bddAbove`. -/
theorem isCompactElement_ofPairs_of_consistent {P : Set (α × β)} (hP : P.Finite)
    (hcptP : P ⊆ compacts α ×ˢ compacts β) (hc : Consistent P) :
    IsCompactElement (ScottHom.ofPairs P) := by
  refine isCompactElement_of_isLUB_finite (finite_stepsOf hP) ?_
    (isLUB_stepsOf_ofPairs hP hcptP hc)
  rintro g ⟨p, hp, hstep⟩
  have hg : g = ScottHom.step hstep.1 p.2 :=
    DFunLike.coe_injective (hstep.2.2.trans (ScottHom.coe_step hstep.1).symm)
  rw [hg]
  exact ScottHom.isCompactElement_step hstep.1 hstep.2.1

end StepFunctions

/-! ## 3. The guard `scottHomEnum` tests is **not** the boundedness test

`Effective.scottHomEnum` selects `ofPairs Q` when `IsCompactElement (ofPairs Q)`
and `⊥` otherwise. Section 2 shows consistency of `Q` — a condition on `D`, `E`
and `Q` alone — implies that guard. This section shows the implication does not
reverse, so the guard is strictly weaker than "the join exists".

The mechanism: `sSup` on `ScottHom` is total, `CompletePartialOrder` constrains
it on directed sets and `BoundedComplete` on bounded sets, and an inconsistent
`stepsOf Q` is neither. The value returned is therefore whatever the codomain's
`SupSet` instance happens to return off its constrained range — and it can be
compact.

The witness runs inside the hypotheses `Effective.StepFunctionsDecidable` is
stated under: `α = β = N⊥`, and `R45.Agent1.natBotPresentation` is `IsRecursive`
(`R45.Agent1.isRecursive_natBot`). -/

section FlatWitness

open ScottDomains.R45.Agent1

/-- Two compact pairs with the same source `up 0` and incomparable values. The
step functions they name have **no** upper bound in `N⊥ → N⊥`, because an upper
bound would have to send `up 0` above both `up 0` and `up 1`. -/
def badPairs : Set (Flat ℕ × Flat ℕ) :=
  {(Flat.up 0, Flat.up 0), (Flat.up 0, Flat.up 1)}

theorem finite_badPairs : badPairs.Finite := Set.Finite.insert _ (Set.finite_singleton _)

theorem badPairs_subset_compacts :
    badPairs ⊆ compacts (Flat ℕ) ×ˢ compacts (Flat ℕ) :=
  fun p _ => ⟨Flat.isCompactElement p.1, Flat.isCompactElement p.2⟩

/-- `badPairs` is inconsistent: its sources are the single element `up 0`, hence
bounded, while its values `up 0` and `up 1` are not. -/
theorem not_consistent_badPairs : ¬ Consistent badPairs := by
  intro h
  obtain ⟨u, hu⟩ := h badPairs subset_rfl ⟨Flat.up 0, by
    rintro _ ⟨p, hp, rfl⟩
    simp only [badPairs, Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl <;> exact le_rfl⟩
  have h0 : (Flat.up 0 : Flat ℕ) ≤ u := hu ⟨(Flat.up 0, Flat.up 0), by simp [badPairs], rfl⟩
  have h1 : (Flat.up 1 : Flat ℕ) ≤ u := hu ⟨(Flat.up 0, Flat.up 1), by simp [badPairs], rfl⟩
  rw [Flat.eq_of_up_le h0] at h1
  exact absurd (Flat.up_le_up_iff.mp h1) (by decide)

/-- …so the step functions it names are unbounded, by the characterization. -/
theorem not_bddAbove_stepsOf_badPairs : ¬ BddAbove (ScottHom.stepsOf badPairs) := fun h =>
  not_consistent_badPairs ((bddAbove_stepsOf_iff finite_badPairs badPairs_subset_compacts).mp h)

/-- The step functions `badPairs` names, listed. Two pairs, two step functions;
a step function is determined by its underlying function. -/
theorem stepsOf_badPairs :
    ScottHom.stepsOf badPairs =
      {ScottHom.step (Flat.isCompactElement (Flat.up 0 : Flat ℕ)) (Flat.up 0),
       ScottHom.step (Flat.isCompactElement (Flat.up 0 : Flat ℕ)) (Flat.up 1)} := by
  ext g
  constructor
  · rintro ⟨p, hp, hstep⟩
    simp only [badPairs, Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl
    · exact Or.inl (DFunLike.coe_injective (hstep.2.2.trans (ScottHom.coe_step _).symm))
    · exact Or.inr (DFunLike.coe_injective (hstep.2.2.trans (ScottHom.coe_step _).symm))
  · rintro (rfl | rfl)
    · exact ⟨(Flat.up 0, Flat.up 0), by simp [badPairs],
        ⟨Flat.isCompactElement _, Flat.isCompactElement _, rfl⟩⟩
    · exact ⟨(Flat.up 0, Flat.up 1), by simp [badPairs],
        ⟨Flat.isCompactElement _, Flat.isCompactElement _, rfl⟩⟩

/-- **`ofPairs badPairs` is a step function** — the junk value the total `sSup`
returns. At `x ⊒ up 0` the pointwise supremum is `sSup {up 0, up 1}`, which
`Flat.flatSup` answers with one of the two; everywhere else it is `⊥`. The
resulting function is `step (up 0) (sSup {up 0, up 1})`, which is continuous
whatever that choice is. -/
theorem ofPairs_badPairs :
    ScottHom.ofPairs badPairs =
      ScottHom.step (Flat.isCompactElement (Flat.up 0 : Flat ℕ))
        (sSup ({Flat.up 0, Flat.up 1} : Set (Flat ℕ))) := by
  have hfun : (fun x : Flat ℕ =>
      sSup ((fun f : ScottHom (Flat ℕ) (Flat ℕ) => f x) '' ScottHom.stepsOf badPairs))
      = ScottHom.stepFun (Flat.up 0) (sSup ({Flat.up 0, Flat.up 1} : Set (Flat ℕ))) := by
    funext x
    rw [stepsOf_badPairs, Set.image_insert_eq, Set.image_singleton]
    by_cases hle : (Flat.up 0 : Flat ℕ) ≤ x
    · rw [ScottHom.stepFun_of_le hle]
      simp only [ScottHom.coe_step, ScottHom.stepFun_of_le hle]
    · rw [ScottHom.stepFun_of_not_le hle]
      simp only [ScottHom.coe_step, ScottHom.stepFun_of_not_le hle, Set.pair_eq_singleton]
      exact sSup_singleton_cpo _
  have hcont : ScottContinuous (fun x : Flat ℕ =>
      sSup ((fun f : ScottHom (Flat ℕ) (Flat ℕ) => f x) '' ScottHom.stepsOf badPairs)) := by
    rw [hfun]
    exact ScottHom.scottContinuous_stepFun (Flat.isCompactElement _) _
  refine DFunLike.coe_injective (funext fun x => ?_)
  rw [show ScottHom.ofPairs badPairs = sSup (ScottHom.stepsOf badPairs) from rfl,
    ScottHom.coe_sSup_of_continuous hcont x, ScottHom.coe_step]
  exact congrFun hfun x

/-- **The guard holds on an unbounded index set.** `ofPairs badPairs` is a step
function with compact value, hence compact — while the step functions it is
supposed to join have no upper bound at all. -/
theorem isCompactElement_ofPairs_badPairs : IsCompactElement (ScottHom.ofPairs badPairs) := by
  rw [ofPairs_badPairs]
  exact ScottHom.isCompactElement_step _ (Flat.isCompactElement _)

/-- **The guard is not the boundedness test.** A closed refutation: no theorem
sends `IsCompactElement (ofPairs P)` to `BddAbove (stepsOf P)`, even for `P` a
finite set of compact pairs in a bounded complete domain.

The consequence for `Effective.StepFunctionsDecidable` is that its subject,
`Effective.scottHomEnum`, branches on a predicate that the two effective
presentations do not determine: on an inconsistent index set the value is read
off the codomain's `SupSet` instance outside the range `CompletePartialOrder` and
`BoundedComplete` constrain. Section 2 decides the guard on the consistent index
sets, from `d` and `e`; nothing decides it on the rest, because nothing about `d`
and `e` mentions the junk values. -/
theorem not_forall_isCompactElement_ofPairs_imp_bddAbove :
    ¬ ∀ {α β : Type} [CompletePartialOrder α] [Domain α] [CompletePartialOrder β]
        [Domain β] [BoundedComplete β] (P : Set (α × β)), P.Finite →
        P ⊆ compacts α ×ˢ compacts β → IsCompactElement (ScottHom.ofPairs P) →
        BddAbove (ScottHom.stepsOf P) := fun h =>
  not_bddAbove_stepsOf_badPairs
    (h badPairs finite_badPairs badPairs_subset_compacts isCompactElement_ofPairs_badPairs)

/-- The witness, located inside the enumeration the claim is about.
`{(1,1),(1,2)}` decodes under `R45.Agent1.natBotEnum` to `badPairs`, because
`natBotEnum 1 = up 0` and `natBotEnum 2 = up 1`. -/
theorem pairsOf_natBot_badPairs :
    Effective.pairsOf natBotPresentation natBotPresentation
      ({(1, 1), (1, 2)} : Finset (ℕ × ℕ)) = badPairs := by
  rw [Effective.pairsOf]
  simp [badPairs, natBotPresentation, Set.image_insert_eq]

/-- **The counterexample runs under hypotheses `StepFunctionsDecidable` grants.**
`R45.Agent1.natBotPresentation` is `IsRecursive` (`isRecursive_natBot`), so the
index set `{(1,1),(1,2)}` is one `Effective.scottHomEnum` must classify, and its
guard answers "compact" on an index set whose step functions are unbounded. -/
theorem natBot_guard_true_but_unbounded :
    IsCompactElement (ScottHom.ofPairs (Effective.pairsOf natBotPresentation
        natBotPresentation ({(1, 1), (1, 2)} : Finset (ℕ × ℕ)))) ∧
      ¬ BddAbove (ScottHom.stepsOf (Effective.pairsOf natBotPresentation
        natBotPresentation ({(1, 1), (1, 2)} : Finset (ℕ × ℕ)))) := by
  rw [pairsOf_natBot_badPairs]
  exact ⟨isCompactElement_ofPairs_badPairs, not_bddAbove_stepsOf_badPairs⟩

end FlatWitness

/-! ## 4. The enumeration of `K(D → E)` guarded by consistency

Section 3 shows `Effective.scottHomEnum`'s guard is not determined by `d` and
`e`. `Effective.Theorem7ArrowRecursive` does not name that enumeration: it asks
for **some** `f : EffectivePresentation (ScottHom α β)` with `IsRecursive f`. So
the defect blocks `Effective.StepFunctionsDecidable`, whose statement does name
`Effective.scottHom d e`, and does **not** block the theorem the paper states.

`consistentEnum` is the same enumeration with the guard replaced by
`Consistent` — a condition on `d`, `e` and the index set alone, which section 2
proves equivalent to the existence of the join, and which
`bddAbove_iff_exists_normal` proves §3.2's two conditions decide. It is an
`EffectivePresentation` (`scottHomC`), it agrees with `Effective.scottHomEnum`
wherever that one is right, and it reduces the claim to recursion theory over a
determinate guard. -/

section Enumeration

variable {α β : Type*} [CompletePartialOrder α] [Domain α]
  [CompletePartialOrder β] [Domain β] [BoundedComplete β]

omit [BoundedComplete β] in
theorem finite_pairsOf (d : EffectivePresentation α) (e : EffectivePresentation β)
    (Q : Finset (ℕ × ℕ)) : (Effective.pairsOf d e Q).Finite :=
  Q.finite_toSet.image _

omit [BoundedComplete β] in
theorem pairsOf_subset_compacts (d : EffectivePresentation α) (e : EffectivePresentation β)
    (Q : Finset (ℕ × ℕ)) : Effective.pairsOf d e Q ⊆ compacts α ×ˢ compacts β := by
  rintro _ ⟨q, _, rfl⟩
  exact ⟨d.enum_mem_compacts q.1, e.enum_mem_compacts q.2⟩

/-- **Every compact function is the join of a finite set of compact pairs that is
consistent.** `ScottHom.exists_ofPairs_of_isCompactElement` returns the naming set
but drops the bound; the step functions it names are bounded by `g` itself, so
`bddAbove_stepsOf_iff` upgrades the conclusion. This is what makes the
consistency-guarded enumeration still exhaust `K(D → E)`. -/
theorem exists_ofPairs_consistent {g : ScottHom α β} (hg : IsCompactElement g) :
    ∃ P : Set (α × β), P.Finite ∧ P ⊆ compacts α ×ˢ compacts β ∧
      g = ScottHom.ofPairs P ∧ Consistent P := by
  obtain ⟨S, hfin, hsub, hlub⟩ := ScottHom.exists_finite_isLUB_of_isCompactElement hg
  have hsteps : ScottHom.stepsOf (ScottHom.stepPairOf '' S) = S :=
    ScottHom.stepsOf_image_stepPairOf fun h hh => (hsub hh).1
  have hcpt : ScottHom.stepPairOf '' S ⊆ compacts α ×ˢ compacts β := by
    rintro _ ⟨h, hh, rfl⟩
    have hp := ScottHom.isStepPair_stepPairOf (hsub hh).1
    exact ⟨hp.1, hp.2.1⟩
  refine ⟨ScottHom.stepPairOf '' S, hfin.image _, hcpt, ?_, ?_⟩
  · rw [ScottHom.ofPairs, hsteps]
    exact hlub.unique (isLUB_sSup_of_bddAbove ⟨g, hlub.1⟩)
  · exact (bddAbove_stepsOf_iff (hfin.image _) hcpt).mp (by rw [hsteps]; exact ⟨g, hlub.1⟩)

open Classical in
/-- **The enumeration of `K(D → E)`, guarded by consistency.** Identical to
`Effective.scottHomEnum` except for the guard: `Consistent (pairsOf d e Q)` in
place of `IsCompactElement (ofPairs (pairsOf d e Q))`. -/
noncomputable def consistentEnum (d : EffectivePresentation α) (e : EffectivePresentation β)
    (n : ℕ) : ScottHom α β :=
  if Consistent (Effective.pairsOf d e (Denumerable.ofNat (Finset (ℕ × ℕ)) n))
    then ScottHom.ofPairs (Effective.pairsOf d e (Denumerable.ofNat (Finset (ℕ × ℕ)) n))
    else ⊥

theorem consistentEnum_isCompactElement (d : EffectivePresentation α)
    (e : EffectivePresentation β) (n : ℕ) : IsCompactElement (consistentEnum d e n) := by
  classical
  simp only [consistentEnum]
  split_ifs with h
  · exact isCompactElement_ofPairs_of_consistent (finite_pairsOf d e _)
      (pairsOf_subset_compacts d e _) h
  · exact isCompactElement_bot

/-- **The consistency-guarded enumeration exhausts `K(D → E)`.** Same pullback as
`Effective.exists_scottHomEnum_eq`; the guard is discharged by
`exists_ofPairs_consistent` rather than by a compactness test. -/
theorem exists_consistentEnum_eq (d : EffectivePresentation α) (e : EffectivePresentation β)
    {g : ScottHom α β} (hg : IsCompactElement g) : ∃ n, consistentEnum d e n = g := by
  classical
  obtain ⟨P, hfin, hsub, hgP, hcons⟩ := exists_ofPairs_consistent hg
  have hchoice : ∀ p ∈ P, ∃ q : ℕ × ℕ, (d.enum q.1, e.enum q.2) = p := by
    intro p hp
    obtain ⟨i, hi⟩ := d.enum_surjective p.1 (hsub hp).1
    obtain ⟨j, hj⟩ := e.enum_surjective p.2 (hsub hp).2
    exact ⟨(i, j), by rw [hi, hj]⟩
  choose! φ hφ using hchoice
  have hpairs : Effective.pairsOf d e (hfin.image φ).toFinset = P := by
    rw [Effective.pairsOf, Set.Finite.coe_toFinset]
    ext p
    constructor
    · rintro ⟨_, ⟨p', hp', rfl⟩, rfl⟩
      show (d.enum (φ p').1, e.enum (φ p').2) ∈ P
      rw [hφ p' hp']
      exact hp'
    · intro hp
      exact ⟨φ p, ⟨p, hp, rfl⟩, hφ p hp⟩
  obtain ⟨n, hn⟩ := Effective.surjective_ofNat_finset (hfin.image φ).toFinset
  refine ⟨n, ?_⟩
  simp only [consistentEnum, hn, hpairs]
  rw [if_pos hcons]
  exact hgP.symm

/-- The two enumerations agree wherever `Effective.scottHomEnum` is reading a
genuine join. They can differ only on the indices section 3 exhibits, where the
join does not exist and the total `sSup` returns an unconstrained value. -/
theorem consistentEnum_eq_scottHomEnum (d : EffectivePresentation α)
    (e : EffectivePresentation β) (n : ℕ)
    (h : Consistent (Effective.pairsOf d e (Denumerable.ofNat (Finset (ℕ × ℕ)) n))) :
    consistentEnum d e n = Effective.scottHomEnum d e n := by
  classical
  rw [consistentEnum, if_pos h]
  exact (Effective.scottHomEnum_of_ofNat d e rfl
    (isCompactElement_ofPairs_of_consistent (finite_pairsOf d e _)
      (pairsOf_subset_compacts d e _) h)).symm

open Classical in
/-- **An effective presentation of `D → E` whose guard is determined by `d` and
`e`.** The two `Decidable` fields are `Classical.dec`, exactly as
`Effective.scottHom`'s are — this construction changes the *enumeration*, not the
decision procedures, and claims nothing about them. -/
noncomputable def scottHomC (d : EffectivePresentation α) (e : EffectivePresentation β) :
    EffectivePresentation (ScottHom α β) where
  enum := consistentEnum d e
  enum_mem_compacts := consistentEnum_isCompactElement d e
  enum_surjective _ hg := exists_consistentEnum_eq d e hg
  decidableLE _ := Classical.dec _
  decidableNormal _ := Classical.dec _

/-- **`Effective.Theorem7ArrowRecursive` reduced to recursion theory over a
determinate enumeration.**

The claim asks for *some* recursive presentation of `D → E`, so it is not tied to
`Effective.scottHom d e`. Routing it through `scottHomC` replaces the guard that
section 3 refutes by one section 2 characterizes, leaving the recursion theory as
the only open input — the same position `R46.Agent3` left `⊸` in.

No added binder: the binder list is `Theorem7ArrowRecursive`'s own, and the
universe annotation is load-bearing for the same reason r0045 records for
`R45.Agent1.theorem_7_arrowRecursive_of_stepFunctionsDecidable` — a hypothesis
cannot quantify over universes. -/
theorem theorem_7_arrowRecursive_of_scottHomC.{u, v}
    (h : ∀ {α : Type u} {β : Type v} [CompletePartialOrder α] [Domain α]
      [CompletePartialOrder β] [Domain β] [BoundedComplete β] (d : EffectivePresentation α)
      (e : EffectivePresentation β), IsRecursive d → IsRecursive e →
      IsRecursive (scottHomC d e)) :
    Effective.Theorem7ArrowRecursive.{u, v} := by
  intro α β _ _ _ _ _ d e hd he
  exact ⟨scottHomC d e, h d e hd he⟩

/-! ### The same repair for `⊸`

`R46.Agent3.strictHomEnum` carries the identical guard, `IsCompactElement
(strictStepJoin d e Q)`, and section 3's refutation applies to it verbatim —
`R46.Agent3.strictStepJoin` is `ofPairs` of a subset of `pairsOf`, and the
subtype inherits the ambient junk `sSup`. `Effective.Theorem7StrictRecursive`
likewise asks only for *some* recursive presentation, so the same replacement
works. -/

omit [BoundedComplete β] in
theorem finite_strictPairsOf (d : EffectivePresentation α) (e : EffectivePresentation β)
    (Q : Finset (ℕ × ℕ)) : (R46.Agent3.strictPairsOf d e Q).Finite :=
  (finite_pairsOf d e Q).subset fun _ hp => hp.1

omit [BoundedComplete β] in
theorem strictPairsOf_subset_compacts (d : EffectivePresentation α)
    (e : EffectivePresentation β) (Q : Finset (ℕ × ℕ)) :
    R46.Agent3.strictPairsOf d e Q ⊆ compacts α ×ˢ compacts β :=
  fun _ hp => pairsOf_subset_compacts d e Q hp.1

open Classical in
/-- **The enumeration of `K(D ⊸ E)`, guarded by consistency.**
`R46.Agent3.strictHomEnum` with its guard replaced, exactly as `consistentEnum`
replaces `Effective.scottHomEnum`'s. -/
noncomputable def strictConsistentEnum (d : EffectivePresentation α)
    (e : EffectivePresentation β) (n : ℕ) : StrictHom α β :=
  if Consistent (R46.Agent3.strictPairsOf d e (Denumerable.ofNat (Finset (ℕ × ℕ)) n))
    then R46.Agent3.strictStepJoin d e (Denumerable.ofNat (Finset (ℕ × ℕ)) n)
    else ⊥

theorem strictConsistentEnum_isCompactElement (d : EffectivePresentation α)
    (e : EffectivePresentation β) (n : ℕ) :
    IsCompactElement (strictConsistentEnum d e n) := by
  classical
  simp only [strictConsistentEnum]
  split_ifs with h
  · exact ClosureProperties.isCompactElement_of_isCompactElement_val
      (isCompactElement_ofPairs_of_consistent (finite_strictPairsOf d e _)
        (strictPairsOf_subset_compacts d e _) h)
  · exact isCompactElement_bot

/-- **The consistency-guarded strict enumeration exhausts `K(D ⊸ E)`.** The proof
is `R46.Agent3.exists_strictHomEnum_eq`'s, with one change: the guard is
discharged from `bddAbove_stepsOf_iff` — the step functions are bounded by `g`
itself — instead of from a compactness test. -/
theorem exists_strictConsistentEnum_eq (d : EffectivePresentation α)
    (e : EffectivePresentation β) {g : StrictHom α β} (hg : IsCompactElement g) :
    ∃ n, strictConsistentEnum d e n = g := by
  classical
  obtain ⟨S, hfin, hsub, hstrictS, hlub⟩ := R46.Agent3.exists_strictSteps_isLUB hg
  have hstepS : ∀ h ∈ S, ∃ p, ScottHom.IsStepPair h p := fun h hh => (hsub hh).1
  have hstepsP : ScottHom.stepsOf (ScottHom.stepPairOf '' S) = S :=
    ScottHom.stepsOf_image_stepPairOf hstepS
  have hPstrict : ∀ p ∈ ScottHom.stepPairOf '' S, p.1 = ⊥ → p.2 = ⊥ := by
    rintro _ ⟨h, hh, rfl⟩
    exact (R46.Agent3.isStrict_iff_of_isStepPair
      (ScottHom.isStepPair_stepPairOf (hstepS h hh))).mp (hstrictS h hh)
  have hchoice : ∀ p ∈ ScottHom.stepPairOf '' S, ∃ q : ℕ × ℕ, (d.enum q.1, e.enum q.2) = p := by
    rintro _ ⟨h, hh, rfl⟩
    have hp := ScottHom.isStepPair_stepPairOf (hstepS h hh)
    obtain ⟨i, hi⟩ := d.enum_surjective _ hp.1
    obtain ⟨j, hj⟩ := e.enum_surjective _ hp.2.1
    exact ⟨(i, j), by rw [hi, hj]⟩
  choose! φ hφ using hchoice
  have hPfin : (ScottHom.stepPairOf '' S).Finite := hfin.image _
  have hpairs : Effective.pairsOf d e (hPfin.image φ).toFinset = ScottHom.stepPairOf '' S := by
    rw [Effective.pairsOf, Set.Finite.coe_toFinset]
    ext p
    constructor
    · rintro ⟨_, ⟨p', hp', rfl⟩, rfl⟩
      show (d.enum (φ p').1, e.enum (φ p').2) ∈ ScottHom.stepPairOf '' S
      rw [hφ p' hp']
      exact hp'
    · intro hp
      exact ⟨φ p, ⟨p, hp, rfl⟩, hφ p hp⟩
  have hstrictPairs :
      R46.Agent3.strictPairsOf d e (hPfin.image φ).toFinset = ScottHom.stepPairOf '' S := by
    rw [R46.Agent3.strictPairsOf, hpairs]
    ext p
    exact ⟨fun h => h.1, fun h => ⟨h, hPstrict p h⟩⟩
  have hcons : Consistent (R46.Agent3.strictPairsOf d e (hPfin.image φ).toFinset) := by
    refine (bddAbove_stepsOf_iff (finite_strictPairsOf d e _) ?_).mp ?_
    · rw [hstrictPairs]
      rintro _ ⟨h, hh, rfl⟩
      have hp := ScottHom.isStepPair_stepPairOf (hstepS h hh)
      exact ⟨hp.1, hp.2.1⟩
    · rw [hstrictPairs, hstepsP]
      exact ⟨(g.val : ScottHom α β), hlub.1⟩
  have hjoin : (R46.Agent3.strictStepJoin d e (hPfin.image φ).toFinset).val
      = (g.val : ScottHom α β) := by
    show ScottHom.ofPairs (R46.Agent3.strictPairsOf d e (hPfin.image φ).toFinset) = _
    rw [hstrictPairs, ScottHom.ofPairs, hstepsP]
    exact (hlub.unique (isLUB_sSup_of_bddAbove ⟨(g.val : ScottHom α β), hlub.1⟩)).symm
  obtain ⟨n, hn⟩ := Effective.surjective_ofNat_finset (hPfin.image φ).toFinset
  refine ⟨n, ?_⟩
  simp only [strictConsistentEnum, hn]
  rw [if_pos hcons]
  exact Subtype.ext hjoin

open Classical in
/-- **An effective presentation of `D ⊸ E` whose guard is determined by `d` and
`e`.** The `[Domain (StrictHom α β)]` binder is `Theorem7StrictRecursive`'s own,
discharged at any use site by `PRepFun.strictHomDomain`. -/
noncomputable def strictHomC [Domain (StrictHom α β)] (d : EffectivePresentation α)
    (e : EffectivePresentation β) : EffectivePresentation (StrictHom α β) where
  enum := strictConsistentEnum d e
  enum_mem_compacts := strictConsistentEnum_isCompactElement d e
  enum_surjective _ hg := exists_strictConsistentEnum_eq d e hg
  decidableLE _ := Classical.dec _
  decidableNormal _ := Classical.dec _

/-- **`Effective.Theorem7StrictRecursive` reduced to recursion theory over a
determinate enumeration**, the `⊸` counterpart of
`theorem_7_arrowRecursive_of_scottHomC`. -/
theorem theorem_7_strictRecursive_of_strictHomC.{u, v}
    (h : ∀ {α : Type u} {β : Type v} [CompletePartialOrder α] [Domain α]
      [CompletePartialOrder β] [Domain β] [BoundedComplete β] [Domain (StrictHom α β)]
      (d : EffectivePresentation α) (e : EffectivePresentation β),
      IsRecursive d → IsRecursive e → IsRecursive (strictHomC d e)) :
    Effective.Theorem7StrictRecursive.{u, v} := by
  intro α β _ _ _ _ _ _ d e hd he
  exact ⟨strictHomC d e, h d e hd he⟩

end Enumeration

end ScottDomains.R47.Agent2
