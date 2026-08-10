import ScottDomains.IdealCompletion
import ScottDomains.Powerset

/-!
# The Plotkin (convex) powerdomain

Gunter & Scott, *Semantic Domains* (Handbook of Theoretical Computer Science
Vol. B, 1990), §5.2. The source PDF was not available to this file's session, so
the definition below is stated in the project's own words rather than quoted; it
is the standard one. What is formalized here is:

* the pre-order `FinCompacts D` of **finite nonempty subsets of `K(D)`** under
  the **Egli–Milner** ordering — the conjunction of the Hoare (lower) and Smyth
  (upper) orderings;
* `Powerdomain D`, the **ideal completion** of that pre-order, which is a
  `Domain` by Theorem 11 (`ScottDomains.IdealCompletion.theorem_11`);
* the identification of `K(Powerdomain D)` with the principal ideals.

## Which ordering, exactly

For `u v : FinCompacts D`,

    u ≤ v  ↔  (∀ a ∈ u, ∃ b ∈ v, a ≤ b) ∧ (∀ b ∈ v, ∃ a ∈ u, a ≤ b).

The first conjunct is the Hoare (lower) ordering, the second the Smyth (upper)
ordering; their conjunction is the Egli–Milner ordering proper. This is the
Plotkin/convex case and it is the ordering formalized here — neither conjunct is
taken alone.

## Orientation

`IdealCompletion.lean` records the trap: the paper writes `a ⊢ b` for "`a` is
larger than `b`", which Mathlib writes `b ≤ a`. Every statement in this file uses
Mathlib's orientation. So `u ≤ v` reads "`u` is below `v`", i.e. the paper's
`v ⊢ u`; the least element is `{⊥}`, matching the paper's requirement of an
element `⊥` with `x ⊢ ⊥` for every `x`, which is `[OrderBot]` here.

## Why the carrier excludes the empty set

`∅` is Egli–Milner-comparable to nothing but itself: `∅ ≤ v` demands a member of
`∅` below each member of `v`, which fails for every nonempty `v`, and `v ≤ ∅`
demands a member of `∅` above each member of `v`. Admitting it would destroy
`OrderBot` and with it Theorem 11's hypothesis. The carrier is therefore the
finite **nonempty** subsets, and the least element is the singleton `{⊥}`.

## Did we quotient? No — and here is the proof that we did not have to

Egli–Milner is a genuine pre-order and **not** a partial order:
`exists_le_le_ne_of_lt_lt` shows antisymmetry fails as soon as `K(D)` holds a
three-element chain `x < y < z`, since `{x, z}` and `{x, y, z}` are each below
the other; `not_antisymm_natPowerset` instantiates that in `P ℕ`. This is where
the convex powerdomain differs from the Hoare and Smyth cases.

No quotient is taken, because Theorem 11 as formalized is stated for an arbitrary
`Preorder` — `Order.Ideal` never needed antisymmetry. The quotient happens on its
own inside the ideal completion: `principal_eq_principal_iff` says two finite sets
name the *same* ideal exactly when each is below the other, so `principal` is not
injective and its range — which is `K(Powerdomain D)` — is precisely the set of
Egli–Milner equivalence classes, the convex sets. Quotienting first and then
completing would produce the same poset by a longer route.

## The union is not a join

`not_single_le_pair`: `{a} ≤ {a, b}` fails whenever `a ≰ b`. Union is an upper
bound for the Hoare and Smyth orderings but not for Egli–Milner, so
`FinCompacts D` is not a `SemilatticeSup` and in general not even directed. This
costs nothing here: Theorem 11 asks the pre-order for a least element and
countability, not for directedness — the directedness it needs is a property of
each *ideal*, not of the ambient pre-order.
-/

namespace ScottDomains.Plotkin

universe u

variable {D : Type u}

/-! ## The pre-order of finite nonempty sets of compacts -/

/-- The carrier of the Plotkin pre-order: the finite nonempty subsets of `K(D)`.

A `def` rather than an `abbrev`, and deliberately: as a bare subtype of
`Set ↥(compacts D)` it would pick up Mathlib's `Subtype.partialOrder`, i.e.
inclusion, and the Egli–Milner `Preorder` declared below would be a second,
non-defeq order instance on the same type. The synonym keeps them apart, exactly
as `IdealCompletion` keeps its `SupSet` apart from Mathlib's. -/
def FinCompacts (D : Type u) [PartialOrder D] : Type u :=
  {u : Set ↥(compacts D) // u.Finite ∧ u.Nonempty}

namespace FinCompacts

section PartialOrder

variable [PartialOrder D]

/-- The underlying set of compact elements. -/
def carrier (u : FinCompacts D) : Set ↥(compacts D) := Subtype.val u

theorem finite (u : FinCompacts D) : u.carrier.Finite := u.2.1

theorem nonempty (u : FinCompacts D) : u.carrier.Nonempty := u.2.2

instance : Membership ↥(compacts D) (FinCompacts D) := ⟨fun u a => a ∈ u.carrier⟩

@[simp] theorem mem_carrier {a : ↥(compacts D)} {u : FinCompacts D} :
    a ∈ u.carrier ↔ a ∈ u := Iff.rfl

@[ext] theorem ext {u v : FinCompacts D} (h : ∀ a, a ∈ u ↔ a ∈ v) : u = v :=
  Subtype.ext (Set.ext h)

/-! ### Small constructors

`single`, `pair` and `triple` are the finite sets the witnesses below need; they
also name the least element (`⊥ = single ⊥`). -/

/-- `{a}`. -/
def single (a : ↥(compacts D)) : FinCompacts D :=
  ⟨{a}, Set.finite_singleton a, Set.singleton_nonempty a⟩

/-- `{a, b}`. -/
def pair (a b : ↥(compacts D)) : FinCompacts D :=
  ⟨{a, b}, (Set.finite_singleton b).insert a, Set.insert_nonempty a {b}⟩

/-- `{a, b, c}`. -/
def triple (a b c : ↥(compacts D)) : FinCompacts D :=
  ⟨{a, b, c}, ((Set.finite_singleton c).insert b).insert a, Set.insert_nonempty a {b, c}⟩

@[simp] theorem mem_single {a b : ↥(compacts D)} : a ∈ single b ↔ a = b := Iff.rfl

@[simp] theorem mem_pair {a b c : ↥(compacts D)} : a ∈ pair b c ↔ a = b ∨ a = c := Iff.rfl

@[simp] theorem mem_triple {a b c d : ↥(compacts D)} :
    a ∈ triple b c d ↔ a = b ∨ a = c ∨ a = d := Iff.rfl

/-! ### The Egli–Milner pre-order -/

/-- The **Egli–Milner** (convex, Plotkin) ordering: `u ≤ v` iff every element of
`u` is below some element of `v` (the Hoare conjunct) **and** every element of
`v` is above some element of `u` (the Smyth conjunct). -/
protected def le (u v : FinCompacts D) : Prop :=
  (∀ a ∈ u, ∃ b ∈ v, a ≤ b) ∧ (∀ b ∈ v, ∃ a ∈ u, a ≤ b)

/-- Reflexivity and transitivity of Egli–Milner. Transitivity composes the two
conjuncts in opposite directions: the Hoare conjunct chases `u → v → w`, the
Smyth conjunct chases `w → v → u`. -/
instance : Preorder (FinCompacts D) where
  le := FinCompacts.le
  le_refl u := ⟨fun a ha => ⟨a, ha, le_rfl⟩, fun b hb => ⟨b, hb, le_rfl⟩⟩
  le_trans _ _ _ huv hvw :=
    ⟨fun a ha => by
        obtain ⟨b, hb, hab⟩ := huv.1 a ha
        obtain ⟨c, hc, hbc⟩ := hvw.1 b hb
        exact ⟨c, hc, hab.trans hbc⟩,
     fun c hc => by
        obtain ⟨b, hb, hbc⟩ := hvw.2 c hc
        obtain ⟨a, ha, hab⟩ := huv.2 b hb
        exact ⟨a, ha, hab.trans hbc⟩⟩

theorem le_def {u v : FinCompacts D} :
    u ≤ v ↔ (∀ a ∈ u, ∃ b ∈ v, a ≤ b) ∧ (∀ b ∈ v, ∃ a ∈ u, a ≤ b) := Iff.rfl

theorem le_hoare {u v : FinCompacts D} (h : u ≤ v) : ∀ a ∈ u, ∃ b ∈ v, a ≤ b := h.1

theorem le_smyth {u v : FinCompacts D} (h : u ≤ v) : ∀ b ∈ v, ∃ a ∈ u, a ≤ b := h.2

/-! ### Antisymmetry fails

This is the one of the three orderings that is a pre-order and not a partial
order, so the fact is proved rather than asserted. -/

/-- If `K(D)` contains a three-element chain `x < y < z`, Egli–Milner
antisymmetry fails: `{x, z} ≤ {x, y, z}` because `y` is above `x`, and
`{x, y, z} ≤ {x, z}` because `y` is below `z`, yet the two sets differ. -/
theorem exists_le_le_ne_of_lt_lt {x y z : ↥(compacts D)} (hxy : x < y) (hyz : y < z) :
    ∃ u v : FinCompacts D, u ≤ v ∧ v ≤ u ∧ u ≠ v := by
  refine ⟨pair x z, triple x y z, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · intro a ha
    rcases mem_pair.mp ha with rfl | rfl
    · exact ⟨a, mem_triple.mpr (Or.inl rfl), le_rfl⟩
    · exact ⟨a, mem_triple.mpr (Or.inr (Or.inr rfl)), le_rfl⟩
  · intro b hb
    rcases mem_triple.mp hb with rfl | rfl | rfl
    · exact ⟨b, mem_pair.mpr (Or.inl rfl), le_rfl⟩
    · exact ⟨x, mem_pair.mpr (Or.inl rfl), hxy.le⟩
    · exact ⟨b, mem_pair.mpr (Or.inr rfl), le_rfl⟩
  · intro a ha
    rcases mem_triple.mp ha with rfl | rfl | rfl
    · exact ⟨a, mem_pair.mpr (Or.inl rfl), le_rfl⟩
    · exact ⟨z, mem_pair.mpr (Or.inr rfl), hyz.le⟩
    · exact ⟨a, mem_pair.mpr (Or.inr rfl), le_rfl⟩
  · intro b hb
    rcases mem_pair.mp hb with rfl | rfl
    · exact ⟨b, mem_triple.mpr (Or.inl rfl), le_rfl⟩
    · exact ⟨b, mem_triple.mpr (Or.inr (Or.inr rfl)), le_rfl⟩
  · intro h
    have hy : y ∈ triple x y z := mem_triple.mpr (Or.inr (Or.inl rfl))
    rw [← h] at hy
    rcases mem_pair.mp hy with rfl | rfl
    exacts [absurd hxy (lt_irrefl _), absurd hyz (lt_irrefl _)]

/-- Egli–Milner is not directed by union, unlike the Hoare and Smyth orderings:
`{a} ≤ {a, b}` fails whenever `a ≰ b`, because the Smyth conjunct then has no
element of `{a}` to place below `b`. -/
theorem not_single_le_pair {a b : ↥(compacts D)} (h : ¬ a ≤ b) : ¬ single a ≤ pair a b := by
  intro hle
  obtain ⟨c, hc, hcb⟩ := hle.2 b (mem_pair.mpr (Or.inr rfl))
  rw [mem_single] at hc
  subst hc
  exact h hcb

end PartialOrder

/-! ### `OrderBot` and `Countable`, the two hypotheses Theorem 11 consumes -/

section Bot

variable [CompletePartialOrder D]

/-- The least element is the singleton `{⊥}`: it is below every nonempty `v`
because `⊥` is below each member of `v` (Smyth conjunct) and some member of `v`
exists to sit above `⊥` (Hoare conjunct — this is where nonemptiness of the
carrier is spent). -/
instance : OrderBot (FinCompacts D) where
  bot := single ⊥
  bot_le u :=
    ⟨fun a ha => by
        obtain ⟨b, hb⟩ := u.nonempty
        rw [mem_single] at ha
        subst ha
        exact ⟨b, hb, bot_le⟩,
     fun b hb => ⟨⊥, mem_single.mpr rfl, bot_le⟩⟩

@[simp] theorem bot_eq_single : (⊥ : FinCompacts D) = single ⊥ := rfl

/-- The finite subsets of a countable set form a countable set, and `K(D)` is
countable because `D` is a domain. This is the countability hypothesis of
Theorem 11. -/
instance instCountable [Domain D] : Countable (FinCompacts D) :=
  (Set.Countable.setOf_finite.mono (fun _ hs => hs.1)).to_subtype

end Bot

end FinCompacts

/-! ## The powerdomain -/

open FinCompacts

variable [CompletePartialOrder D]

/-- The **Plotkin (convex) powerdomain** of `D`: the ideal completion of the
Egli–Milner pre-order on finite nonempty subsets of `K(D)`.

An `abbrev`, so that Theorem 11's `CompletePartialOrder`, `IsAlgebraic` and
`Domain` instances on `IdealCompletion` apply to it without restatement. -/
abbrev Powerdomain (D : Type u) [CompletePartialOrder D] : Type u :=
  IdealCompletion (FinCompacts D)

/-- `↓u`, the principal ideal of the finite set `u` — the compact element of the
powerdomain that `u` names. -/
abbrev principal (u : FinCompacts D) : Powerdomain D := IdealCompletion.principal u

/-- `principal` is order-reflecting as well as monotone. -/
@[simp] theorem principal_le_principal {u v : FinCompacts D} :
    principal u ≤ principal v ↔ u ≤ v :=
  IdealCompletion.principal_le_iff.trans IdealCompletion.mem_principal

/-- **The convex quotient, taken for free by the ideal completion.** Two finite
sets name the same element of the powerdomain exactly when each is Egli–Milner
below the other — that is, exactly when they have the same convex closure. No
`Quotient` is formed anywhere in this file; the ideal completion of a pre-order
already collapses equivalent elements, because `↓u = ↓v` whenever `u` and `v`
are equivalent. -/
theorem principal_eq_principal_iff {u v : FinCompacts D} :
    principal u = principal v ↔ u ≤ v ∧ v ≤ u := by
  constructor
  · intro h
    exact ⟨principal_le_principal.mp h.le, principal_le_principal.mp h.ge⟩
  · rintro ⟨h₁, h₂⟩
    exact le_antisymm (principal_le_principal.mpr h₁) (principal_le_principal.mpr h₂)

/-- `K(Powerdomain D)` is the set of principal ideals — the second half of
Theorem 11's conclusion, read at the Plotkin pre-order. With
`principal_eq_principal_iff`, this says the compact elements of the Plotkin
powerdomain are the Egli–Milner equivalence classes of finite nonempty sets of
compacts, i.e. the finitely generated convex sets. -/
theorem compacts_eq_range_principal (D : Type u) [CompletePartialOrder D] :
    compacts (Powerdomain D) = Set.range (principal : FinCompacts D → Powerdomain D) :=
  IdealCompletion.compacts_eq_range_principal

/-- Elementwise form of the same characterization. -/
theorem isCompactElement_iff {P : Powerdomain D} :
    IsCompactElement P ↔ ∃ u : FinCompacts D, P = principal u :=
  IdealCompletion.isCompactElement_iff_exists_eq_principal

/-- **The Plotkin powerdomain of a domain is a domain**, with `K` the principal
ideals. This is Theorem 11 instantiated at the pre-order `FinCompacts D`: the
three hypotheses it consumes are `Preorder`, `OrderBot` (the singleton `{⊥}`) and
`Countable` (from `Domain.countable_compacts`), all supplied above. -/
theorem isDomain (D : Type u) [CompletePartialOrder D] [Domain D] :
    Domain (Powerdomain D) ∧
      compacts (Powerdomain D) = Set.range (principal : FinCompacts D → Powerdomain D) :=
  IdealCompletion.theorem_11 (FinCompacts D)

/-- The `Domain` instance is found by resolution, with no bespoke instance in
this file. -/
example [Domain D] : Domain (Powerdomain D) := inferInstance

/-! ## Witnesses in `P ℕ`

`Prop` cannot witness anything here — its two elements admit no three-element
chain and no incomparable pair. `P ℕ` (`Powerset.lean`) has both. -/

/-- A finite subset of `ℕ`, as a compact element of `P ℕ`. -/
def natCompact (s : Set ℕ) (h : s.Finite) : ↥(compacts (Set ℕ)) :=
  ⟨s, isCompactElement_iff_finite.mpr h⟩

/-- `∅`, `{0}`, `{1}`, `{1, 0}` as compact elements of `P ℕ`. The last is written
`{1, 0}` and not `{0, 1}` — the same set, but only in that spelling is it the
literal `insert 1 {0}` that `Set.ssubset_insert` consumes. -/
def cEmpty : ↥(compacts (Set ℕ)) := natCompact ∅ Set.finite_empty

@[inherit_doc cEmpty]
def cZero : ↥(compacts (Set ℕ)) := natCompact {0} (Set.finite_singleton 0)

@[inherit_doc cEmpty]
def cOne : ↥(compacts (Set ℕ)) := natCompact {1} (Set.finite_singleton 1)

@[inherit_doc cEmpty]
def cZeroOne : ↥(compacts (Set ℕ)) := natCompact {1, 0} ((Set.finite_singleton 0).insert 1)

theorem cEmpty_lt_cZero : cEmpty < cZero :=
  Subtype.mk_lt_mk.mpr (Set.empty_ssubset.mpr (Set.singleton_nonempty 0))

theorem cZero_lt_cZeroOne : cZero < cZeroOne :=
  Subtype.mk_lt_mk.mpr (Set.ssubset_insert (by simp))

theorem not_cZero_le_cOne : ¬ cZero ≤ cOne := by
  intro h
  have h' : ({0} : Set ℕ) ⊆ {1} := Subtype.mk_le_mk.mp h
  simpa using h' (Set.mem_singleton (0 : ℕ))

/-- Egli–Milner antisymmetry fails in `P ℕ`: `{∅, {0,1}} ` and `{∅, {0}, {0,1}}`
are each below the other and are distinct. So `FinCompacts (Set ℕ)` is a
pre-order that is not a partial order — the Plotkin case, and the reason the
other two powerdomains' shape must not be forced onto it. -/
theorem not_antisymm_natPowerset :
    ∃ u v : FinCompacts (Set ℕ), u ≤ v ∧ v ≤ u ∧ u ≠ v :=
  exists_le_le_ne_of_lt_lt cEmpty_lt_cZero cZero_lt_cZeroOne

/-- The powerdomain identifies that pair: distinct finite sets, one ideal. This
is the convex quotient happening inside the ideal completion. -/
theorem exists_ne_principal_eq :
    ∃ u v : FinCompacts (Set ℕ), u ≠ v ∧ principal u = principal v := by
  obtain ⟨u, v, h₁, h₂, hne⟩ := not_antisymm_natPowerset
  exact ⟨u, v, hne, principal_eq_principal_iff.mpr ⟨h₁, h₂⟩⟩

/-- Union is not an upper bound in `P ℕ`: `{{0}} ≰ {{0}, {1}}`. -/
theorem not_single_le_pair_natPowerset :
    ¬ single cZero ≤ pair cZero cOne :=
  not_single_le_pair not_cZero_le_cOne

example : Domain (Powerdomain (Set ℕ)) := inferInstance

end ScottDomains.Plotkin

/- Axiom audit, by `#print axioms` (run, then removed so the build emits no
`info` lines). Every declaration depends only on the three standard axioms; none
depends on `sorryAx`.

  ScottDomains.Plotkin.isDomain                             [propext, Classical.choice, Quot.sound]
  ScottDomains.Plotkin.compacts_eq_range_principal          [propext, Classical.choice, Quot.sound]
  ScottDomains.Plotkin.isCompactElement_iff                 [propext, Classical.choice, Quot.sound]
  ScottDomains.Plotkin.principal_eq_principal_iff           [propext, Quot.sound]
  ScottDomains.Plotkin.principal_le_principal               [propext, Quot.sound]
  ScottDomains.Plotkin.FinCompacts.instPreorder             [propext]
  ScottDomains.Plotkin.FinCompacts.instOrderBot             [propext, Classical.choice, Quot.sound]
  ScottDomains.Plotkin.FinCompacts.instCountable            [propext, Classical.choice, Quot.sound]
  ScottDomains.Plotkin.FinCompacts.exists_le_le_ne_of_lt_lt [propext, Classical.choice, Quot.sound]
  ScottDomains.Plotkin.FinCompacts.not_single_le_pair       [propext, Classical.choice, Quot.sound]
  ScottDomains.Plotkin.not_antisymm_natPowerset             [propext, Classical.choice, Quot.sound]
  ScottDomains.Plotkin.exists_ne_principal_eq               [propext, Classical.choice, Quot.sound]
  ScottDomains.Plotkin.not_single_le_pair_natPowerset       [propext, Classical.choice, Quot.sound]

`Classical.choice` is inherited from `IdealCompletion`'s `idealSup` (a `dite` on
the undecidable predicate `Order.IsIdeal`) and from `Set.Countable.setOf_finite`;
the Egli–Milner `Preorder` itself needs none of it. -/
