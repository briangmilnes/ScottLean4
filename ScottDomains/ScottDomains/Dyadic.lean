import ScottDomains.IdealCompletion
-- `ScottHom`, `IsEmbeddingProjectionPair` (Theorem 27's conclusion), and
-- `IsNormalIn` (its hypothesis).
import ScottDomains.Projection
import ScottDomains.NormalSubposet
-- `ℚ` as a linearly ordered field: the order instances, then the field structure,
-- then `div_lt_one` and its neighbours.  Without these `ℚ` is not even a known
-- name and Lean auto-binds it as an implicit type variable.
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Order.Field.Basic
-- `Finset.countable`, the instance `Countable α → Countable (Finset α)` that
-- makes the basis `U₀` countable, and `Countable ℚ`, which it needs.
import Mathlib.Logic.Equiv.List
import Mathlib.Data.Rat.Denumerable

/-!
# §7.3: the universal domain `U`, the ideal completion of the dyadic half-open intervals

Gunter & Scott, *Semantic Domains* (Handbook of Theoretical Computer Science
Vol. B, 1990), §7.3, quoted from the source PDF rather than paraphrased:

> The construction of a suitable domain is somewhat more involved than was the
> case for `P N`. We begin by describing the basis of a domain `U`. Let `S` be the
> set of rational numbers of the form `n/2^m` where `0 ≤ n < 2^m` and `0 < m`. As
> the basis `U₀` of our domain we take finite (non-empty) unions of half open
> intervals `[r, t) = {s ∈ S | r ≤ s < t}`. … We order these sets by superset so
> that the interval `[0, 1)` is the least element. There is no top element under
> this ordering. If we adjoin the emptyset, say `B = U₀ ∪ {∅}`, then we get a
> Boolean algebra. … Letting `U` be the domain of ideals over `U₀` we may now
> conclude the following:

> **Theorem 27** For any bounded complete domain `D`, there is a projection
> `p : U → D`.

## What is built here and what is reused

This file supplies **only the pre-order** `U₀` and its two finiteness facts, and
then applies Theorem 11. Nothing about ideals, cpos, algebraicity or compactness
is re-proved: `IdealCompletion.instDomain` already turns a countable pre-order
with a least element into a `Domain`, and `IdealCompletion.theorem_11` records that
`K(D)` is the set of principal ideals. So the content of Part 1 is three
declarations —

* `Dyadic.instPartialOrderU₀` — the paper's *superset* ordering;
* `Dyadic.instOrderBotU₀` — the least element `[0, 1) = S`;
* `Dyadic.instCountableU₀` — countability, by the injection of a basis element
  into the `Finset (ℚ × ℚ)` of interval endpoints that names it;

— after which `Domain U` is `inferInstance`.

## The endpoints

The paper writes `[r, t)` without saying where `r` and `t` live. They are dyadic:
the displayed picture places the endpoints on the dyadic grid, and the Boolean
algebra `B = U₀ ∪ {∅}` is closed under complement only if they are. `E` below is
therefore the dyadic rationals of `[0, 1]` — `S` together with the right endpoint
`1`, which is not itself a point of `S`. Note that `E`'s only role is fidelity:
countability, the least element, and bounded completeness would all hold verbatim
with arbitrary rational endpoints, since a linear order's `max` and `min` of two
endpoints is one of the two.

## Orientation of the order

`IdealCompletion` uses Mathlib's orientation, in which the paper's `a ⊢ b` ("`a`
is larger than `b`", i.e. `a` carries more information) is `b ≤ a`. The paper
orders `U₀` by superset with `[0, 1)` least, so here

> `X ≤ Y ↔ toSet Y ⊆ toSet X`

and `⊥ = S = [0, 1)`. A *smaller* set of dyadic points is a *larger* element:
more information is a narrower interval.

## Bounded completeness

`U` is bounded complete (`instBoundedCompleteU`), which is what makes Theorem 27
plausible in the first place — a projection of a bounded complete cpo is bounded
complete, and §7.4 opens by observing that the convex powerdomain *cannot* be
represented over `U` for exactly this reason. The proof consumes
`IdealCompletion.boundedComplete`, whose one hypothesis is least upper bounds of
bounded **pairs** of `U₀`; that least upper bound is the *intersection*
`X ∩ Y` (a larger element is a smaller set), and `isBasic_inter` is the fact that
finite unions of half-open intervals are closed under intersection.

## Statements

* `U₀` — the paper's basis: finite non-empty unions of dyadic half-open intervals
  of `[0, 1)`, ordered by superset.
* `U` — `IdealCompletion U₀`, the paper's universal domain; `Domain U` and
  `BoundedComplete U` are instances.
* `compacts_U` — `K(U)` is the set of principal ideals `↓X = {Y | X ⊆ Y}`,
  `X` ranging over `U₀`; `theorem_11_at_U` is the pair.
-/

namespace ScottDomains.Dyadic

/-! ### `S`: the dyadic points of `[0, 1)` -/

/-- The paper's `S`: the rationals `n/2^m` with `0 ≤ n < 2^m` and `0 < m` — that
is, the dyadic rationals of the half-open unit interval. -/
def S : Set ℚ := {q | ∃ n m : ℕ, 0 < m ∧ n < 2 ^ m ∧ q = (n : ℚ) / 2 ^ m}

theorem zero_mem_S : (0 : ℚ) ∈ S := ⟨0, 1, one_pos, by norm_num, by norm_num⟩

theorem S_nonempty : S.Nonempty := ⟨0, zero_mem_S⟩

/-- Every dyadic point is in `[0, 1)`: `0 ≤ n` gives the left bound and
`n < 2^m` the right one. -/
theorem mem_Ico_of_mem_S {q : ℚ} (h : q ∈ S) : 0 ≤ q ∧ q < 1 := by
  obtain ⟨n, m, -, hn, rfl⟩ := h
  have h2 : (0 : ℚ) < 2 ^ m := pow_pos (by norm_num) m
  refine ⟨div_nonneg (Nat.cast_nonneg n) h2.le, (div_lt_one h2).mpr ?_⟩
  exact_mod_cast hn

/-! ### `E`: the admissible endpoints -/

/-- The dyadic rationals of the *closed* interval `[0, 1]`, the endpoints an
interval `[r, t)` may take. It is `S` together with `1`. -/
def E : Set ℚ := {q | ∃ n m : ℕ, 0 < m ∧ n ≤ 2 ^ m ∧ q = (n : ℚ) / 2 ^ m}

theorem zero_mem_E : (0 : ℚ) ∈ E := ⟨0, 1, one_pos, by norm_num, by norm_num⟩

theorem one_mem_E : (1 : ℚ) ∈ E := ⟨2, 1, one_pos, by norm_num, by norm_num⟩

/-- `E` is closed under `max` because `max r t` *is* `r` or `t`; no arithmetic on
denominators is needed. The same argument gives `min_mem_E`. -/
theorem max_mem_E {r t : ℚ} (hr : r ∈ E) (ht : t ∈ E) : max r t ∈ E := by
  rcases le_total r t with h | h
  · rwa [max_eq_right h]
  · rwa [max_eq_left h]

theorem min_mem_E {r t : ℚ} (hr : r ∈ E) (ht : t ∈ E) : min r t ∈ E := by
  rcases le_total r t with h | h
  · rwa [min_eq_left h]
  · rwa [min_eq_right h]

/-! ### Half-open intervals -/

/-- The paper's `[r, t) = {s ∈ S | r ≤ s < t}`. -/
def Ivl (r t : ℚ) : Set ℚ := {s | s ∈ S ∧ r ≤ s ∧ s < t}

@[simp] theorem mem_Ivl {r t s : ℚ} : s ∈ Ivl r t ↔ s ∈ S ∧ r ≤ s ∧ s < t := Iff.rfl

theorem Ivl_subset_S {r t : ℚ} : Ivl r t ⊆ S := fun _ h => h.1

/-- `[0, 1)` is all of `S`, which is why it is the least element under superset. -/
theorem Ivl_zero_one : Ivl 0 1 = S := by
  ext q
  exact ⟨fun h => h.1, fun h => ⟨h, (mem_Ico_of_mem_S h).1, (mem_Ico_of_mem_S h).2⟩⟩

/-- Two half-open intervals meet in a half-open interval. This is the one fact
about intervals that bounded completeness of `U` consumes. -/
theorem Ivl_inter (r t r' t' : ℚ) :
    Ivl r t ∩ Ivl r' t' = Ivl (max r r') (min t t') := by
  ext s
  simp only [mem_Ivl, Set.mem_inter_iff, max_le_iff, lt_min_iff]
  tauto

/-! ### `U₀`: finite non-empty unions of intervals -/

/-- The union of the intervals named by a finite set of endpoint pairs. -/
def unionOf (F : Finset (ℚ × ℚ)) : Set ℚ := ⋃ p ∈ F, Ivl p.1 p.2

theorem mem_unionOf {F : Finset (ℚ × ℚ)} {s : ℚ} :
    s ∈ unionOf F ↔ ∃ p ∈ F, s ∈ Ivl p.1 p.2 := by
  simp only [unionOf, Set.mem_iUnion, exists_prop]

theorem unionOf_subset_S {F : Finset (ℚ × ℚ)} : unionOf F ⊆ S := by
  intro s hs
  obtain ⟨p, -, hp⟩ := mem_unionOf.mp hs
  exact Ivl_subset_S hp

theorem unionOf_singleton (r t : ℚ) : unionOf {(r, t)} = Ivl r t := by
  ext s
  rw [mem_unionOf]
  constructor
  · rintro ⟨p, hp, hs⟩
    rw [Finset.mem_singleton] at hp
    subst hp
    exact hs
  · exact fun hs => ⟨(r, t), Finset.mem_singleton_self _, hs⟩

/-- The paper's `U₀` as a predicate: a **finite non-empty union of half-open
intervals** with dyadic endpoints. Non-emptiness is the paper's own parenthesis,
and it is what keeps `∅` out of `U₀` — the paper adjoins it separately to form
the Boolean algebra `B`. -/
def IsBasic (X : Set ℚ) : Prop :=
  X.Nonempty ∧ ∃ F : Finset (ℚ × ℚ), (∀ p ∈ F, p.1 ∈ E ∧ p.2 ∈ E) ∧ X = unionOf F

theorem IsBasic.subset_S {X : Set ℚ} (h : IsBasic X) : X ⊆ S := by
  obtain ⟨-, F, -, rfl⟩ := h
  exact unionOf_subset_S

/-- `[0, 1)` is a basis element: the singleton family `{(0, 1)}`. -/
theorem isBasic_S : IsBasic S := by
  refine ⟨S_nonempty, {((0 : ℚ), (1 : ℚ))}, ?_, ?_⟩
  · intro p hp
    rw [Finset.mem_singleton] at hp
    subst hp
    exact ⟨zero_mem_E, one_mem_E⟩
  · rw [unionOf_singleton, Ivl_zero_one]

/-- Finite unions of intervals are closed under intersection: distribute, then
apply `Ivl_inter` pairwise over the product of the two endpoint families. -/
theorem unionOf_inter (F G : Finset (ℚ × ℚ)) :
    unionOf F ∩ unionOf G =
      unionOf ((F ×ˢ G).image fun pq => (max pq.1.1 pq.2.1, min pq.1.2 pq.2.2)) := by
  ext s
  simp only [Set.mem_inter_iff, mem_unionOf, Finset.mem_image, Finset.mem_product]
  constructor
  · rintro ⟨⟨p, hp, hsp⟩, q, hq, hsq⟩
    refine ⟨(max p.1 q.1, min p.2 q.2), ⟨(p, q), ⟨hp, hq⟩, rfl⟩, ?_⟩
    rw [← Ivl_inter]
    exact ⟨hsp, hsq⟩
  · rintro ⟨x, ⟨⟨p, q⟩, ⟨hp, hq⟩, rfl⟩, hs⟩
    rw [← Ivl_inter] at hs
    exact ⟨⟨p, hp, hs.1⟩, q, hq, hs.2⟩

/-- A finite family of intervals with endpoints in `E` and a non-empty union is a
basis element. Stated separately so `isBasic_inter` never has to unify two
independently elaborated copies of the `Finset.image` term (which forces defeq
checks on `DecidableEq ℚ` and exhausts the `whnf` budget). -/
theorem isBasic_unionOf {F : Finset (ℚ × ℚ)} (hF : ∀ p ∈ F, p.1 ∈ E ∧ p.2 ∈ E)
    (hne : (unionOf F).Nonempty) : IsBasic (unionOf F) := ⟨hne, F, hF, rfl⟩

theorem isBasic_inter {X Y : Set ℚ} (hX : IsBasic X) (hY : IsBasic Y)
    (hne : (X ∩ Y).Nonempty) : IsBasic (X ∩ Y) := by
  obtain ⟨-, F, hF, rfl⟩ := hX
  obtain ⟨-, G, hG, rfl⟩ := hY
  rw [unionOf_inter F G] at hne ⊢
  refine isBasic_unionOf ?_ hne
  intro p hp
  rw [Finset.mem_image] at hp
  obtain ⟨⟨a, b⟩, hab, rfl⟩ := hp
  rw [Finset.mem_product] at hab
  exact ⟨max_mem_E (hF a hab.1).1 (hG b hab.2).1, min_mem_E (hF a hab.1).2 (hG b hab.2).2⟩

/-- **The paper's basis `U₀`**: the finite non-empty unions of dyadic half-open
intervals of `[0, 1)`, carried as a subtype of `Set ℚ`. It is a plain `def` and
not an `abbrev` on purpose: `↥{X | IsBasic X}` would inherit Mathlib's
`Subtype.partialOrder`, which orders by `⊆` — the *opposite* of the paper's
order. -/
def U₀ : Type := {X : Set ℚ // IsBasic X}

namespace U₀

/-- The set of dyadic points a basis element names. -/
def toSet (X : U₀) : Set ℚ := X.1

theorem isBasic (X : U₀) : IsBasic (toSet X) := X.2

/-- Build a basis element from its set of points. -/
def mk (X : Set ℚ) (h : IsBasic X) : U₀ := ⟨X, h⟩

@[simp] theorem toSet_mk (X : Set ℚ) (h : IsBasic X) : toSet (mk X h) = X := rfl

@[ext] theorem ext {X Y : U₀} (h : toSet X = toSet Y) : X = Y := Subtype.ext h

theorem toSet_nonempty (X : U₀) : (toSet X).Nonempty := X.isBasic.1

theorem toSet_subset_S (X : U₀) : toSet X ⊆ S := X.isBasic.subset_S

/-- **The paper's order: superset.** In Mathlib's orientation `X ≤ Y` reads "`Y`
carries at least as much information as `X`", and more information is a narrower
set of dyadic points. -/
instance : PartialOrder U₀ where
  le X Y := toSet Y ⊆ toSet X
  le_refl _ := subset_rfl
  le_trans _ _ _ h₁ h₂ := h₂.trans h₁
  le_antisymm _ _ h₁ h₂ := U₀.ext (Set.Subset.antisymm h₂ h₁)

theorem le_iff {X Y : U₀} : X ≤ Y ↔ toSet Y ⊆ toSet X := Iff.rfl

/-- The least element is `[0, 1) = S`, exactly as the paper says. -/
instance : OrderBot U₀ where
  bot := mk S isBasic_S
  bot_le X := X.toSet_subset_S

@[simp] theorem toSet_bot : toSet (⊥ : U₀) = S := rfl

/-- `U₀` is countable: a basis element is the union of the intervals named by
*some* finite set of endpoint pairs, so `{X | IsBasic X}` is contained in the
range of `unionOf`, whose domain `Finset (ℚ × ℚ)` is countable. -/
theorem countable_isBasic : {X : Set ℚ | IsBasic X}.Countable := by
  refine Set.Countable.mono ?_ (Set.countable_range unionOf)
  rintro X ⟨-, F, -, rfl⟩
  exact ⟨F, rfl⟩

instance : Countable U₀ := countable_isBasic.to_subtype

/-- **Bounded pairs of `U₀` have least upper bounds**, and the least upper bound
of `X` and `Y` is their intersection. This is the hypothesis
`IdealCompletion.boundedComplete` consumes. Boundedness is spent exactly once, to
know the intersection is non-empty and therefore a basis element. -/
theorem exists_isLUB_pair (X Y : U₀) (h : BddAbove ({X, Y} : Set U₀)) :
    ∃ c, IsLUB ({X, Y} : Set U₀) c := by
  obtain ⟨Z, hZ⟩ := h
  have hZX : toSet Z ⊆ toSet X := le_iff.mp (hZ (Set.mem_insert X {Y}))
  have hZY : toSet Z ⊆ toSet Y := le_iff.mp (hZ (Set.mem_insert_of_mem X rfl))
  obtain ⟨s, hs⟩ := Z.toSet_nonempty
  refine ⟨mk (toSet X ∩ toSet Y) (isBasic_inter X.isBasic Y.isBasic ⟨s, hZX hs, hZY hs⟩), ?_, ?_⟩
  · rintro W (rfl | rfl)
    · exact fun a ha => ha.1
    · exact fun a ha => ha.2
  · intro W hW a ha
    exact ⟨le_iff.mp (hW (Set.mem_insert X {Y})) ha,
      le_iff.mp (hW (Set.mem_insert_of_mem X rfl)) ha⟩

end U₀

/-! ### The basis is nondegenerate

Three `def`s and a `Prop`-valued predicate can be satisfied vacuously: if `E` or
`Ivl` were mis-stated so that every basis element were `[0, 1)`, `U₀` would be a
one-point poset, every instance above would still hold, and `U` would be the
one-point cpo. `[0, 1/2)` is the witness that rules that out. -/

theorem half_mem_S : (1 / 2 : ℚ) ∈ S := ⟨1, 1, one_pos, by norm_num, by norm_num⟩

theorem half_mem_E : (1 / 2 : ℚ) ∈ E := ⟨1, 1, one_pos, by norm_num, by norm_num⟩

theorem isBasic_lowerHalf : IsBasic (Ivl 0 (1 / 2)) := by
  refine ⟨⟨0, zero_mem_S, le_rfl, by norm_num⟩, {((0 : ℚ), (1 / 2 : ℚ))}, ?_, ?_⟩
  · intro p hp
    rw [Finset.mem_singleton] at hp
    subst hp
    exact ⟨zero_mem_E, half_mem_E⟩
  · rw [unionOf_singleton]

/-- `[0, 1/2)`, a basis element strictly above the least one. -/
def lowerHalf : U₀ := U₀.mk (Ivl 0 (1 / 2)) isBasic_lowerHalf

/-- `[0, 1) < [0, 1/2)`: strictly more information, strictly fewer points. `1/2`
is the point that separates them. -/
theorem bot_lt_lowerHalf : (⊥ : U₀) < lowerHalf := by
  refine lt_of_le_of_ne bot_le fun h => ?_
  have hmem : (1 / 2 : ℚ) ∈ U₀.toSet lowerHalf := by
    rw [← h]
    exact half_mem_S
  exact absurd hmem.2.2 (lt_irrefl _)

instance : Nontrivial U₀ := ⟨⊥, lowerHalf, bot_lt_lowerHalf.ne⟩

/-! ### `U`: the domain of ideals over `U₀` -/

/-- **§7.3's universal domain `U`**: the domain of ideals over the dyadic
half-open intervals. An `abbrev` so that Theorem 11's `Domain`,
`CompletePartialOrder` and `IsAlgebraic` instances on `IdealCompletion U₀` are
found by instance search at `U`. -/
abbrev U : Type := IdealCompletion U₀

/-- `U` is a domain — Theorem 11 applied to the countable pre-order `U₀` with its
least element `[0, 1)`. -/
example : Domain U := inferInstance

/-- `U` is bounded complete: the least upper bound of a bounded pair of basis
elements is their intersection (`U₀.exists_isLUB_pair`), which is all
`IdealCompletion.boundedComplete` needs. -/
instance : BoundedComplete U := IdealCompletion.boundedComplete U₀.exists_isLUB_pair

/-! ### `K(U)` -/

/-- `↓X`, the compact element of `U` named by a basis element `X`. Its members are
the basis elements **containing** `X`, since a superset is a coarser
approximation. -/
theorem mem_principal_iff {X Y : U₀} :
    Y ∈ (IdealCompletion.principal X : U) ↔ U₀.toSet X ⊆ U₀.toSet Y :=
  IdealCompletion.mem_principal.trans U₀.le_iff

/-- **`K(U)` is the set of principal ideals over `U₀`** — the second half of
Theorem 11's conclusion, at `A = U₀`. Concretely, the compact elements of `U` are
exactly the ideals `↓X = {Y ∈ U₀ | X ⊆ Y}` for `X` a finite non-empty union of
dyadic half-open intervals. -/
theorem compacts_U : compacts U = Set.range (IdealCompletion.principal : U₀ → U) :=
  IdealCompletion.compacts_eq_range_principal

/-- An ideal of `U` is compact if and only if it is principal. -/
theorem isCompactElement_iff {I : U} :
    IsCompactElement I ↔ ∃ X : U₀, I = IdealCompletion.principal X :=
  IdealCompletion.isCompactElement_iff_exists_eq_principal

/-- **Theorem 11 at `U₀`**, both conjuncts: `U` is a domain and `K(U)` is the set
of principal ideals. -/
theorem theorem_11_at_U :
    Domain U ∧ compacts U = Set.range (IdealCompletion.principal : U₀ → U) :=
  IdealCompletion.theorem_11 U₀

/-! ## Theorem 27

> **Theorem 27** For any bounded complete domain `D`, there is a projection
> `p : U → D`.

The paper's proof runs through the Boolean algebra `B = U₀ ∪ {∅}`:

> If we adjoin the emptyset, say `B = U₀ ∪ {∅}`, then we get a Boolean algebra. …
> In particular, any interval contains a proper sub-interval so, as a Boolean
> algebra, `B` is atomless. But `B` is countable, and — up to isomorphism — the
> only countable atomless Boolean algebra is the free one on countably many
> generators. But this Boolean algebra has the property that every countable
> Boolean algebra is isomorphic to a subalgebra. Now, suppose `A` is a countable
> bounded complete poset. Let `B'` be the boolean algebra of subsets of `A`
> generated by those subsets of the form `↑x = {y ∈ A | x ⊑ y}` … if
> `j : B' → B` maps `B'` isomorphically onto a subalgebra of `B`, then the
> composition `j ∘ i` cuts down to an isomorphism between `A` and a normal
> subposet `A' ◁ U₀`.

That paragraph ends at "an isomorphism between `A` and a normal subposet
`A' ◁ U₀`" and everything after it is order theory. So the proof splits exactly
there, and the split is made a definition: `IsNormallyRepresented A` below is the
paragraph's conclusion, and `theorem_27_of_isNormallyRepresented` is everything after
it, proved.

**What is proved here and where the rest is.** `theorem_27_of_isNormallyRepresented`
is a Lean-checked theorem: from a normal subposet `N ◁ U₀` order-isomorphic to
`K(D)` it constructs the embedding–projection pair `(e, p)` with `p ∘ e = id` and
`e ∘ p ⊑ id`, which is the paper's `p : U → D`. `IsNormallyRepresented` names the
paragraph's conclusion so that this half can be stated and checked on its own.

`IsNormallyRepresented ↥(compacts D)` is **proved**, in `ScottDomains.Atomless`
(r0036), and `Atomless.theorem_27` is Theorem 27 with no hypothesis at all. Two
earlier claims made in this docstring were wrong and are corrected here. The
first was that the proof needs the uniqueness up to isomorphism of the countable
atomless Boolean algebra — Vaught's theorem, by back-and-forth. It does not: that
is how the *paper* reaches the embedding `j`, but what Theorem 27 consumes is
only that `K(D)` is order-isomorphic to a normal subposet of `U₀`, and
`Atomless.psi` builds one directly. The second was that "nothing weaker will do";
`Atomless` uses no Boolean algebra, no atomlessness, and no categoricity. What is
still true is the measurement that motivated the split: Mathlib v4.32.2 has zero
occurrences of `IsAtomless` in `Mathlib/` and zero occurrences of "atomless" in
`Mathlib/ModelTheory/`, so the paper's own route would have had to be built from
nothing.

**Where bounded completeness is spent.** Not here. The construction below needs
only `Domain D`; `BoundedComplete D` is what the paper spends in the *assumed*
half, to know that the subsets `↑x` generate a Boolean algebra in which a
bounded family has non-empty intersection. `theorem_27` records the paper's own
statement with the hypothesis in place.

**Why the construction avoids `im(p)`.** The obvious route — take
`p_N : U → U` from `NormalProjection.normalHom` and identify `im(p_N)` with `D`
— pays twice: the cpo on `im(p_N)` is `IsProjection.rangeCompletePartialOrder`,
which is not an instance (it depends on the projection *proof*), and identifying
it with `D` needs the ideal completion to be functorial on order isomorphisms.
Building `e` and `p` directly between `D` and `U` needs neither. -/

section Theorem27

universe u

variable {D : Type u} [CompletePartialOrder D] [Domain D] {N : Set U₀}

/-- **The paper's Boolean-algebra step, as a named `Prop`.** `A` is isomorphic to
a normal subposet of the basis `U₀`. For `A = K(D)` this is the last sentence of
§7.3's proof paragraph; it is the only part of Theorem 27 not proved in this
module, and `Atomless.isNormallyRepresented` proves it. -/
def IsNormallyRepresented (A : Type*) [PartialOrder A] : Prop :=
  ∃ N : Set U₀, IsNormalIn N (Set.univ : Set U₀) ∧ Nonempty (A ≃o ↥N)

variable (φ : ↥(compacts D) ≃o ↥N)

/-- `ψ : K(D) → U₀`, the order embedding underlying the hypothesis. -/
def emb (k : ↥(compacts D)) : U₀ := (φ k : U₀)

omit [Domain D] in
theorem emb_mem (k : ↥(compacts D)) : emb φ k ∈ N := (φ k).2

omit [Domain D] in
@[simp] theorem emb_le_emb {k₁ k₂ : ↥(compacts D)} : emb φ k₁ ≤ emb φ k₂ ↔ k₁ ≤ k₂ :=
  Subtype.coe_le_coe.trans φ.le_iff_le

omit [Domain D] in
theorem emb_mono : Monotone (emb φ) := fun _ _ h => (emb_le_emb φ).mpr h

omit [Domain D] in
/-- Every member of `N` is `ψ` of a compact element: `φ` is onto `N`. -/
theorem exists_emb_eq {Y : U₀} (hY : Y ∈ N) : ∃ k : ↥(compacts D), emb φ k = Y :=
  ⟨φ.symm ⟨Y, hY⟩, congrArg Subtype.val (φ.apply_symm_apply ⟨Y, hY⟩)⟩

/-- `⊥ = [0, 1)` belongs to every normal subposet: `N ∩ ↓⊥` is non-empty and
`↓⊥ = {⊥}`. -/
theorem bot_mem_of_isNormalIn (hN : IsNormalIn N (Set.univ : Set U₀)) : (⊥ : U₀) ∈ N := by
  obtain ⟨Z, hZN, hZ⟩ := hN.nonempty (Set.mem_univ (⊥ : U₀))
  have hZbot : Z = ⊥ := le_antisymm (Set.mem_Iic.mp hZ) bot_le
  rwa [hZbot] at hZN

omit [Domain D] in
/-- `ψ` preserves the least element. `K(D)`'s least element is `⊥` because `⊥` is
compact, and `N`'s is `[0, 1)` by `bot_mem_of_isNormalIn`; an order isomorphism
carries one to the other. -/
theorem emb_bot (hN : IsNormalIn N (Set.univ : Set U₀)) : emb φ (⊥ : ↥(compacts D)) = ⊥ := by
  refine le_antisymm ?_ bot_le
  have h : φ (⊥ : ↥(compacts D)) ≤ (⟨⊥, bot_mem_of_isNormalIn hN⟩ : ↥N) := by
    have hle := φ.monotone
      (bot_le : (⊥ : ↥(compacts D)) ≤ φ.symm ⟨⊥, bot_mem_of_isNormalIn hN⟩)
    rwa [φ.apply_symm_apply] at hle
  exact Subtype.coe_le_coe.mpr h

/-! ### The embedding `e : D → U` -/

/-- `e x`, as a set: the basis elements below `ψ k` for some compact `k ⊑ x`. -/
def embSet (x : D) : Set U₀ := {Y | ∃ k : ↥(compacts D), (k : D) ≤ x ∧ Y ≤ emb φ k}

theorem isIdeal_embSet (x : D) : Order.IsIdeal (embSet φ x) := by
  refine ⟨?_, ⟨emb φ ⊥, ⊥, bot_le, le_rfl⟩, ?_⟩
  · rintro Y Z hZY ⟨k, hkx, hYk⟩
    exact ⟨k, hkx, hZY.trans hYk⟩
  · rintro Y ⟨k₁, hk₁, hY⟩ Z ⟨k₂, hk₂, hZ⟩
    obtain ⟨c, ⟨hc, hcx⟩, h₁c, h₂c⟩ :=
      IsAlgebraic.directedOn_compactsBelow x (k₁ : D) ⟨k₁.2, hk₁⟩ (k₂ : D) ⟨k₂.2, hk₂⟩
    refine ⟨emb φ ⟨c, hc⟩, ⟨⟨c, hc⟩, hcx, le_rfl⟩, ?_, ?_⟩
    · exact hY.trans ((emb_le_emb φ).mpr h₁c)
    · exact hZ.trans ((emb_le_emb φ).mpr h₂c)

/-- `e x`, the ideal of basis elements approximating `x` through `ψ`. -/
def embIdeal (x : D) : U := IdealCompletion.ofIdeal (isIdeal_embSet φ x).toIdeal

theorem mem_embIdeal {x : D} {Y : U₀} :
    Y ∈ embIdeal φ x ↔ ∃ k : ↥(compacts D), (k : D) ≤ x ∧ Y ≤ emb φ k := Iff.rfl

theorem embIdeal_mono : Monotone (embIdeal φ) := by
  rintro x y hxy Y ⟨k, hkx, hY⟩
  exact ⟨k, hkx.trans hxy, hY⟩

/-- `e` is Scott-continuous. Least-upper-bound-preservation is where compactness
is spent: a compact `k ⊑ ⨆S` already sits below some member of `S`. -/
theorem scottContinuous_embIdeal : ScottContinuous (embIdeal φ) := by
  intro s hne hdir x hlub
  refine ⟨?_, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    exact embIdeal_mono φ (hlub.1 hy)
  · rintro J hJ Y ⟨k, hkx, hY⟩
    obtain ⟨z, hz, hkz⟩ := k.2 s x hne hdir hlub hkx
    exact hJ (Set.mem_image_of_mem _ hz) (show Y ∈ embIdeal φ z from ⟨k, hkz, hY⟩)

/-- The embedding `e : D → U` of Theorem 27. -/
def embHom : ScottHom D U := ⟨embIdeal φ, scottContinuous_embIdeal φ⟩

@[simp] theorem embHom_apply (x : D) : embHom φ x = embIdeal φ x := rfl

/-! ### The projection `p : U → D` -/

/-- `p I`, as a set: the compact elements of `D` whose image under `ψ` lies in the
ideal `I`. -/
def projSet (I : U) : Set D := {y | ∃ k : ↥(compacts D), emb φ k ∈ I ∧ (k : D) = y}

omit [Domain D] in
theorem projSet_nonempty (hN : IsNormalIn N (Set.univ : Set U₀)) (I : U) :
    (projSet φ I).Nonempty :=
  ⟨((⊥ : ↥(compacts D)) : D), ⊥, by rw [emb_bot φ hN]; exact IdealCompletion.bot_mem I, rfl⟩

omit [Domain D] in
/-- `p I` is directed. **This is the only place normality of `N` is used**: two
members of `I ∩ N` have an upper bound in `I`, and normality turns that into an
upper bound inside `N ∩ ↓Z`, which lies in `I` because `I` is a lower set. -/
theorem directedOn_projSet (hN : IsNormalIn N (Set.univ : Set U₀)) (I : U) :
    DirectedOn (· ≤ ·) (projSet φ I) := by
  rintro _ ⟨k₁, h₁, rfl⟩ _ ⟨k₂, h₂, rfl⟩
  obtain ⟨Z, hZ, h₁Z, h₂Z⟩ := I.directed _ h₁ _ h₂
  obtain ⟨W, ⟨hWN, hWZ⟩, hW₁, hW₂⟩ :=
    hN.directedOn (Set.mem_univ Z) (emb φ k₁) ⟨emb_mem φ k₁, h₁Z⟩ (emb φ k₂)
      ⟨emb_mem φ k₂, h₂Z⟩
  obtain ⟨k₃, rfl⟩ := exists_emb_eq φ hWN
  exact ⟨(k₃ : D), ⟨k₃, I.lower hWZ hZ, rfl⟩, (emb_le_emb φ).mp hW₁, (emb_le_emb φ).mp hW₂⟩

/-- The projection `p : U → D`, pointwise: the least upper bound in `D` of the
compact elements `I` names. -/
noncomputable def projElem (I : U) : D := sSup (projSet φ I)

omit [Domain D] in
theorem isLUB_projElem (hN : IsNormalIn N (Set.univ : Set U₀)) (I : U) :
    IsLUB (projSet φ I) (projElem φ I) := (directedOn_projSet φ hN I).isLUB_sSup

omit [Domain D] in
theorem projSet_mono {I J : U} (h : I ≤ J) : projSet φ I ⊆ projSet φ J := by
  rintro _ ⟨k, hk, rfl⟩
  exact ⟨k, h hk, rfl⟩

omit [Domain D] in
theorem projElem_mono (hN : IsNormalIn N (Set.univ : Set U₀)) : Monotone (projElem φ) :=
  fun _ _ h => (isLUB_projElem φ hN _).2
    fun _ hy => (isLUB_projElem φ hN _).1 (projSet_mono φ h hy)

omit [Domain D] in
theorem scottContinuous_projElem (hN : IsNormalIn N (Set.univ : Set U₀)) :
    ScottContinuous (projElem φ) := by
  intro s hne hdir I hlub
  refine ⟨?_, ?_⟩
  · rintro _ ⟨J, hJ, rfl⟩
    exact projElem_mono φ hN (hlub.1 hJ)
  · intro d hd
    refine (isLUB_projElem φ hN I).2 ?_
    rintro _ ⟨k, hk, rfl⟩
    rw [hlub.unique hdir.isLUB_sSup] at hk
    obtain ⟨J, hJ, hkJ⟩ := (IdealCompletion.mem_sSup_iff hne hdir).mp hk
    exact le_trans ((isLUB_projElem φ hN J).1 ⟨k, hkJ, rfl⟩) (hd (Set.mem_image_of_mem _ hJ))

/-- The projection `p : U → D` of Theorem 27. -/
noncomputable def projHom (hN : IsNormalIn N (Set.univ : Set U₀)) : ScottHom U D :=
  ⟨projElem φ, scottContinuous_projElem φ hN⟩

omit [Domain D] in
@[simp] theorem projHom_apply (hN : IsNormalIn N (Set.univ : Set U₀)) (I : U) :
    projHom φ hN I = projElem φ I := rfl

/-! ### `(e, p)` is an embedding–projection pair -/

/-- `p ∘ e = id` reduces to a set identity: the compacts named by `e x` are
exactly the compact approximants of `x`, whose least upper bound is `x` by
algebraicity. -/
theorem projSet_embIdeal (x : D) : projSet φ (embIdeal φ x) = compactsBelow x := by
  ext y
  constructor
  · rintro ⟨k, ⟨k', hk'x, hkk'⟩, rfl⟩
    exact ⟨k.2, le_trans ((emb_le_emb φ).mp hkk') hk'x⟩
  · rintro ⟨hy, hyx⟩
    exact ⟨⟨y, hy⟩, ⟨⟨y, hy⟩, hyx, le_rfl⟩, rfl⟩

theorem projElem_embIdeal (hN : IsNormalIn N (Set.univ : Set U₀)) (x : D) :
    projElem φ (embIdeal φ x) = x := by
  have h : IsLUB (compactsBelow x) (projElem φ (embIdeal φ x)) := by
    rw [← projSet_embIdeal φ x]
    exact isLUB_projElem φ hN (embIdeal φ x)
  exact h.unique (IsAlgebraic.isLUB_compactsBelow x)

/-- `e ∘ p ⊑ id`: a compact `k` below `⨆(p I)` already sits below some `k'` with
`ψ k' ∈ I`, so `ψ k ∈ I` and every `Y ⊑ ψ k` is in `I`. -/
theorem embIdeal_projElem_le (hN : IsNormalIn N (Set.univ : Set U₀)) (I : U) :
    embIdeal φ (projElem φ I) ≤ I := by
  rintro Y ⟨k, hk, hY⟩
  obtain ⟨_, ⟨k', hk', rfl⟩, hkk'⟩ :=
    k.2 (projSet φ I) (projElem φ I) (projSet_nonempty φ hN I) (directedOn_projSet φ hN I)
      (isLUB_projElem φ hN I) hk
  exact I.lower (hY.trans ((emb_le_emb φ).mpr hkk')) hk'

/-- **Theorem 27, everything after the Boolean algebra.** Given the paper's
isomorphism between `K(D)` and a normal subposet of `U₀`, the pair `(e, p)`
built above is an embedding–projection pair `D ⇄ U`; in particular `p : U → D`
is the projection the theorem asserts. Bounded completeness of `D` is not used —
it is spent in the hypothesis. -/
theorem theorem_27_of_isNormallyRepresented (D : Type u) [CompletePartialOrder D] [Domain D]
    (h : IsNormallyRepresented ↥(compacts D)) :
    ∃ (e : ScottHom D U) (p : ScottHom U D), ScottHom.IsEmbeddingProjectionPair e p := by
  obtain ⟨N, hN, ⟨φ⟩⟩ := h
  exact ⟨embHom φ, projHom φ hN,
    projElem_embIdeal φ hN, embIdeal_projElem_le φ hN⟩

/-- **Theorem 27** as the paper states it, with the Boolean-algebra step carried
as a named hypothesis: *for any bounded complete domain `D` there is a projection
`p : U → D`*. `Atomless.theorem_27` is the same statement with the hypothesis
discharged; this form is kept because it is the one whose proof lives here, and
because it records exactly where the paragraph was cut. -/
theorem theorem_27 (D : Type u) [CompletePartialOrder D] [Domain D] [BoundedComplete D]
    (h : IsNormallyRepresented ↥(compacts D)) :
    ∃ (e : ScottHom D U) (p : ScottHom U D), ScottHom.IsEmbeddingProjectionPair e p :=
  theorem_27_of_isNormallyRepresented D h

end Theorem27

end ScottDomains.Dyadic
