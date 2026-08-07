import ScottDomains.IdealCompletion

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
with a least element into a `Domain`, and `IdealCompletion.thm11` records that
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
  `X` ranging over `U₀`; `thm11_at_U` is the pair.
-/

namespace ScottDomains.Dyadic

open Set

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
  have h2 : (0 : ℚ) < 2 ^ m := by positivity
  refine ⟨div_nonneg (by positivity) h2.le, (div_lt_one h2).mpr ?_⟩
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
  simp only [mem_Ivl, mem_inter_iff, max_le_iff, lt_min_iff]
  tauto

/-! ### `U₀`: finite non-empty unions of intervals -/

/-- The union of the intervals named by a finite set of endpoint pairs. -/
def unionOf (F : Finset (ℚ × ℚ)) : Set ℚ := ⋃ p ∈ F, Ivl p.1 p.2

theorem mem_unionOf {F : Finset (ℚ × ℚ)} {s : ℚ} :
    s ∈ unionOf F ↔ ∃ p ∈ F, s ∈ Ivl p.1 p.2 := by
  simp [unionOf]

theorem unionOf_subset_S {F : Finset (ℚ × ℚ)} : unionOf F ⊆ S := by
  intro s hs
  obtain ⟨p, -, hp⟩ := mem_unionOf.mp hs
  exact Ivl_subset_S hp

@[simp] theorem unionOf_singleton (r t : ℚ) : unionOf {(r, t)} = Ivl r t := by
  ext s
  simp [mem_unionOf]

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
  simp only [mem_inter_iff, mem_unionOf, Finset.mem_image, Finset.mem_product]
  constructor
  · rintro ⟨⟨p, hp, hsp⟩, q, hq, hsq⟩
    refine ⟨(max p.1 q.1, min p.2 q.2), ⟨(p, q), ⟨hp, hq⟩, rfl⟩, ?_⟩
    rw [← Ivl_inter]
    exact ⟨hsp, hsq⟩
  · rintro ⟨x, ⟨⟨p, q⟩, ⟨hp, hq⟩, rfl⟩, hs⟩
    rw [← Ivl_inter] at hs
    exact ⟨⟨p, hp, hs.1⟩, q, hq, hs.2⟩

theorem isBasic_inter {X Y : Set ℚ} (hX : IsBasic X) (hY : IsBasic Y)
    (hne : (X ∩ Y).Nonempty) : IsBasic (X ∩ Y) := by
  obtain ⟨-, F, hF, rfl⟩ := hX
  obtain ⟨-, G, hG, rfl⟩ := hY
  refine ⟨hne, (F ×ˢ G).image fun pq => (max pq.1.1 pq.2.1, min pq.1.2 pq.2.2), ?_,
    unionOf_inter F G⟩
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
  le_antisymm _ _ h₁ h₂ := ext (Subset.antisymm h₂ h₁)

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
  have hZX : toSet Z ⊆ toSet X := hZ (mem_insert X {Y})
  have hZY : toSet Z ⊆ toSet Y := hZ (mem_insert_of_mem X rfl)
  obtain ⟨s, hs⟩ := Z.toSet_nonempty
  refine ⟨mk (toSet X ∩ toSet Y) (isBasic_inter X.isBasic Y.isBasic ⟨s, hZX hs, hZY hs⟩), ?_, ?_⟩
  · rintro W (rfl | rfl)
    · exact fun a ha => ha.1
    · exact fun a ha => ha.2
  · intro W hW a ha
    exact ⟨hW (mem_insert X {Y}) ha, hW (mem_insert_of_mem X rfl) ha⟩

end U₀

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
    Y ∈ (IdealCompletion.principal X : U) ↔ U₀.toSet X ⊆ U₀.toSet Y := Iff.rfl

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
theorem thm11_at_U :
    Domain U ∧ compacts U = Set.range (IdealCompletion.principal : U₀ → U) :=
  IdealCompletion.thm11 U₀

end ScottDomains.Dyadic
