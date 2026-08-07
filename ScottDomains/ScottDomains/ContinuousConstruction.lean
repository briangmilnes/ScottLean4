import ScottDomains.FunctionSpaceDomain
import ScottDomains.MinimalUpperBounds
import ScottDomains.Projection

/-!
# Constructing continuous functions on a domain that is not bounded complete

Everything §6.2 does with continuous functions, `CompactFunction.lean` does under
`[BoundedComplete β]`: a compact function is a *finite join* of step functions,
and that join is the pointwise supremum of a **bounded** — not directed — family,
which only bounded completeness supplies. Theorem 18 exists precisely to remove
that hypothesis, so its proof cannot use any of it. Round r0028 stopped there:

> the perturbing family `qₙ` has no general construction in this development …
> the natural formulas all take a least upper bound of a bounded, not directed,
> set, which is exactly what a non-bounded-complete `D` need not have.

This file removes the obstruction. The observation it turns on is that
`ScottHom.scottContinuous_pointwiseSup_of_forall_isLUB` never needed the *family*
to be directed — only each **evaluation image** to attain its supremum. So a
family of step functions may be wildly non-directed as a set of functions and
still define a continuous function, provided that at each point the values it
offers are directed. That condition is checkable, and two large classes satisfy
it outright.

## The constructor

A family is a set `s ⊆ D × E` of pairs, read as "offer at least `e` once `k` has
arrived". It defines

    familyFun s x = ⨆ {e | (k, e) ∈ s and k ⊑ x}.

`scottContinuous_familyFun` proves this Scott continuous from two hypotheses:
every `k` occurring in `s` is compact, and `valuesAt s x` is directed for each
`x`. Compactness is spent exactly once — to pull `k ⊑ ⨆M` back to `k ⊑ z` for
some `z ∈ M` — which is the same single use `StepFunction.lean` makes of it.
There is no completeness hypothesis on `D` at all, and no bounded completeness
anywhere.

`familyFun_le_iff` is the adjunction, generalizing `ScottHom.step_le_iff` from one
pair to a family:

    (∀ x, familyFun s x ⊑ f x) ↔ ∀ (k, e) ∈ s, e ⊑ f k

for monotone `f`. Every later fact is proved through it rather than by unfolding
the supremum, and it is what makes `isLUB_of_iUnion` — a union of families is the
least upper bound of its pieces — a fifteen-line proof.

## The two classes of admissible families

* **A monotone assignment on the basis.** For `v` monotone on `K(D)` the graph
  `{(k, v k) | k ∈ K(D)}` has `valuesAt = v '' compactsBelow x`, the monotone
  image of a directed set. So `basisExtension` extends *any* monotone assignment
  on `K(D)` to a continuous `D → E` agreeing with it there, and
  `eq_basisExtension_of_eqOn` shows it is the only continuous function that does.
  This is r0028's stated prerequisite — "the least continuous function above a
  given monotone partial assignment on `K(D)`" — supplied in full, and
  `coe_eq_basisExtension_self` reads it back as a structure theorem: every
  continuous function *is* the basis extension of its own restriction to `K(D)`,
  with no bounded completeness where `CompactFunction.lean` needs it.

* **A family totally ordered in both coordinates.** Then `valuesAt s x` is a
  chain, hence directed, with no algebraicity used at all. `shift` is the instance
  §6.2 asks for: along a strictly descending chain `x₀ ⊐ x₁ ⊐ …` of compacts it is
  the continuous function with `shift (xₙ) = xₙ₊₁` and `shift z ⊑ z` everywhere —
  the perturbation r0028 could write down only inside a hand-worked example.

## What this buys Theorem 18, and what still blocks it

Figure 3(a) is a finite `u ⊆ K(D)` with no complete set of minimal upper bounds.
Three steps below it are proved here:

1. `exists_isCompactElement_le` — from algebraicity of `D → D`, any finite
   `u ⊆ K(D)` and any `f` with `k ⊑ f k` on `u` admit a **compact** `g ⊑ f` with
   `k ⊑ g k` on `u`. Taking `f = idHom` gives the compact `g ⊑ id` fixing `u`.
2. `apply_mem_upperBounds` — such a `g` carries upper bounds of `u` to upper
   bounds of `u`, and `g ⊑ id` puts the image below its argument. So
   `g '' ub(u)` is a *complete set of upper bounds*.
3. `hasCompleteMub_of_finite_image` — a **finite** complete set of upper bounds
   inside `A` yields a complete set of minimal upper bounds, by the
   minimal-in-a-finite-complete-set argument of `hasCompleteMub_of_isNormalIn`.

Figure 3(b) — infinitely many minimal upper bounds — reduces to the *same*
statement: `minimalUpperBounds_subset_image` shows every minimal upper bound is
fixed by such a `g`, hence lies in that image.

So cases (a) and (b) reduce to one statement, and only one: *a compact deflation
has a finite image on the upper bounds of `u`*. That is Smyth's crux, and it is
not proved here. `exists_strictAnti_of_not_hasCompleteMub` records the other side
of the intended contradiction — failure of completeness produces a strictly
descending sequence of upper bounds in `K(D)`, which is exactly what `shift`
consumes — but the two ends are not joined; the report states the failing step.

The last section shows the finiteness asked for is not merely necessary:
`isBifinite_of_exists_finite_projection` proves that a domain in which every
finite set of compacts sits inside the range of a projection with finite range
*is* bifinite. Its range is the finite normal subposet, mub-closed by
`minimalUpperBounds_subset_image` and mub-complete by
`hasCompleteMub_of_finite_image`. That is the shape Theorem 18 needs its argument
to deliver, and it is proved here once and for all.
-/

namespace ScottDomains

namespace ContinuousConstruction

variable {α β : Type*}

/-! ## Families of pairs and the function they define -/

section Values

variable [PartialOrder α] {s t : Set (α × β)} {x y : α}

/-- The values the family `s` offers at `x`: the second coordinates of those
pairs whose first coordinate has arrived. -/
def valuesAt (s : Set (α × β)) (x : α) : Set β := {b | ∃ p ∈ s, p.1 ≤ x ∧ p.2 = b}

theorem mem_valuesAt {b : β} : b ∈ valuesAt s x ↔ ∃ p ∈ s, p.1 ≤ x ∧ p.2 = b := Iff.rfl

theorem mem_valuesAt_of_mem {p : α × β} (hp : p ∈ s) (h : p.1 ≤ x) :
    p.2 ∈ valuesAt s x := ⟨p, hp, h, rfl⟩

theorem valuesAt_mono_family (hst : s ⊆ t) : valuesAt s x ⊆ valuesAt t x := by
  rintro _ ⟨p, hp, hpx, rfl⟩
  exact ⟨p, hst hp, hpx, rfl⟩

theorem valuesAt_mono_point (hxy : x ≤ y) : valuesAt s x ⊆ valuesAt s y := by
  rintro _ ⟨p, hp, hpx, rfl⟩
  exact ⟨p, hp, hpx.trans hxy, rfl⟩

end Values

section Family

variable [PartialOrder α] [CompletePartialOrder β] {s : Set (α × β)} {x : α}

/-- The function a family defines: at `x`, the supremum of the values offered
there. Nothing is asserted about it until `valuesAt s x` is known to be directed —
on a non-directed set `sSup` is the junk value of the `SupSet` instance. -/
def familyFun (s : Set (α × β)) : α → β := fun x => sSup (valuesAt s x)

variable (hd : ∀ x, DirectedOn (· ≤ ·) (valuesAt s x))
include hd

/-- The defining property: on a pointwise-directed family the value at `x` *is*
the least upper bound of the values offered at `x`. -/
theorem isLUB_familyFun (x : α) : IsLUB (valuesAt s x) (familyFun s x) := (hd x).isLUB_sSup

theorem le_familyFun {p : α × β} (hp : p ∈ s) (h : p.1 ≤ x) : p.2 ≤ familyFun s x :=
  (isLUB_familyFun hd x).1 (mem_valuesAt_of_mem hp h)

theorem monotone_familyFun : Monotone (familyFun s) := fun _ _ hxy =>
  (isLUB_familyFun hd _).2 fun _ hb => (isLUB_familyFun hd _).1 (valuesAt_mono_point hxy hb)

/-- **The adjunction.** `familyFun s` sits below a monotone `f` exactly when each
pair's value sits below `f`'s value at that pair's key. This generalizes
`ScottHom.step_le_iff`, and every statement about a family below is proved through
it rather than by unfolding the supremum. -/
theorem familyFun_le_iff {f : α → β} (hf : Monotone f) :
    (∀ z, familyFun s z ≤ f z) ↔ ∀ p ∈ s, p.2 ≤ f p.1 := by
  constructor
  · exact fun h p hp => (le_familyFun hd hp le_rfl).trans (h p.1)
  · intro h z
    refine (isLUB_familyFun hd z).2 ?_
    rintro _ ⟨p, hp, hpz, rfl⟩
    exact (h p hp).trans (hf hpz)

/-- **The constructor.** A family whose keys are compact and whose values are
directed at every point defines a Scott-continuous function.

Compactness is spent exactly once, in the second half: a value offered at
`a = ⨆M` comes with a compact key `k ⊑ a`, which some `z ∈ M` already dominates,
so that value is already offered at `z`. The first half is monotonicity, which
needs nothing but directedness. -/
theorem scottContinuous_familyFun (hk : ∀ p ∈ s, IsCompactElement p.1) :
    ScottContinuous (familyFun s) := by
  intro d hne hdd a ha
  constructor
  · rintro _ ⟨z, hz, rfl⟩
    exact monotone_familyFun hd (ha.1 hz)
  · intro w hw
    refine (isLUB_familyFun hd a).2 ?_
    rintro _ ⟨p, hp, hpa, rfl⟩
    obtain ⟨z, hz, hpz⟩ := hk p hp d a hne hdd ha hpa
    exact (le_familyFun hd hp hpz).trans (hw ⟨z, hz, rfl⟩)

/-- The family as an element of the function space. -/
def family (hk : ∀ p ∈ s, IsCompactElement p.1) : ScottHom α β :=
  ⟨familyFun s, scottContinuous_familyFun hd hk⟩

@[simp] theorem coe_family (hk : ∀ p ∈ s, IsCompactElement p.1) :
    ⇑(family hd hk) = familyFun s := rfl

end Family

section Union

variable [PartialOrder α] [CompletePartialOrder β]

/-- **A union of families is the least upper bound of its pieces.** Stated on the
coercions rather than on `family` itself, so that no proof term appears in the
statement.

Both halves are the adjunction: each piece sits below the union because its pairs
are pairs of the union, and the union sits below any common bound `H` because each
of its pairs lies in some piece, whose value at that key is already `⊑ H`. -/
theorem isLUB_of_iUnion {ι : Type*} {s : ι → Set (α × β)} {F : ScottHom α β}
    {G : ι → ScottHom α β} (hG : ∀ i, ⇑(G i) = familyFun (s i))
    (hF : ⇑F = familyFun (⋃ i, s i))
    (hds : ∀ i x, DirectedOn (· ≤ ·) (valuesAt (s i) x))
    (hdt : ∀ x, DirectedOn (· ≤ ·) (valuesAt (⋃ i, s i) x)) :
    IsLUB (Set.range G) F := by
  have hG' : ∀ i z, (G i) z = familyFun (s i) z := fun i z => congrFun (hG i) z
  have hF' : ∀ z, F z = familyFun (⋃ i, s i) z := fun z => congrFun hF z
  constructor
  · rintro _ ⟨i, rfl⟩ z
    show (G i) z ≤ F z
    rw [hG', hF']
    exact (familyFun_le_iff (hds i) (monotone_familyFun hdt)).mpr
      (fun p hp => le_familyFun hdt (Set.mem_iUnion_of_mem i hp) le_rfl) z
  · intro H hH z
    show F z ≤ H z
    rw [hF']
    refine (familyFun_le_iff hdt H.monotone).mpr ?_ z
    intro p hp
    obtain ⟨i, hpi⟩ := Set.mem_iUnion.mp hp
    calc p.2 ≤ familyFun (s i) p.1 := le_familyFun (hds i) hpi le_rfl
      _ = (G i) p.1 := (hG' i p.1).symm
      _ ≤ H p.1 := hH ⟨i, rfl⟩ p.1

end Union

/-! ## Class 1: a monotone assignment on the basis

The graph of a monotone assignment on `K(D)` is pointwise directed for free,
because `valuesAt` is then the monotone image of `compactsBelow x`. -/

section BasisExtension

variable [CompletePartialOrder α] [IsAlgebraic α] [CompletePartialOrder β] {v : α → β} {k : α}

/-- The graph of `v` over the compact elements — the family that reads "at each
compact `k`, offer `v k`". -/
def graphOn (v : α → β) : Set (α × β) := {p | IsCompactElement p.1 ∧ p.2 = v p.1}

omit [IsAlgebraic α] [CompletePartialOrder β] in
theorem valuesAt_graphOn (v : α → β) (x : α) :
    valuesAt (graphOn v) x = v '' compactsBelow x := by
  ext b
  constructor
  · rintro ⟨⟨k, e⟩, ⟨hk, he⟩, hkx, rfl⟩
    exact ⟨k, ⟨hk, hkx⟩, he.symm⟩
  · rintro ⟨k, ⟨hk, hkx⟩, rfl⟩
    exact ⟨(k, v k), ⟨hk, rfl⟩, hkx, rfl⟩

/-- Monotonicity on the basis is exactly what makes the graph pointwise directed:
`compactsBelow x` is directed by algebraicity, and a monotone image of a directed
set is directed. -/
theorem directedOn_valuesAt_graphOn (hv : MonotoneOn v (compacts α)) (x : α) :
    DirectedOn (· ≤ ·) (valuesAt (graphOn v) x) := by
  rw [valuesAt_graphOn]
  rintro _ ⟨k₁, hk₁, rfl⟩ _ ⟨k₂, hk₂, rfl⟩
  obtain ⟨k₃, hk₃, h₁, h₂⟩ := IsAlgebraic.directedOn_compactsBelow x k₁ hk₁ k₂ hk₂
  exact ⟨v k₃, ⟨k₃, hk₃, rfl⟩, hv hk₁.1 hk₃.1 h₁, hv hk₂.1 hk₃.1 h₂⟩

/-- **Every monotone assignment on `K(D)` extends to a continuous function.** No
bounded completeness, and no condition on `E` beyond being a cpo. This is the
constructor r0028 named as the missing prerequisite. -/
def basisExtension (v : α → β) (hv : MonotoneOn v (compacts α)) : ScottHom α β :=
  family (directedOn_valuesAt_graphOn hv) fun _ hp => hp.1

@[simp] theorem coe_basisExtension (hv : MonotoneOn v (compacts α)) :
    ⇑(basisExtension v hv) = familyFun (graphOn v) := rfl

theorem isLUB_basisExtension (hv : MonotoneOn v (compacts α)) (x : α) :
    IsLUB (v '' compactsBelow x) (basisExtension v hv x) := by
  rw [← valuesAt_graphOn]
  exact isLUB_familyFun (directedOn_valuesAt_graphOn hv) x

/-- The extension **agrees with the assignment on the basis**: `compactsBelow k`
has `k` itself as greatest element, so the supremum is attained at `v k`. -/
theorem basisExtension_apply_of_isCompactElement (hv : MonotoneOn v (compacts α))
    (hk : IsCompactElement k) : basisExtension v hv k = v k := by
  refine (isLUB_basisExtension hv k).unique ⟨?_, fun b hb => hb ⟨k, ⟨hk, le_rfl⟩, rfl⟩⟩
  rintro _ ⟨k', ⟨hk', hk'k⟩, rfl⟩
  exact hv hk' hk hk'k

/-- **Uniqueness.** A continuous function is determined by its restriction to
`K(D)`: one that agrees with `v` on the compacts *is* the basis extension of `v`.
Continuity plus algebraicity is the whole proof — `f x` is the supremum of
`f '' compactsBelow x`, and that image is `v '' compactsBelow x`. -/
theorem eq_basisExtension_of_eqOn (hv : MonotoneOn v (compacts α)) (f : ScottHom α β)
    (hf : ∀ k, IsCompactElement k → f k = v k) : ⇑f = basisExtension v hv := by
  funext x
  have himg : ⇑f '' compactsBelow x = v '' compactsBelow x :=
    Set.image_congr fun k hk => hf k hk.1
  have hfx : IsLUB (⇑f '' compactsBelow x) (f x) :=
    f.scottContinuous (compactsBelow_nonempty x) (IsAlgebraic.directedOn_compactsBelow x)
      (IsAlgebraic.isLUB_compactsBelow x)
  rw [himg] at hfx
  exact hfx.unique (isLUB_basisExtension hv x)

/-- **Structure theorem.** Every continuous function is the basis extension of its
own restriction to `K(D)` — the decomposition `CompactFunction.lean` obtains only
under `[BoundedComplete β]`, here with no such hypothesis. -/
theorem coe_eq_basisExtension_self (f : ScottHom α β) :
    ⇑f = basisExtension ⇑f (f.monotone.monotoneOn _) :=
  eq_basisExtension_of_eqOn _ f fun _ _ => rfl

end BasisExtension

/-! ## Class 2: families totally ordered in both coordinates

Here `valuesAt s x` is a chain, hence directed, with no algebraicity and no
condition on the ambient order. This is the class the §6.2 perturbations live
in. -/

section Chain

variable [PartialOrder α] [CompletePartialOrder β] {s : Set (α × β)}

/-- A family whose pairs are pairwise comparable in *both* coordinates is
pointwise directed: the larger of two pairs offers its value wherever the smaller
one does. -/
theorem directedOn_valuesAt_of_comparable
    (h : ∀ p ∈ s, ∀ q ∈ s, (p.1 ≤ q.1 ∧ p.2 ≤ q.2) ∨ (q.1 ≤ p.1 ∧ q.2 ≤ p.2)) (x : α) :
    DirectedOn (· ≤ ·) (valuesAt s x) := by
  rintro _ ⟨p, hp, hpx, rfl⟩ _ ⟨q, hq, hqx, rfl⟩
  rcases h p hp q hq with ⟨_, h₂⟩ | ⟨_, h₂⟩
  · exact ⟨q.2, mem_valuesAt_of_mem hq hqx, h₂, le_rfl⟩
  · exact ⟨p.2, mem_valuesAt_of_mem hp hpx, le_rfl, h₂⟩

end Chain

section Shift

variable [CompletePartialOrder α] {x : ℕ → α}

/-- The family of a descending sequence: "once `xₙ` has arrived, offer `xₙ₊₁`". -/
def chainFamily (x : ℕ → α) : Set (α × α) := Set.range fun n => (x n, x (n + 1))

theorem directedOn_valuesAt_chainFamily (hx : StrictAnti x) (z : α) :
    DirectedOn (· ≤ ·) (valuesAt (chainFamily x) z) := by
  refine directedOn_valuesAt_of_comparable ?_ z
  rintro _ ⟨m, rfl⟩ _ ⟨n, rfl⟩
  rcases le_total m n with h | h
  · exact Or.inr ⟨hx.antitone h, hx.antitone (Nat.succ_le_succ h)⟩
  · exact Or.inl ⟨hx.antitone h, hx.antitone (Nat.succ_le_succ h)⟩

/-- **The shift along a strictly descending chain of compacts**: the continuous
function sending each `xₙ` to `xₙ₊₁` and staying below the identity. This is the
perturbation §6.2 needs, and the one r0028 could exhibit only inside a hand-worked
example. -/
def shift (hx : StrictAnti x) (hc : ∀ n, IsCompactElement (x n)) : ScottHom α α :=
  family (directedOn_valuesAt_chainFamily hx) (by rintro _ ⟨n, rfl⟩; exact hc n)

/-- The shift is a deflation: every value it offers at `z` is below `z`. -/
theorem shift_apply_le (hx : StrictAnti x) (hc : ∀ n, IsCompactElement (x n)) (z : α) :
    shift hx hc z ≤ z := by
  refine (isLUB_familyFun (directedOn_valuesAt_chainFamily hx) z).2 ?_
  rintro _ ⟨_, ⟨n, rfl⟩, hnz, rfl⟩
  exact (hx (Nat.lt_succ_self n)).le.trans hnz

/-- The shift moves the chain one step down. Strictness is what pins the value:
`xₘ ⊑ xₙ` forces `n ≤ m`, so every value offered at `xₙ` is below `xₙ₊₁`, which is
itself offered there. -/
theorem shift_chain (hx : StrictAnti x) (hc : ∀ n, IsCompactElement (x n)) (n : ℕ) :
    shift hx hc (x n) = x (n + 1) := by
  refine (isLUB_familyFun (directedOn_valuesAt_chainFamily hx) (x n)).unique ⟨?_, ?_⟩
  · rintro _ ⟨_, ⟨m, rfl⟩, hmn, rfl⟩
    have hnm : n ≤ m := by
      by_contra hlt
      exact absurd (hmn.trans_lt (hx (Nat.lt_of_not_le hlt))) (lt_irrefl _)
    exact hx.antitone (Nat.succ_le_succ hnm)
  · exact fun b hb => hb ⟨(x n, x (n + 1)), ⟨n, rfl⟩, le_rfl, rfl⟩

end Shift

/-! ## Towards Theorem 18, Figure 3(a) -/

section CaseA

variable [CompletePartialOrder α] {k : α} {u : Set α}

/-- The identity of the function space.

`ScottHom.id` in `FinitaryProjectionPoset.lean` is the same function, but that
file imports `Skeleton/Section6.lean`, which imports this one — so the identity is
declared again here, under a different name and in this namespace, to keep the
import graph acyclic. -/
def idHom : ScottHom α α := ⟨_root_.id, ScottContinuous.id⟩

@[simp] theorem idHom_apply (z : α) : (idHom : ScottHom α α) z = z := rfl

/-- `g ⊑ id` unfolded: a **deflation**. True by `rfl` — the order on the function
space is the pointwise order. -/
theorem le_idHom_iff {g : ScottHom α α} : g ≤ idHom ↔ ∀ z, g z ≤ z := Iff.rfl

open Classical in
/-- The diagonal step function `step k k`, made total in `k` so that a *set* of
them is the image of a set of elements and inherits its finiteness. Off the
compacts the value is `⊥`, which no result below reads. -/
noncomputable def diagStep (k : α) : ScottHom α α :=
  if hk : IsCompactElement k then ScottHom.step hk k else ⊥

theorem diagStep_of_isCompactElement (hk : IsCompactElement k) :
    diagStep k = ScottHom.step hk k := by
  classical exact dif_pos hk

theorem isCompactElement_diagStep (hk : IsCompactElement k) :
    IsCompactElement (diagStep k) := by
  rw [diagStep_of_isCompactElement hk]
  exact ScottHom.isCompactElement_step hk hk

/-- The adjunction for the diagonal step function: `step k k ⊑ f` says exactly
that `f` moves `k` no lower than `k`. -/
theorem diagStep_le_iff (hk : IsCompactElement k) {f : ScottHom α α} :
    diagStep k ≤ f ↔ k ≤ f k := by
  rw [diagStep_of_isCompactElement hk]
  exact ScottHom.step_le_iff hk

/-- **The entry point of Smyth's argument.** If `D → D` is algebraic then for any
finite `u ⊆ K(D)` and any continuous `f` moving no member of `u` down, there is a
**compact** `g ⊑ f` that also moves no member of `u` down.

The diagonal step functions `step k k` for `k ∈ u` are compact and below `f`, so
they are finitely many members of the directed set `compactsBelow f`, and
`exists_mem_upperBounds_of_directedOn` collapses them to a single `g` there.

Taking `f = idHom` gives the compact `g ⊑ id` with `g k = k` on `u` that Figure
3(a) is about: `g k ⊑ k` from `g ⊑ id`, and `k ⊑ g k` from the conclusion. -/
theorem exists_isCompactElement_le [IsAlgebraic (ScottHom α α)] {f : ScottHom α α}
    (hu : u.Finite) (huc : u ⊆ compacts α) (hf : ∀ k ∈ u, k ≤ f k) :
    ∃ g : ScottHom α α, IsCompactElement g ∧ g ≤ f ∧ ∀ k ∈ u, k ≤ g k := by
  have hcov : ∀ y ∈ diagStep '' u, ∃ z ∈ compactsBelow f, y ≤ z := by
    rintro _ ⟨k, hk, rfl⟩
    exact ⟨diagStep k, ⟨isCompactElement_diagStep (huc hk),
      (diagStep_le_iff (huc hk)).mpr (hf k hk)⟩, le_rfl⟩
  obtain ⟨g, hg, hgub⟩ :=
    exists_mem_upperBounds_of_directedOn (IsAlgebraic.directedOn_compactsBelow f)
      (compactsBelow_nonempty f) (hu.image diagStep) hcov
  exact ⟨g, hg.1, hg.2, fun k hk => (diagStep_le_iff (huc hk)).mp (hgub _ ⟨k, hk, rfl⟩)⟩

end CaseA

section Deflation

variable [Preorder α] {u : Set α} {g : α → α}

/-- A monotone map moving no member of `u` down carries upper bounds of `u` to
upper bounds of `u`. -/
theorem apply_mem_upperBounds (hmono : Monotone g) (hgu : ∀ k ∈ u, k ≤ g k) {z : α}
    (hz : z ∈ upperBounds u) : g z ∈ upperBounds u :=
  fun k hk => (hgu k hk).trans (hmono (hz hk))

end Deflation

section FiniteImage

variable [PartialOrder α] {u A : Set α} {g : α → α}

/-- **Figure 3(a) reduced to one finiteness statement.** Let `g` be monotone, a
deflation (`g z ⊑ z`), and fix `u` from below (`k ⊑ g k` on `u`). If the image
under `g` of the upper bounds of `u` in `A` is finite and lands back in `A`, then
`u` has a complete set of minimal upper bounds in `A`.

That image is a *complete set of upper bounds*: `g z` is an upper bound of `u` and
`g z ⊑ z`. Minimality inside a finite complete set upgrades to minimality
outright — for an upper bound `y ⊑ m` the element `g y` is again in the finite set
and below `y`, so minimality of `m` gives `m ⊑ g y ⊑ y`. This is the argument of
`hasCompleteMub_of_isNormalIn` with `g '' ub(u)` in place of `N ∩ ↓x`. -/
theorem hasCompleteMub_of_finite_image (hmono : Monotone g) (hgle : ∀ z, g z ≤ z)
    (hgu : ∀ k ∈ u, k ≤ g k) (hfin : (g '' upperBoundsIn A u).Finite)
    (hsub : g '' upperBoundsIn A u ⊆ A) : HasCompleteMub A u := by
  intro z hz
  set S : Set α := {y | y ∈ g '' upperBoundsIn A u ∧ y ∈ upperBounds u ∧ y ≤ z}
  have hSfin : S.Finite := hfin.subset fun _ hy => hy.1
  have hgz : g z ∈ S := ⟨⟨z, hz, rfl⟩, apply_mem_upperBounds hmono hgu hz.2, hgle z⟩
  obtain ⟨m, _, hmS, hmmin⟩ := hSfin.exists_le_minimal hgz
  refine ⟨m, ⟨⟨hsub hmS.1, hmS.2.1⟩, ?_⟩, hmS.2.2⟩
  intro y hy hym
  have hgy : g y ∈ S :=
    ⟨⟨y, hy, rfl⟩, apply_mem_upperBounds hmono hgu hy.2, (hgle y).trans (hym.trans hmS.2.2)⟩
  exact (hmmin hgy ((hgle y).trans hym)).trans (hgle y)

/-- **Figure 3(b) reduces to the same finiteness statement.** Every minimal upper
bound of `u` in `A` is *fixed* by such a `g`, so it lies in the image: `g m` is an
upper bound of `u` in `A` below `m`, and minimality of `m` forces `m ⊑ g m`.
Finiteness of the image therefore bounds the minimal upper bounds as well. -/
theorem minimalUpperBounds_subset_image (hmono : Monotone g) (hgle : ∀ z, g z ≤ z)
    (hgu : ∀ k ∈ u, k ≤ g k) (hsub : g '' upperBoundsIn A u ⊆ A) :
    minimalUpperBounds A u ⊆ g '' upperBoundsIn A u := by
  rintro m ⟨hmub, hmin⟩
  have hgm : g m ∈ upperBoundsIn A u :=
    ⟨hsub ⟨m, hmub, rfl⟩, apply_mem_upperBounds hmono hgu hmub.2⟩
  exact ⟨m, hmub, le_antisymm (hgle m) (hmin hgm (hgle m))⟩

/-- **The other side of Figure 3(a).** If `u` has *no* complete set of minimal
upper bounds in `A`, then `A` contains a strictly descending sequence of upper
bounds of `u`.

Some upper bound `x₀` has no minimal upper bound below it; then *every* upper
bound below `x₀` is non-minimal, since a minimal one would itself be below `x₀`.
Choice turns that into a descent function and `Function.iterate` into the
sequence. This is the input `shift` consumes. -/
theorem exists_strictAnti_of_not_hasCompleteMub (h : ¬ HasCompleteMub A u) :
    ∃ x : ℕ → α, (∀ n, x n ∈ upperBoundsIn A u) ∧ StrictAnti x := by
  classical
  have h' : ∃ x₀ ∈ upperBoundsIn A u, ∀ m ∈ minimalUpperBounds A u, ¬ m ≤ x₀ := by
    by_contra hc
    push Not at hc
    exact h hc
  obtain ⟨x₀, hx₀, hno⟩ := h'
  have key : ∀ y, y ∈ upperBoundsIn A u → y ≤ x₀ → ∃ z, z ∈ upperBoundsIn A u ∧ z < y := by
    intro y hy hyx
    by_contra hc
    push Not at hc
    refine hno y ⟨hy, fun z hz hzy => ?_⟩ hyx
    rcases eq_or_lt_of_le hzy with rfl | hlt
    · exact le_rfl
    · exact absurd hlt (hc z hz)
  choose! d hd hdlt using key
  have hstep : ∀ n : ℕ, d^[n] x₀ ∈ upperBoundsIn A u ∧ d^[n] x₀ ≤ x₀ := by
    intro n
    induction n with
    | zero => exact ⟨hx₀, le_rfl⟩
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact ⟨hd _ ih.1 ih.2, (hdlt _ ih.1 ih.2).le.trans ih.2⟩
  refine ⟨fun n => d^[n] x₀, fun n => (hstep n).1, strictAnti_nat_of_succ_lt fun n => ?_⟩
  rw [Function.iterate_succ_apply']
  exact hdlt _ (hstep n).1 (hstep n).2

end FiniteImage

/-! ## Finite projections make a domain bifinite

What the reduction of Figures 3(a) and 3(b) is worth once the finiteness it asks
for is available: it is not merely *necessary* for bifiniteness but sufficient.
The hypothesis Smyth's argument has to produce is exactly the one below. -/

section FiniteProjection

variable [CompletePartialOrder α] {p : ScottHom α α}

/-- **Every element of the range of a finite projection is compact.** The image of
a directed set under `p` is a directed subset of the finite range, so it has a
greatest element `p z`; then `p (⨆M) = p z ⊑ z`, and a member of the range is
fixed by `p`, so it is already below that single `z ∈ M`.

Finiteness of the range is what replaces the usual algebraicity argument, and
`exists_mem_upperBounds_of_directedOn` is what turns "finite and directed" into
"has a greatest element". -/
theorem isCompactElement_of_mem_range (hp : ScottHom.IsProjection p)
    (hfin : (Set.range ⇑p).Finite) {y : α} (hy : y ∈ Set.range ⇑p) : IsCompactElement y := by
  intro s w hne hs hlub hyw
  have himg : (⇑p '' s).Finite :=
    hfin.subset (by rintro _ ⟨z, _, rfl⟩; exact Set.mem_range_self z)
  obtain ⟨c, hc, hcmax⟩ :=
    exists_mem_upperBounds_of_directedOn (ScottHom.directedOn_image p hs) (hne.image _) himg
      fun b hb => ⟨b, hb, le_rfl⟩
  obtain ⟨z, hz, rfl⟩ := hc
  have hpw : p w = p z :=
    (p.scottContinuous hne hs hlub).unique ⟨hcmax, fun b hb => hb ⟨z, hz, rfl⟩⟩
  refine ⟨z, hz, ?_⟩
  calc y = p y := (hp.apply_of_mem_range hy).symm
    _ ≤ p w := p.monotone hyw
    _ = p z := hpw
    _ ≤ z := hp.le z

theorem range_subset_compacts (hp : ScottHom.IsProjection p)
    (hfin : (Set.range ⇑p).Finite) : Set.range ⇑p ⊆ compacts α :=
  fun _ hy => isCompactElement_of_mem_range hp hfin hy

/-- **A domain with enough finite projections is bifinite.** If every finite set
of compact elements lies in the range of a projection with finite range, then
`K(D)` is a Plotkin order.

The witness is the range itself. It is finite by hypothesis, it consists of
compacts by `range_subset_compacts`, and `isNormalIn_of_isMubClosed` reduces
normality to the two conditions the previous section supplies: it is closed under
minimal upper bounds by `minimalUpperBounds_subset_image`, and each of its finite
subsets is mub-complete by `hasCompleteMub_of_finite_image`. A projection fixes
its own range, which is what feeds `k ⊑ p k` to both. -/
theorem isBifinite_of_exists_finite_projection
    (h : ∀ u : Set α, u.Finite → u ⊆ compacts α → ∃ p : ScottHom α α,
      ScottHom.IsProjection p ∧ (Set.range ⇑p).Finite ∧ u ⊆ Set.range ⇑p) :
    IsBifinite α := by
  intro u hu huc
  obtain ⟨p, hp, hfin, hup⟩ := h u hu huc
  have hNA : Set.range ⇑p ⊆ compacts α := range_subset_compacts hp hfin
  have hfix : ∀ v : Set α, v ⊆ Set.range ⇑p → ∀ k ∈ v, k ≤ p k :=
    fun _ hv _ hk => (hp.apply_of_mem_range (hv hk)).ge
  have himg : ∀ v : Set α, ⇑p '' upperBoundsIn (compacts α) v ⊆ Set.range ⇑p := by
    rintro v _ ⟨z, _, rfl⟩
    exact Set.mem_range_self z
  refine ⟨Set.range ⇑p, hfin, isNormalIn_of_isMubClosed hNA (fun v hv _ => ?_)
    (fun v hv _ => ?_), hup⟩
  · exact (minimalUpperBounds_subset_image p.monotone hp.le (hfix v hv)
      ((himg v).trans hNA)).trans (himg v)
  · exact hasCompleteMub_of_finite_image p.monotone hp.le (hfix v hv)
      (hfin.subset (himg v)) ((himg v).trans hNA)

end FiniteProjection

end ContinuousConstruction

end ScottDomains
