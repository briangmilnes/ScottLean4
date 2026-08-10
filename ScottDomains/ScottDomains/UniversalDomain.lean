import ScottDomains.Powerset
-- `IsClosure` and its API — see the note in `FinitaryProjectionPoset.lean`.
import ScottDomains.Closure
import ScottDomains.Skeleton.Lemma17

/-!
# §7: the universal domain — Theorem 22 and Lemma 23

Gunter & Scott, *Semantic Domains*, §7, quoted from the source PDF:

> **Definition:** Let `D` and `E` be cpo's. A continuous function `r : D → E` is a
> **closure** if there is a continuous function `s : E → D` such that
> `r ∘ s = id` and `s ∘ r ⊒ id`.

> **Theorem 22** For any (countably based) algebraic lattice `L`, there is a
> closure `r : P N → L`.

> **Definition:** Let us say that an operator `F` on cpo's is **representable**
> over a cpo `U` if and only if there is a continuous function `R_F` which
> completes the following diagram (up to isomorphism) … i.e.
> `im(R_F(r)) ≅ F(im(r))` for every closure `r`.

> **Lemma 23** The function space operator is representable over `P N`.

This is §7's entry point. §7 solves recursive domain equations *by
representability over a universal domain*, not by an inverse limit: Theorem 21
says that a representable `F` has a fixed point `D ≅ F(D)`, obtained as `im(r)`
for the `r ∈ Fc(U)` given by the Fixed Point Theorem applied to `R_F`. So every
later result of §7 — `D∞` included — runs through the two results proved here.

## Two different things are both called "closure"

`Skeleton/Section6.lean` defines `IsClosure r` for an **endomorphism**
`r : D → D`: `r ∘ r = r ⊒ id`. §7's closure is the **two-cpo** notion above, a
retraction `r : D → E` together with a section `s`, and it is the order dual of
`ScottHom.IsEmbeddingProjectionPair` (`Projection.lean`). `IsClosurePair r s`
below is that notion. The two are related — `s ∘ r : D → D` is an `IsClosure`
whose image is order-isomorphic to `E` — but the relation is not needed here and
would require a composition operation on `ScottHom`, which the development does
not have.

## Which lattice hypothesis Theorem 22 is stated with

The paper's "countably based algebraic lattice" is, in this development's
vocabulary, `[Domain L]` (algebraic with `K(L)` countable) together with
completeness of the lattice. Mathlib packages the same notion as
`CompleteLattice` + `IsCompactlyGenerated` + countability of the compacts, and
`theorem_22_of_isCompactlyGenerated` is that entry point, derived from
`isAlgebraic_of_isCompactlyGenerated`.

`theorem_22` itself is **not** stated over `CompleteLattice`, and the reason is
Lemma 23. Lemma 23 applies Theorem 22 at `L = P N → P N`, and
`ScottHom (Set ℕ) (Set ℕ)` already carries a `CompletePartialOrder` instance
(`ScottHom.lean`) whose `sSup` is a `dite`. Adding a `CompleteLattice` instance
there would create a second `CompletePartialOrder` instance on the same type —
the instance diamond `ScottHom.lean`'s docstring records as having broken an
`Iff.rfl` in r0004. So lattice completeness is carried as the *proposition*
`∀ t : Set L, IsLUB t (sSup t)` against the cpo's own `sSup`, which is exactly
`BoundedComplete.isLUB_sSup_of_bddAbove` with the boundedness hypothesis dropped,
and `isLUB_sSup_scottHom_set` proves it for the function space.

## What this file assumes from elsewhere

`compHom` — Gunter & Scott's `(q, p)(f) = q ∘ f ∘ p` and its continuity — is
reused from `Skeleton/Lemma17.lean` rather than restated, since it is exactly the
operator `R→` is built from. `IsClosure`, `IsClosure.rangeCompletePartialOrder`
and `Powerset.lean`'s `Domain (Set ℕ)` are the other imports that carry weight.
-/

namespace ScottDomains

/-! ### Closures between two cpo's -/

section ClosurePair

variable {α β : Type*} [Preorder α] [Preorder β]

/-- **`r` is a closure with section `s`** (Gunter & Scott, §7): `r ∘ s = id` and
`s ∘ r ⊒ id`, stated pointwise for the same reason
`ScottHom.IsEmbeddingProjectionPair` is — there is no composition operation on
`ScottHom`, and the order on `ScottHom` *is* pointwise. -/
def IsClosurePair (r : ScottHom α β) (s : ScottHom β α) : Prop :=
  (∀ y, r (s y) = y) ∧ ∀ x, x ≤ s (r x)

end ClosurePair

/-! ### Theorem 22

The paper's proof verbatim: `r(S) = ⨆{lₙ | n ∈ S}` and `s(l) = {n | lₙ ⊑ l}` for
an enumeration `l₀, l₁, l₂, …` of the basis. What the paper leaves "for the
reader" is the four facts below; each is one short argument, and each spends a
different hypothesis:

| # | Fact | Spends |
| -- | ---- | ------ |
| 1 | `r` is continuous | completeness of the lattice only |
| 2 | `s` is continuous | compactness of each `lₙ` |
| 3 | `r ∘ s = id` | algebraicity, and that `l` is *onto* `K(L)` |
| 4 | `s ∘ r ⊒ id` | nothing beyond `lₙ ⊑ ⨆{lₘ ∣ m ∈ S}` for `n ∈ S` |
-/

section Theorem22

variable {L : Type*} [CompletePartialOrder L] (l : ℕ → L)

/-- `r(S) = ⨆{lₙ | n ∈ S}`, the paper's closure `P N → L`. -/
def enumSup (S : Set ℕ) : L := sSup (l '' S)

/-- `s(x) = {n | lₙ ⊑ x}`, the paper's section `L → P N`. -/
def enumIndex (x : L) : Set ℕ := {n | l n ≤ x}

variable {l}

/-- `r` is monotone: a larger index set has a larger image, hence a larger
supremum. Needs the supremum of *every* set, which is where the lattice
hypothesis enters — `l '' S` is in general unbounded. -/
theorem monotone_enumSup (hsup : ∀ t : Set L, IsLUB t (sSup t)) : Monotone (enumSup l) :=
  fun _ _ hST => (hsup _).2 fun _ hy => (hsup _).1 (Set.image_mono hST hy)

/-- `r` is Scott continuous. In fact it preserves *all* suprema — it is a left
adjoint — and directedness of `d` is never used: the least-upper-bound half only
needs that a member of `⋃₀ d` lies in some `S ∈ d`. -/
theorem scottContinuous_enumSup (hsup : ∀ t : Set L, IsLUB t (sSup t)) :
    ScottContinuous (enumSup l) := by
  intro d _ _ a ha
  refine ⟨?_, ?_⟩
  · rintro _ ⟨S, hS, rfl⟩
    exact monotone_enumSup hsup (ha.1 hS)
  · intro u hu
    refine (hsup _).2 ?_
    rintro _ ⟨n, hn, rfl⟩
    have hsUnion : IsLUB d (⋃₀ d) := by
      rw [← Set.sSup_eq_sUnion]
      exact isLUB_sSup d
    rw [ha.unique hsUnion] at hn
    obtain ⟨S, hS, hnS⟩ := hn
    exact ((hsup (l '' S)).1 ⟨n, hnS, rfl⟩).trans (hu ⟨S, hS, rfl⟩)

/-- `s` is Scott continuous. This is where compactness of the basis elements is
spent: `lₙ ⊑ ⨆A` for a directed `A` puts `lₙ` below some member of `A` already,
which is exactly `n ∈ s(x)` for that member. -/
theorem scottContinuous_enumIndex (hc : ∀ n, IsCompactElement (l n)) :
    ScottContinuous (enumIndex l) := by
  intro d hne hd a ha
  refine ⟨?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact fun _ hn => hn.trans (ha.1 hx)
  · intro u hu n hn
    obtain ⟨x, hx, hnx⟩ := hc n d a hne hd ha hn
    exact hu ⟨x, hx, rfl⟩ hnx

/-- **Theorem 22.** For any countably based algebraic lattice `L` there is a
closure `r : P N → L`.

`P N` is `Set ℕ` (`Powerset.lean`), and "countably based algebraic" is `[Domain L]`:
`IsAlgebraic L` with `K(L)` countable. Lattice completeness is the hypothesis
`hsup`. The enumeration comes from `Set.Countable.exists_eq_range` applied to
`K(L)`, which is nonempty because `⊥` is compact — so the theorem needs no
nontriviality assumption on `L`. -/
theorem theorem_22 (L : Type*) [CompletePartialOrder L] [Domain L]
    (hsup : ∀ t : Set L, IsLUB t (sSup t)) :
    ∃ (r : ScottHom (Set ℕ) L) (s : ScottHom L (Set ℕ)), IsClosurePair r s := by
  obtain ⟨l, hl⟩ :=
    (Domain.countable_compacts (α := L)).exists_eq_range ⟨⊥, isCompactElement_bot⟩
  have hc : ∀ n, IsCompactElement (l n) := by
    intro n
    have : l n ∈ compacts L := by rw [hl]; exact Set.mem_range_self n
    exact this
  refine ⟨⟨enumSup l, scottContinuous_enumSup hsup⟩,
    ⟨enumIndex l, scottContinuous_enumIndex hc⟩, fun x => ?_, fun S n hn => ?_⟩
  · show sSup (l '' enumIndex l x) = x
    have himg : l '' enumIndex l x = compactsBelow x := by
      ext k
      constructor
      · rintro ⟨n, hn, rfl⟩
        exact ⟨hc n, hn⟩
      · rintro ⟨hk, hkx⟩
        have hkr : k ∈ Set.range l := by rw [← hl]; exact hk
        obtain ⟨n, rfl⟩ := hkr
        exact ⟨n, hkx, rfl⟩
    rw [himg]
    exact (hsup _).unique (IsAlgebraic.isLUB_compactsBelow x)
  · exact (hsup _).1 ⟨n, hn, rfl⟩

end Theorem22

/-! ### Mathlib's `IsCompactlyGenerated` as an entry point

`IsCompactlyGenerated` over a `CompleteLattice` *is* the paper's "algebraic
lattice": `exists_sSup_eq` says every element is a supremum of compact elements.
It gives `IsAlgebraic` — the directedness conjunct, which Mathlib's class does
not state, comes free in a lattice from `isCompactElement_of_isLUB_pair`. -/

section CompactlyGenerated

variable {L : Type*} [CompleteLattice L]

/-- Mathlib's `IsCompactlyGenerated` implies this development's `IsAlgebraic`.

The two conjuncts are recovered separately. Directedness: `k₁ ⊔ k₂` is compact by
`isCompactElement_of_isLUB_pair` against `isLUB_pair`, and is still below `x`.
Least upper bound: `x` bounds `compactsBelow x` outright, and `x = sSup s` for a
set `s` of compact elements with `s ⊆ compactsBelow x`, so any upper bound of
`compactsBelow x` already bounds `s`, hence `x`. -/
theorem isAlgebraic_of_isCompactlyGenerated [IsCompactlyGenerated L] : IsAlgebraic L where
  directedOn_compactsBelow x k₁ h₁ k₂ h₂ :=
    ⟨k₁ ⊔ k₂,
      ⟨isCompactElement_of_isLUB_pair h₁.1 h₂.1 (isLUB_pair (γ := L)), sup_le h₁.2 h₂.2⟩,
      le_sup_left, le_sup_right⟩
  isLUB_compactsBelow x := by
    obtain ⟨s, hsc, hsx⟩ := IsCompactlyGenerated.exists_sSup_eq x
    refine ⟨fun _ hk => hk.2, fun u hu => ?_⟩
    rw [← hsx]
    exact sSup_le fun k hk => hu ⟨hsc k hk, hsx ▸ le_sSup hk⟩

/-- **Theorem 22, stated with Mathlib's vocabulary for "countably based algebraic
lattice".** `isLUB_sSup` supplies the completeness hypothesis of `theorem_22` for
free, since in a `CompleteLattice` every subset has a least upper bound. -/
theorem theorem_22_of_isCompactlyGenerated (L : Type*) [CompleteLattice L]
    [IsCompactlyGenerated L] (hcount : (compacts L).Countable) :
    ∃ (r : ScottHom (Set ℕ) L) (s : ScottHom L (Set ℕ)), IsClosurePair r s := by
  haveI : Domain L :=
    { __ := isAlgebraic_of_isCompactlyGenerated
      countable_compacts := hcount }
  exact theorem_22 L fun t => isLUB_sSup t

end CompactlyGenerated

/-! ### The image of a closure, as a sub-cpo

`Skeleton/Section6.lean` builds the cpo structure on `im(r)` with
`sSup s = r (⨆ s)`, which lands in the range by construction and needs no
continuity of `r`. For the isomorphism of Lemma 23 more is needed: that `im(r)`
is *closed* under nonempty directed suprema of the ambient order, so that the
inclusion `im(r) ↪ D` is itself Scott continuous. That does spend continuity of
`r`, and it fails for the empty directed set — `r ⊥ = ⊥` is exactly what a
closure does not satisfy. -/

section ClosureRange

variable {U : Type*} [CompletePartialOrder U] {r : ScottHom U U}

-- `IsClosure.apply_sSup_of_directed` moved to `Skeleton/Section6.lean`, where
-- `IsClosure` is defined: `FinitaryProjectionPoset.lean` needs it too, and both
-- files defining it under one name clashed on any import of the pair.

/-- The inclusion `im(r) ↪ D` is Scott continuous: a least upper bound taken in
the subtype is already the ambient one, because the ambient supremum of a
nonempty directed subset of `im(r)` lies back in `im(r)`. -/
theorem IsClosure.scottContinuous_val (hr : IsClosure r) :
    ScottContinuous (Subtype.val : ↥(Set.range ⇑r) → U) := by
  intro D hne hD a ha
  have hD' : DirectedOn (· ≤ ·) (Subtype.val '' D) := ScottHom.directedOn_val_image hD
  have hne' : (Subtype.val '' D).Nonempty := hne.image _
  have hsub : Subtype.val '' D ⊆ Set.range ⇑r := by rintro _ ⟨x, _, rfl⟩; exact x.2
  refine ⟨fun _ hy => ?_, fun u hu => ?_⟩
  · obtain ⟨x, hx, rfl⟩ := hy
    exact ha.1 hx
  · have hmem : sSup (Subtype.val '' D) ∈ Set.range ⇑r :=
      Set.mem_range.mpr ⟨_, hr.apply_sSup_of_directed hne' hD' hsub⟩
    have hub : (⟨sSup (Subtype.val '' D), hmem⟩ : ↥(Set.range ⇑r)) ∈ upperBounds D :=
      fun x hx => hD'.le_sSup ⟨x, hx, rfl⟩
    exact le_trans (ha.2 hub) (hD'.sSup_le hu)

/-- The corestriction `x ↦ r x` of a closure onto its own image is Scott
continuous. Leastness is where the inflationary law is spent: an upper bound `b`
of `r '' D` inside `im(r)` already bounds `D`, since `x ⊑ r x ⊑ b`. -/
theorem IsClosure.scottContinuous_corestrict (hr : IsClosure r) :
    ScottContinuous (fun x : U => (⟨r x, Set.mem_range_self x⟩ : ↥(Set.range ⇑r))) := by
  intro D _ _ a ha
  refine ⟨?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact r.monotone (ha.1 hx)
  · rintro ⟨b, hb⟩ hub
    show r a ≤ b
    calc r a ≤ r b := r.monotone (ha.2 fun x hx => (hr.le_apply x).trans (hub ⟨x, hx, rfl⟩))
      _ = b := hr.apply_of_mem_range hb

end ClosureRange

/-! ### `Fc(U)`, and Gunter & Scott's *representable*

`Cpo` bundles a carrier with its structure so that "an operator on cpo's" is
literally a function `Cpo → Cpo` and `≅` is `OrderIso` between carriers. -/

universe u

/-- A cpo as a value: a carrier together with its structure. Gunter & Scott's
"operator on cpo's" is then a function `Cpo → Cpo`, and their `≅` is `≃o`
between the carriers. -/
structure Cpo : Type (u + 1) where
  /-- The underlying type. -/
  carrier : Type u
  /-- Its complete-partial-order structure. -/
  str : CompletePartialOrder carrier

attribute [instance] Cpo.str

/-- `Fc(U)`, the poset of finitary closures `r : U → U`, ordered pointwise.

The paper's definition has two conjuncts — `r ∘ r = r ⊒ id` *and* `im(r)` is a
domain — and immediately observes that over a domain the second is automatic:
"In the event that `D` is a domain, the requirement that `im(r)` be a domain is
unnecessary because we have the following: **Lemma 19**." `U` is `P N` at every
use here, which is a domain (`Powerset.lean`), so this subtype is `Fc(U)`.

Recorded precisely, because it is an appeal to a result the development has not
finished: `Skeleton/Section6.lean`'s `lemma_19` establishes only that `im(r)` carries
a `CompletePartialOrder`, not that it is algebraic with a countable basis. -/
def ClosurePoset (U : Type*) [CompletePartialOrder U] : Type _ :=
  {r : ScottHom U U // IsClosure r}

instance {U : Type*} [CompletePartialOrder U] : PartialOrder (ClosurePoset U) :=
  inferInstanceAs (PartialOrder {r : ScottHom U U // IsClosure r})

/-- `im(r)` as a cpo, using `IsClosure.rangeCompletePartialOrder`. -/
def ClosurePoset.image {U : Type u} [CompletePartialOrder U] (r : ClosurePoset U) : Cpo.{u} :=
  ⟨↥(Set.range ⇑r.val), r.2.rangeCompletePartialOrder⟩

/-- **Representable** (Gunter & Scott, §7):

> Let us say that an operator `F` on cpo's is representable over a cpo `U` if and
> only if there is a continuous function `R_F` which completes the following
> diagram (up to isomorphism) … i.e. `im(R_F(r)) ≅ F(im(r))` for every closure `r`.

The diagram is the square with `im : Fc(U) → Cpo's` down both sides, `F` across
the top and `R_F` across the bottom; "completes it up to isomorphism" is exactly
the displayed equation, which is what is formalized. `≅` is `≃o`: an order
isomorphism of cpos automatically preserves directed suprema, so no separate
continuity condition on the isomorphism is needed. -/
def IsRepresentable (U : Type u) [CompletePartialOrder U] (F : Cpo.{u} → Cpo.{u}) : Prop :=
  ∃ R : ClosurePoset U → ClosurePoset U, ScottContinuous R ∧
    ∀ r : ClosurePoset U, Nonempty ((R r).image.carrier ≃o (F r.image).carrier)

/-- **Representable**, binary case, which the paper states in full for the very
operator of Lemma 23:

> This idea extends to multiary operators as well. For example, the function
> space operator `· → ·` is representable over a cpo `U` if there is a continuous
> function `R : Fc(U) × Fc(U) → Fc(U)` such that, for any `r, s ∈ Fc(U)`,
> `im(R(r,s)) ≅ im(r) → im(s)`.

Continuity of `R` is with respect to the product order on `Fc(U) × Fc(U)`. -/
def IsRepresentable₂ (U : Type u) [CompletePartialOrder U]
    (F : Cpo.{u} → Cpo.{u} → Cpo.{u}) : Prop :=
  ∃ R : ClosurePoset U × ClosurePoset U → ClosurePoset U, ScottContinuous R ∧
    ∀ p : ClosurePoset U × ClosurePoset U,
      Nonempty ((R p).image.carrier ≃o (F p.1.image p.2.image).carrier)

/-- The function-space operator `· → ·` as an operator on cpos. -/
noncomputable def Cpo.funSpace (D E : Cpo.{u}) : Cpo.{u} :=
  ⟨ScottHom D.carrier E.carrier, inferInstance⟩

/-! ### Suprema in `Fc(U)`

Continuity of a map *out of* `Fc(U)` is stated against least upper bounds taken
in the subtype, and every computation available is about the ambient function
space. The two agree, because the closures are closed under nonempty directed
suprema. -/

section ClosureSup

variable {U : Type*} [CompletePartialOrder U]

-- `isClosure_sSup` moved to `Skeleton/Section6.lean` for the same reason;
-- `FinitaryProjectionPoset.lean` had proved the identical statement separately.

/-- A least upper bound taken in `Fc(U)` is already one in `U → U`. Both
inequalities go through `isClosure_sSup`: the ambient supremum is a closure, so
it is an upper bound *inside* `Fc(U)`, which the subtype bound must beat, and it
is beaten by any ambient upper bound. -/
theorem isLUB_val_image_of_isLUB {d : Set (ClosurePoset U)} (hne : d.Nonempty)
    (hd : DirectedOn (· ≤ ·) d) {a : ClosurePoset U} (ha : IsLUB d a) :
    IsLUB ((fun c : ClosurePoset U => c.val) '' d) a.val := by
  have hedir : DirectedOn (· ≤ ·) ((fun c : ClosurePoset U => c.val) '' d) := by
    rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩
    obtain ⟨c, hc, h₁, h₂⟩ := hd p hp q hq
    exact ⟨c.val, ⟨c, hc, rfl⟩, h₁, h₂⟩
  have hVcl : IsClosure (sSup ((fun c : ClosurePoset U => c.val) '' d)) :=
    isClosure_sSup (hne.image _) hedir (by rintro _ ⟨p, _, rfl⟩; exact p.2)
  have hub : (⟨_, hVcl⟩ : ClosurePoset U) ∈ upperBounds d :=
    fun c hc => hedir.le_sSup ⟨c, hc, rfl⟩
  have heq : a.val = sSup ((fun c : ClosurePoset U => c.val) '' d) :=
    le_antisymm (ha.2 hub) (hedir.sSup_le (by rintro _ ⟨c, hc, rfl⟩; exact ha.1 hc))
  rw [heq]
  exact hedir.isLUB_sSup

end ClosureSup

/-! ### `P N → P N` is a complete lattice

Theorem 22 is applied at `L = P N → P N`, so its `hsup` hypothesis has to be
discharged there: the pointwise supremum of an *arbitrary* set of continuous maps
into a powerset is continuous, because in `P X` the least upper bound of every
set is its union and unions commute with one another. This is
`ScottHom.scottContinuous_pointwiseSup_of_forall_isLUB` — written in
`ScottHom.lean` precisely so that the directed case and the bounded case share
one script — instantiated with `isLUB_sSup`, which needs neither. -/

section PowersetCodomain

variable {α : Type*} [Preorder α] {X : Type*}

/-- The pointwise supremum of any set of continuous maps into `P X` is
continuous. -/
theorem scottContinuous_pointwiseSup_set (t : Set (ScottHom α (Set X))) :
    ScottContinuous fun x => sSup ((fun f : ScottHom α (Set X) => f x) '' t) :=
  ScottHom.scottContinuous_pointwiseSup_of_forall_isLUB fun _ => isLUB_sSup _

/-- `α → P X` is a complete lattice: `sSup` is the least upper bound of *every*
set of continuous functions, not only the directed and the bounded ones. This is
the `hsup` hypothesis of `theorem_22`. -/
theorem isLUB_sSup_scottHom_set (t : Set (ScottHom α (Set X))) : IsLUB t (sSup t) := by
  constructor
  · intro f hf x
    dsimp only
    rw [ScottHom.coe_sSup_of_continuous (scottContinuous_pointwiseSup_set t)]
    exact (isLUB_sSup ((fun g : ScottHom α (Set X) => g x) '' t)).1 ⟨f, hf, rfl⟩
  · intro g hg x
    dsimp only
    rw [ScottHom.coe_sSup_of_continuous (scottContinuous_pointwiseSup_set t)]
    refine (isLUB_sSup ((fun f : ScottHom α (Set X) => f x) '' t)).2 ?_
    rintro _ ⟨f, hf, rfl⟩
    exact hg hf x

end PowersetCodomain

/-! ### `(s, r)` is a closure on the function space -/

section CompHomClosure

variable {U : Type*} [CompletePartialOrder U] {r s : ScottHom U U}

/-- Gunter & Scott's `(s, r)(f) = s ∘ f ∘ r` is a closure on `D → D` whenever `r`
and `s` are closures on `D` — the closure analogue of
`Skeleton/Lemma17.lean`'s `isProjection_compHom`. Idempotence is the two
idempotences composed; inflation is `f x ⊑ f (r x) ⊑ s (f (r x))`. -/
theorem isClosure_compHom (hr : IsClosure r) (hs : IsClosure s) :
    IsClosure (compHom r s) := by
  refine ⟨fun f => ?_, fun f x => ?_⟩
  · ext x
    show s (s (f (r (r x)))) = s (f (r x))
    rw [hr.idem, hs.idem]
  · exact (f.monotone (hr.le_apply x)).trans (hs.le_apply (f (r x)))

/-- `(s, r)` is monotone in `(r, s)`: `s (f (r x)) ⊑ s' (f (r x)) ⊑ s' (f (r' x))`,
the first step by the pointwise order on `s ⊑ s'` and the second by monotonicity
of `s'` and `f`. -/
theorem compHom_mono {r r' s s' : ScottHom U U} (hr : r ≤ r') (hs : s ≤ s')
    (f : ScottHom U U) : compHom r s f ≤ compHom r' s' f :=
  fun x => (hs (f (r x))).trans (s'.monotone (f.monotone (hr x)))

end CompHomClosure

/-! ### The representing map `R→`

Gunter & Scott's construction, with `→⁻ = fn : U → (U → U)` and
`→⁺ = gr : (U → U) → U` the closure pair Theorem 22 supplies:

> `R→(r, s) = →⁺ ∘ (s, r) ∘ →⁻`

and their computation that it is a finitary closure. -/

section Representation

variable {U : Type*} [CompletePartialOrder U]

section Defs

variable (fn : ScottHom U (ScottHom U U)) (gr : ScottHom (ScottHom U U) U)

/-- `R→(r, s) = →⁺ ∘ (s, r) ∘ →⁻`, continuous as a composite of three continuous
maps. -/
noncomputable def repFun (r s : ScottHom U U) : ScottHom U U :=
  ⟨⇑gr ∘ ⇑(compHom r s) ∘ ⇑fn,
    ScottContinuous.comp
      (ScottContinuous.comp fn.scottContinuous (compHom r s).scottContinuous)
      gr.scottContinuous⟩

end Defs

variable {fn : ScottHom U (ScottHom U U)} {gr : ScottHom (ScottHom U U) U}

/-- `R→(r, s)` is a closure, which is Gunter & Scott's displayed computation:

> `(R→(r,s) ∘ R→(r,s))(x) = →⁺((s,r)(→⁻(→⁺((s,r)(→⁻(x)))))) = … = R→(r,s)(x)`
> and `R→(r,s)(x) = →⁺(s ∘ →⁻(x) ∘ r) ⊒ →⁺(→⁻(x)) ⊒ x`.

Six equalities collapse to two rewrites here: `→⁻ ∘ →⁺ = id` deletes the inner
pair, and `isClosure_compHom` is the idempotence of `(s, r)` that the paper spells
out as `(s ∘ s) ∘ →⁻(x) ∘ (r ∘ r) = s ∘ →⁻(x) ∘ r`. -/
theorem isClosure_repFun (hfg : ∀ y, fn (gr y) = y) (hgf : ∀ x, x ≤ gr (fn x))
    {r s : ScottHom U U} (hr : IsClosure r) (hs : IsClosure s) :
    IsClosure (repFun fn gr r s) := by
  have hC := isClosure_compHom hr hs
  refine ⟨fun x => ?_, fun x => ?_⟩
  · show gr (compHom r s (fn (gr (compHom r s (fn x))))) = gr (compHom r s (fn x))
    rw [hfg, hC.idem]
  · exact (hgf x).trans (gr.monotone (hC.le_apply (fn x)))

/-- The exchange step behind continuity of `R→`: `(s, r)` applied to a fixed `f`
carries a least upper bound in `Fc(U) × Fc(U)` to one in `U → U`.

The least-upper-bound half is the only content. At a point `y` it unwinds three
suprema — `a₁ y = ⨆ r y`, then `f`'s continuity, then `a₂`'s — leaving
`s (f (r y)) ⊑ v y` to be shown for an *arbitrary* pair `(r, s)` drawn from the
two projections separately. Directedness of `d` is what puts them back on the
diagonal: some `c ∈ d` dominates both, and `s (f (r y)) ⊑ c₂ (f (c₁ y)) ⊑ v y`. -/
theorem isLUB_compHom_of_isLUB {d : Set (ClosurePoset U × ClosurePoset U)}
    (hne : d.Nonempty) (hd : DirectedOn (· ≤ ·) d) {a₁ a₂ : ScottHom U U}
    (h₁ : IsLUB ((fun p : ClosurePoset U × ClosurePoset U => p.1.val) '' d) a₁)
    (h₂ : IsLUB ((fun p : ClosurePoset U × ClosurePoset U => p.2.val) '' d) a₂)
    (f : ScottHom U U) :
    IsLUB ((fun p : ClosurePoset U × ClosurePoset U => compHom p.1.val p.2.val f) '' d)
      (compHom a₁ a₂ f) := by
  have hd₁ : DirectedOn (· ≤ ·) ((fun p : ClosurePoset U × ClosurePoset U => p.1.val) '' d) := by
    rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩
    obtain ⟨c, hc, hpc, hqc⟩ := hd p hp q hq
    exact ⟨c.1.val, ⟨c, hc, rfl⟩, hpc.1, hqc.1⟩
  have hd₂ : DirectedOn (· ≤ ·) ((fun p : ClosurePoset U × ClosurePoset U => p.2.val) '' d) := by
    rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩
    obtain ⟨c, hc, hpc, hqc⟩ := hd p hp q hq
    exact ⟨c.2.val, ⟨c, hc, rfl⟩, hpc.2, hqc.2⟩
  refine ⟨?_, ?_⟩
  · rintro _ ⟨p, hp, rfl⟩
    exact compHom_mono (h₁.1 ⟨p, hp, rfl⟩) (h₂.1 ⟨p, hp, rfl⟩) f
  · intro v hv y
    have hAdir := ScottHom.directedOn_eval_image hd₁ y
    have hAne : ((fun g : ScottHom U U => g y) ''
        ((fun p : ClosurePoset U × ClosurePoset U => p.1.val) '' d)).Nonempty :=
      (hne.image _).image _
    have hA := ScottHom.isLUB_eval_image_of_isLUB hd₁ h₁ y
    have hfA := f.scottContinuous hAne hAdir hA
    have hfAdir := ScottHom.directedOn_image f hAdir
    have h2 := a₂.scottContinuous (hAne.image _) hfAdir hfA
    refine h2.2 ?_
    rintro _ ⟨_, ⟨_, ⟨_, ⟨p, hp, rfl⟩, rfl⟩, rfl⟩, rfl⟩
    refine (ScottHom.isLUB_eval_image_of_isLUB hd₂ h₂ (f (p.1.val y))).2 ?_
    rintro _ ⟨_, ⟨q, hq, rfl⟩, rfl⟩
    obtain ⟨c, hc, hpc, hqc⟩ := hd p hp q hq
    exact (compHom_mono hpc.1 hqc.2 f y).trans (hv ⟨c, hc, rfl⟩ y)

/-- **`R→ : Fc(U) × Fc(U) → Fc(U)` is continuous.** The upper-bound half is
monotonicity of `(s, r)` followed by monotonicity of `→⁺`. The least half feeds
`isLUB_compHom_of_isLUB` at the argument `→⁻(x)` into the continuity of `→⁺`,
which is legitimate because the least upper bound taken in `Fc(U)` is already the
one taken in `U → U` (`isLUB_val_image_of_isLUB`). -/
theorem scottContinuous_repClosure (hfg : ∀ y, fn (gr y) = y) (hgf : ∀ x, x ≤ gr (fn x)) :
    ScottContinuous (fun p : ClosurePoset U × ClosurePoset U =>
      (⟨repFun fn gr p.1.val p.2.val, isClosure_repFun hfg hgf p.1.2 p.2.2⟩ :
        ClosurePoset U)) := by
  intro d hne hd a ha
  have hdfst : DirectedOn (· ≤ ·) (Prod.fst '' d) := by
    rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩
    obtain ⟨c, hc, hpc, hqc⟩ := hd p hp q hq
    exact ⟨c.1, ⟨c, hc, rfl⟩, hpc.1, hqc.1⟩
  have hdsnd : DirectedOn (· ≤ ·) (Prod.snd '' d) := by
    rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩
    obtain ⟨c, hc, hpc, hqc⟩ := hd p hp q hq
    exact ⟨c.2, ⟨c, hc, rfl⟩, hpc.2, hqc.2⟩
  have h₁ : IsLUB ((fun p : ClosurePoset U × ClosurePoset U => p.1.val) '' d) a.1.val := by
    have := isLUB_val_image_of_isLUB (hne.image _) hdfst (isLUB_prod.mp ha).1
    rwa [Set.image_image] at this
  have h₂ : IsLUB ((fun p : ClosurePoset U × ClosurePoset U => p.2.val) '' d) a.2.val := by
    have := isLUB_val_image_of_isLUB (hne.image _) hdsnd (isLUB_prod.mp ha).2
    rwa [Set.image_image] at this
  refine ⟨?_, ?_⟩
  · rintro _ ⟨p, hp, rfl⟩ x
    exact gr.monotone (compHom_mono (h₁.1 ⟨p, hp, rfl⟩) (h₂.1 ⟨p, hp, rfl⟩) (fn x) )
  · intro u hu x
    have hE : IsLUB ((fun p : ClosurePoset U × ClosurePoset U =>
        compHom p.1.val p.2.val (fn x)) '' d) (compHom a.1.val a.2.val (fn x)) :=
      isLUB_compHom_of_isLUB hne hd h₁ h₂ (fn x)
    have hEdir : DirectedOn (· ≤ ·) ((fun p : ClosurePoset U × ClosurePoset U =>
        compHom p.1.val p.2.val (fn x)) '' d) := by
      rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩
      obtain ⟨c, hc, hpc, hqc⟩ := hd p hp q hq
      exact ⟨_, ⟨c, hc, rfl⟩, compHom_mono hpc.1 hpc.2 _, compHom_mono hqc.1 hqc.2 _⟩
    refine (gr.scottContinuous (hne.image _) hEdir hE).2 ?_
    rintro _ ⟨_, ⟨p, hp, rfl⟩, rfl⟩
    exact hu ⟨p, hp, rfl⟩ x

/-! #### `im(R→(r,s)) ≅ im((s, r))`

> We claim that `→⁺` cuts down to an isomorphism between such functions and the
> sets in the image of `R→(r,s)`. Since `→⁻ ∘ →⁺ = id`, we need only show that
> `(→⁺ ∘ →⁻)(x) = x` for each `x = R→(r,s)(x)`.
-/

section RangeEquiv

variable {r s : ScottHom U U}

/-- `→⁻` carries `im(R→(r,s))` into `im((s, r))`. -/
theorem fn_mem_range_compHom (hfg : ∀ y, fn (gr y) = y) {x : U}
    (hx : x ∈ Set.range ⇑(repFun fn gr r s)) : fn x ∈ Set.range ⇑(compHom r s) := by
  obtain ⟨y, rfl⟩ := hx
  refine Set.mem_range.mpr ⟨fn y, ?_⟩
  show compHom r s (fn y) = fn (gr (compHom r s (fn y)))
  rw [hfg]

/-- `→⁺` carries `im((s, r))` into `im(R→(r,s))`. -/
theorem gr_mem_range_repFun (hfg : ∀ y, fn (gr y) = y) {F : ScottHom U U}
    (hF : F ∈ Set.range ⇑(compHom r s)) : gr F ∈ Set.range ⇑(repFun fn gr r s) := by
  obtain ⟨G, rfl⟩ := hF
  refine Set.mem_range.mpr ⟨gr G, ?_⟩
  show gr (compHom r s (fn (gr G))) = gr (compHom r s G)
  rw [hfg]

/-- The paper's "we need only show that `(→⁺ ∘ →⁻)(x) = x` for each
`x = R→(r,s)(x)`". -/
theorem gr_fn_of_mem_range (hfg : ∀ y, fn (gr y) = y) {x : U}
    (hx : x ∈ Set.range ⇑(repFun fn gr r s)) : gr (fn x) = x := by
  obtain ⟨y, rfl⟩ := hx
  show gr (fn (gr (compHom r s (fn y)))) = gr (compHom r s (fn y))
  rw [hfg]

/-- `im(R→(r,s)) ≅ im((s, r))`, by `→⁻` and `→⁺` restricted. -/
noncomputable def repRangeOrderIso (hfg : ∀ y, fn (gr y) = y) (r s : ScottHom U U) :
    ↥(Set.range ⇑(repFun fn gr r s)) ≃o ↥(Set.range ⇑(compHom r s)) :=
  Equiv.toOrderIso
    { toFun := fun x => ⟨fn x.val, fn_mem_range_compHom hfg x.2⟩
      invFun := fun F => ⟨gr F.val, gr_mem_range_repFun hfg F.2⟩
      left_inv := fun x => Subtype.ext (gr_fn_of_mem_range hfg x.2)
      right_inv := fun F => Subtype.ext (hfg F.val) }
    (fun _ _ h => fn.monotone h) (fun _ _ h => gr.monotone h)

end RangeEquiv

/-! #### `im((s, r)) ≅ (im(r) → im(s))`

> Now, there is an evident isomorphism between continuous functions
> `f : im(r) → im(s)` and continuous functions `g : P N → P N` such that
> `g = s ∘ g ∘ r`.

`im((s,r))` *is* the set of such `g`, because `(s, r)` is idempotent. The
isomorphism restricts `g` to `im(r)` and corestricts it to `im(s)`; the inverse
composes with the inclusion `im(r) ↪ D` and the corestriction `x ↦ r x`, both
Scott continuous by `IsClosure.scottContinuous_val` and
`IsClosure.scottContinuous_corestrict`. -/

section EvidentEquiv

variable {r s : ScottHom U U}

/-- `G ↦ G` restricted to `im(r)` and corestricted to `im(s)`. -/
noncomputable def restrictHom (hr : IsClosure r) (hs : IsClosure s) (G : ScottHom U U) :
    ScottHom ↥(Set.range ⇑r) ↥(Set.range ⇑s) :=
  ⟨fun x => ⟨s (G x.val), Set.mem_range_self _⟩,
    ScottContinuous.comp (ScottContinuous.comp hr.scottContinuous_val G.scottContinuous)
      hs.scottContinuous_corestrict⟩

/-- `F ↦ ι ∘ F ∘ (x ↦ r x)`, the inverse direction. -/
noncomputable def extendHom (hr : IsClosure r) (hs : IsClosure s)
    (F : ScottHom ↥(Set.range ⇑r) ↥(Set.range ⇑s)) : ScottHom U U :=
  ⟨fun x => (F ⟨r x, Set.mem_range_self x⟩).val,
    ScottContinuous.comp (ScottContinuous.comp hr.scottContinuous_corestrict F.scottContinuous)
      hs.scottContinuous_val⟩

/-- `ι ∘ F ∘ (x ↦ r x)` is fixed by `(s, r)`, hence lies in `im((s, r))`:
`s (F (r (r x))) = s (F (r x)) = F (r x)`, the first equation by idempotence of
`r` and the second because `F` already takes values in `im(s)`. -/
theorem extendHom_mem_range (hr : IsClosure r) (hs : IsClosure s)
    (F : ScottHom ↥(Set.range ⇑r) ↥(Set.range ⇑s)) :
    extendHom hr hs F ∈ Set.range ⇑(compHom r s) := by
  refine Set.mem_range.mpr ⟨extendHom hr hs F, ScottHom.ext fun x => ?_⟩
  show s ((F ⟨r (r x), _⟩).val) = (F ⟨r x, _⟩).val
  have hidem : (⟨r (r x), Set.mem_range_self (r x)⟩ : ↥(Set.range ⇑r)) =
      ⟨r x, Set.mem_range_self x⟩ := Subtype.ext (hr.idem x)
  rw [hidem]
  exact hs.apply_of_mem_range (F ⟨r x, Set.mem_range_self x⟩).2

/-- `im((s, r)) ≅ im(r) → im(s)`, the paper's "evident isomorphism". -/
noncomputable def evidentOrderIso (hr : IsClosure r) (hs : IsClosure s) :
    ↥(Set.range ⇑(compHom r s)) ≃o ScottHom ↥(Set.range ⇑r) ↥(Set.range ⇑s) :=
  Equiv.toOrderIso
    { toFun := fun G => restrictHom hr hs G.val
      invFun := fun F => ⟨extendHom hr hs F, extendHom_mem_range hr hs F⟩
      left_inv := fun G => by
        refine Subtype.ext (ScottHom.ext fun x => ?_)
        show s (G.val (r x)) = G.val x
        exact DFunLike.congr_fun ((isClosure_compHom hr hs).apply_of_mem_range G.2) x
      right_inv := fun F => by
        refine ScottHom.ext fun x => Subtype.ext ?_
        show s ((F ⟨r x.val, Set.mem_range_self x.val⟩).val) = (F x).val
        have hx : (⟨r x.val, Set.mem_range_self x.val⟩ : ↥(Set.range ⇑r)) = x :=
          Subtype.ext (hr.apply_of_mem_range x.2)
        rw [hx]
        exact hs.apply_of_mem_range (F x).2 }
    (fun _ _ h x => s.monotone (h x.val)) (fun _ _ h x => h _)

end EvidentEquiv

end Representation

/-! ### Lemma 23 -/

/-- **Lemma 23.** The function space operator is representable over `P N`.

The representing map is Gunter & Scott's `R→(r,s) = →⁺ ∘ (s, r) ∘ →⁻`, with
`→⁻, →⁺` the closure pair that **Theorem 22** supplies at
`L = P N → P N` — an algebraic lattice because `Powerset.lean` makes `P N` a
bounded complete domain, `FunctionSpaceCountable.lean` makes the function space
one too (Theorem 7), and `isLUB_sSup_scottHom_set` supplies the completeness of
the lattice.

The three obligations of `IsRepresentable₂` are discharged by
`isClosure_repFun` (`R→(r,s) ∈ Fc(P N)`), `scottContinuous_repClosure`
(continuity of `R→`), and the composite
`repRangeOrderIso ≫ evidentOrderIso` (the isomorphism
`im(R→(r,s)) ≅ im(r) → im(s)`), which is the paper's proof in its two stated
steps. -/
theorem lemma_23 : IsRepresentable₂ (Set ℕ) Cpo.funSpace := by
  obtain ⟨fn, gr, hfg, hgf⟩ := theorem_22 (ScottHom (Set ℕ) (Set ℕ)) isLUB_sSup_scottHom_set
  refine ⟨fun p => ⟨repFun fn gr p.1.val p.2.val, isClosure_repFun hfg hgf p.1.2 p.2.2⟩,
    scottContinuous_repClosure hfg hgf, fun p => ⟨?_⟩⟩
  exact (repRangeOrderIso hfg p.1.val p.2.val).trans (evidentOrderIso p.1.2 p.2.2)

end ScottDomains
