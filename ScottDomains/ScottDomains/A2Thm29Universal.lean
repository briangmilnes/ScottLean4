import ScottDomains.LemThirty
-- `Set.Finite.exists_maximal`, the maximal point of `B ∖ A` that Proposition 21
-- adjoins; not reachable from the ScottDomains imports above.
import Mathlib.Order.Preorder.Finite
-- `Set.ncard`, which measures how many points of `β` are still to be realized in
-- the induction of `hasFiniteExtensions_of_hasNormalRealizations`.
import Mathlib.Data.Set.Card

/-!
# `Thm29Normal`: the missing input, named and located

`LemThirty.Thm29Normal` is the statement that `A∞` is universal among the bases
of bifinite domains under normal embedding, and `LemThirty.lean` already proves
that it yields Theorem 29's second sentence
(`thm29SecondAtDomains_of_thm29Normal`). What it does not do is say *what*
would yield `Thm29Normal`. `LemThirty.lean:426` locates the gap —

> Producing `Nᵢ₊₁ → Stg nᵢ₊₁` from `Nᵢ → Stg nᵢ` is the step §7.4 defers in full
> to [Gun87], and it is exactly the universal property of `M` among finite posets
> and normal embeddings.

— and `BifiniteUniversal.lean:38–45` records [Gun87] as
`C. A. Gunter. Sets and the semantics of bounded nondeterminism. Manuscript,
1987` — unpublished and not obtainable.

## The correction: the argument is not lost, and it is in `papers/`

`BifiniteUniversal.lean:47` says "The construction itself is *not* lost with the
manuscript", citing p. 23 of Gunter, *Universal Profinite Domains*, Information
and Computation **72** (1987) 1–30, `papers/Gunter 1987 Universal Profinite
Domains.pdf`. That is right but understates the case by a wide margin. **§5 of
that paper carries the whole universality argument, with proofs**, not merely the
construction:

| # | result | page | content |
| - | ------ | ---: | ------- |
| 1 | Proposition 21 | 18 | `A ◁ B` finite, `A ≠ B` ⟹ the inclusion factors through singleton steps |
| 2 | Theorem 22 (Enumeration) | 19 | a countable Plotkin poset `A` has an enumeration `X₀, X₁, …` with `rt(A) ∪ {Xᵢ ∣ i < n} ◁ A` |
| 3 | Lemma 23 | 19 | a normal type over `B ◁ A` is realized by one new point of a finite `A₁ ▷ A` |
| 4 | Lemma 24 | 20 | **for finite `A` there is a finite `A⁺ ▷ A` realizing every normal type over every `B ◁ A`, normally** |
| 5 | Theorem 25 | 21 | a countable Plotkin poset `V` with property 4 is universal: `rt(B) ≅ rt(V)` ⟹ `B ⊴ V` |
| 6 | Corollary 26 | 21 | `V_A = ⋃ₙ Aₙ` with `Aₙ₊₁ = Aₙ⁺` has property 4 |
| 7 | remark | 23 | "an even more explicit way … remarked to the author by Dana Scott": `A⁺` **is** `M(A)` |

Row 7 is the sentence `BifiniteUniversal.lean` already quotes. Read with rows
4–6, it says that `M(A)` is Gunter's `A⁺` — so the property row 4 asserts of
`A⁺` is exactly "the universal property of `M` among finite posets under normal
embedding" that `LemThirty.lean:426` names as missing, and row 5 is exactly the
implication from it to `Thm29Normal`.

So the input is *not* an unobtainable manuscript. It is a published proof this
repository holds. What is missing is a formalization, not a source.

## What this file does

1. `HasNormalRealizations` states row 5's hypothesis — the universal property —
   precisely, in Lean, over an arbitrary poset. It is the missing input, named.
2. `HasFiniteExtensions` states the same property with a whole finite normal
   extension realized at once, and `hasFiniteExtensions_of_hasNormalRealizations`
   derives it from `HasNormalRealizations` by Proposition 21. This is the form
   the reduction consumes.
3. `thm29Normal_of_hasFiniteExtensions` and
   `thm29Normal_of_hasNormalRealizations` prove **row 5's implication**:
   `HasNormalRealizations Ainf → LemThirty.Thm29Normal`. `Thm29Normal` is used
   exactly as `LemThirty.lean` states it — no added binder, no weakening.
4. `isRoot_singleton_bot` discharges row 5's other hypothesis, `rt(B) ≅ rt(V)`,
   in this setting: both roots are `{⊥}` because both posets have a least
   element, so the root condition costs nothing here and the realization
   property is the *only* remaining input.

Composing 3 with `LemThirty.thm29SecondAtDomains_of_thm29Normal` reduces
`Thm29SecondAtDomains`, `Lemma30AtV`'s retraction conjuncts and `Lem30Arrow` to
one statement about `A∞` alone.

## Gunter's diagram types, without the syntax

Gunter (p. 19) defines a *diagram type* over a poset `A` as a set of formulas
`v ⪯ X`, `v ⋠ X`, `X ⪯ v`, `X ⋠ v` for `X ∈ A`, and calls it **normal** when
there is a poset `B` with `A ◁ B` in which it is realized.

Formalizing that syntax is unnecessary. Every type this development has to
realize is a *complete* type — the full diagram type of an actual point `z` of an
actual extension — and a complete type is determined by the two relations it
records. So `HasNormalRealizations` quantifies over the witness `(β, g, z)`
directly: `β` is Gunter's `B`, `g` is the normal embedding `A ◁ β`, and `z` is
the point realizing the type. `SameTypeOver` says the new point of `α` stands in
the same relation to `A` that `z` stands in to `g '' A`, which is precisely
"realizes the diagram type of `z` over `A`". Quantifying over the witness rather
than over syntax also *weakens* the property — a syntactic type need not be
complete — so the input named here is no stronger than Gunter's Lemma 24.
-/

namespace ScottDomains.R46.Agent2

open ScottDomains

/-! ## Roots

Gunter's Proposition 19 (p. 16): the normal substructures of a poset `A` form a
dcpo, with a least element `rt(A) = ⋂ {B ∣ B ◁ A}` when `A` has property m.
Theorem 25's second hypothesis is `rt(B) ≅ rt(V)`, and Gunter observes (p. 18)
that this is a genuine obstruction — "no profinite domain can be a continuous
projection of a profinite domain that has a different root", which is why there
is no projection-universal ω-profinite domain at all.

In *this* setting the obstruction is vacuous, and that is worth recording: every
poset in sight has a least element, so every root is `{⊥}`. Both facts are
already in `NormalSubposet.lean`; only the packaging is new. -/

section Root

variable {α : Type*} [PartialOrder α] [OrderBot α] {A : Set α}

/-- **The root of `A`** (Gunter 1987, Proposition 19): the `◁`-least normal
substructure. Stated as a predicate rather than an intersection because
`NormalSubposet.lean` proves the two halves directly. -/
def IsRoot (R S : Set α) : Prop := R ◁ S ∧ ∀ N : Set α, N ◁ S → R ◁ N

/-- **Every root here is a single point.** `{⊥}` is normal in any `A` containing
`⊥` (`singleton_bot_isNormalIn`) and `◁`-below every normal substructure of such
an `A` (`singleton_bot_isNormalIn_of_isNormalIn`).

This discharges Theorem 25's hypothesis `rt(B) ≅ rt(V)` for every pair of posets
with least elements — in particular for `K(E)` and `A∞` — so the realization
property is the theorem's *only* substantive hypothesis in this development. -/
theorem isRoot_singleton_bot (hbot : (⊥ : α) ∈ A) : IsRoot ({⊥} : Set α) A :=
  ⟨singleton_bot_isNormalIn hbot,
    fun _ hN => singleton_bot_isNormalIn_of_isNormalIn hbot hN⟩

omit [OrderBot α] in
/-- A root is unique, so "the" root is justified and `rt(B) ≅ rt(V)` may be
checked by exhibiting one-point roots on both sides. -/
theorem IsRoot.unique {R R' : Set α} (h : IsRoot R A) (h' : IsRoot R' A) : R = R' :=
  IsNormalIn.antisymm (h.2 R' h'.1) (h'.2 R h.1)

end Root

/-! ## Proposition 21: a normal inclusion of finite posets factors through
singleton steps

> **Proposition 21** If `A` and `B` are finite posets such that `A ◁ B` but
> `A ≠ B`, then there are posets `A₀, …, Aₙ` such that
> `A = A₀ ◁ A₁ ◁ ⋯ ◁ Aₙ₋₁ ◁ Aₙ = B` and, for each `k < n`, `Aₖ₊₁ − Aₖ` is a
> singleton.

Only the one-step form is needed, and it is what is proved here: a *maximal*
point `X` of `B ∖ A` may be adjoined to `A` keeping normality on both sides.
Gunter's induction on `|B − A|` is then the induction inside
`hasFiniteExtensions_of_hasNormalRealizations`, run on the realization property
rather than on the posets.

The proof is Gunter's, with one simplification. He shows `A ∪ {X}` normal in `B`
by exhibiting a *largest* element of `(A ∪ {X}) ∩ ↓Z` for each `Z ∈ B`, which
needs finiteness to convert directedness into a maximum. `IsNormalIn` asks only
for non-emptiness and directedness, so the largest element is produced but
finiteness of `A` is never spent — the statement below asks only that `B ∖ A` be
finite, and only to find the maximal `X`. -/

section Refine

variable {α : Type*} [PartialOrder α] {A B : Set α}

/-- **Proposition 21, one step.** If `A ◁ B` and `B ∖ A` is finite and non-empty,
some `X ∈ B ∖ A` extends `A` by a single point, normally on both sides.

The witness is any element maximal in `B ∖ A`. Maximality is spent exactly once:
for `Z ∈ B` with `X ⊑ Z`, either `Z = X` or `X ⊏ Z`, and in the second case
maximality puts `Z` in `A`, so `Z` itself is the largest element of
`(A ∪ {X}) ∩ ↓Z`. When `X ⋢ Z` the set is `A ∩ ↓Z` unchanged and `A ◁ B`
applies directly. -/
theorem exists_singleton_step (hAB : A ◁ B) (hfin : (B \ A).Finite)
    (hne : (B \ A).Nonempty) :
    ∃ X ∈ B \ A, A ◁ insert X A ∧ insert X A ◁ B := by
  obtain ⟨X, hXmem, hXmax⟩ := hfin.exists_maximal hne
  have hXB : X ∈ B := hXmem.1
  have hsub : insert X A ⊆ B := Set.insert_subset hXB hAB.subset
  refine ⟨X, hXmem, IsNormalIn.mono_right (Set.subset_insert _ _) hsub hAB, hsub, ?_⟩
  intro Z hZB
  by_cases hXZ : X ≤ Z
  · -- `X ⊑ Z` with `Z ∈ B`: maximality of `X` forces `Z = X` or `Z ∈ A`.
    have hZA : Z = X ∨ Z ∈ A := by
      by_cases hZmem : Z ∈ B \ A
      · exact Or.inl (le_antisymm (hXmax hZmem hXZ) hXZ)
      · exact Or.inr (by simpa [hZB] using hZmem)
    -- In either case some `W ∈ insert X A` is the largest element of the slice.
    obtain ⟨W, hWmem, hWZ, hWtop⟩ :
        ∃ W ∈ insert X A, W ≤ Z ∧ ∀ y ∈ insert X A, y ≤ Z → y ≤ W := by
      rcases hZA with hZX | hZA
      · exact ⟨X, Set.mem_insert _ _, hXZ, fun _y _hy hyZ => hZX ▸ hyZ⟩
      · exact ⟨Z, Set.mem_insert_of_mem _ hZA, le_rfl, fun _y _hy hyZ => hyZ⟩
    exact ⟨⟨W, hWmem, hWZ⟩, fun a ha b hb =>
      ⟨W, ⟨hWmem, hWZ⟩, hWtop a ha.1 ha.2, hWtop b hb.1 hb.2⟩⟩
  · -- `X ⋢ Z`: the slice is `A ∩ ↓Z`, and `A ◁ B` gives it directly.
    have hslice : insert X A ∩ Set.Iic Z = A ∩ Set.Iic Z := by
      ext y
      constructor
      · rintro ⟨hy, hyZ⟩
        rcases hy with rfl | hy
        · exact absurd hyZ hXZ
        · exact ⟨hy, hyZ⟩
      · rintro ⟨hy, hyZ⟩
        exact ⟨Set.mem_insert_of_mem _ hy, hyZ⟩
    rw [hslice]
    exact ⟨hAB.nonempty hZB, hAB.directedOn hZB⟩

end Refine

/-! ## The missing input, named

`HasNormalRealizations α` is Theorem 25's hypothesis on `V`, and by rows 4 and 7
of the table above it is exactly what Gunter's `A⁺ = M(A)` supplies. It is the
statement `LemThirty.lean:426` calls "the universal property of `M` among finite
posets and normal embeddings", written out. -/

section Properties

/-- **`y` realizes over `A` the diagram type that `z` realizes over `g '' A`.**

Gunter's four formula shapes `v ⪯ X`, `v ⋠ X`, `X ⪯ v`, `X ⋠ v` for `X ∈ A`
collapse to two biconditionals once the type is complete: `y` sits below exactly
the members of `A` that `z` sits below, and above exactly those that `z` sits
above. Negated formulas are the failing directions of the same two, so nothing
of the syntax is lost. -/
def SameTypeOver {α β : Type*} [Preorder α] [Preorder β]
    (A : Set α) (g : α → β) (z : β) (y : α) : Prop :=
  ∀ a ∈ A, (a ≤ y ↔ g a ≤ z) ∧ (y ≤ a ↔ z ≤ g a)

/-- **The realization property — the missing input of `Thm29Normal`.**

Gunter 1987, Theorem 25's hypothesis on `V`, p. 21:

> Suppose that for every finite `A ◁ V` and normal type `Γ` over `A`, there is a
> realization `Z` for `Γ` such that `A ∪ {Z} ◁ V`.

with "normal type over `A`" unfolded to Gunter's own definition of *normal*
(p. 19): a type realized in some poset `β` in which `A` sits normally. The
witness is quantified over directly — `β` is that poset, `g` the normal
embedding of `A` into it, `z` the point realizing the type — rather than encoded
as syntax.

The witnessing poset appears as a **finite subset `T` of a poset `β`** rather
than as a finite type, because that is the shape every application has: `T` is a
finite normal subposet of the basis `K(E)`, sitting inside `β = K(E)`. Nothing
turns on the choice — `T = Set.univ` recovers the type reading — but it removes
every subtype transport from the reduction below.

Three hypotheses beyond Gunter's are carried, each of which makes this property
**weaker**, so that what is asked for is no more than Lemma 24 delivers: `T` is
finite; `g '' A ◁ T`, which is Gunter's `A ◁ β` in the image; and
`insert z (g '' A) ◁ T`, which is the shape the reduction always presents (there
the extension is a one-point normal extension of `A` inside `T`).

**Nothing in this file proves this property of `A∞`.** It is recorded as a `Prop`
exactly as `LemThirty.Thm29Normal` is, per this development's convention: the
statement is fixed and citable, and nothing asserts it. -/
def HasNormalRealizations (α : Type) [PartialOrder α] : Prop :=
  ∀ A : Set α, A.Finite → A ◁ (Set.univ : Set α) →
    ∀ (β : Type) [PartialOrder β] (T : Set β), T.Finite → ∀ (g : α → β) (z : β),
      (∀ a ∈ A, ∀ b ∈ A, (g a ≤ g b ↔ a ≤ b)) →
      g '' A ◁ T → insert z (g '' A) ◁ T →
      ∃ y : α, SameTypeOver A g z y ∧ insert y A ◁ (Set.univ : Set α)

/-- **The finite extension property**: the same statement with a whole finite
normal extension realized at once instead of one point at a time.

This is the form the reduction to `Thm29Normal` consumes, because the chain of
finite normal subposets that exhausts a countable Plotkin order grows by finite
chunks, not by single points.
`hasFiniteExtensions_of_hasNormalRealizations` derives it from
`HasNormalRealizations` by Gunter's Proposition 21, so it is not an independent
assumption. -/
def HasFiniteExtensions (α : Type) [PartialOrder α] : Prop :=
  ∀ A : Set α, A.Finite → A ◁ (Set.univ : Set α) →
    ∀ (β : Type) [PartialOrder β] (T : Set β), T.Finite → T.Nonempty → ∀ g : α → β,
      (∀ a ∈ A, ∀ b ∈ A, (g a ≤ g b ↔ a ≤ b)) →
      g '' A ◁ T →
      ∃ h : β → α, (∀ b ∈ T, ∀ b' ∈ T, (h b ≤ h b' ↔ b ≤ b')) ∧
        (∀ a ∈ A, h (g a) = a) ∧ h '' T ◁ (Set.univ : Set α)

/-- **The realization property is a real constraint.** It fails for the one-point
poset: the type of `true` over `{false}` in `Bool` is normal — `{false}` is normal
in `{false, true}` and so is `{false, true}` — and demands a point strictly above
its argument, which a one-point poset does not have.

Recorded because a reduction is worth nothing if the thing reduced to is
satisfied by everything. `thm29Normal_of_hasNormalRealizations` is a reduction to
a property that at least one poset lacks. -/
theorem not_hasNormalRealizations_unit : ¬ HasNormalRealizations Unit := by
  have hA : ({()} : Set Unit) ◁ (Set.univ : Set Unit) := by
    refine ⟨Set.subset_univ _, fun _ _ => ⟨⟨(), rfl, by simp⟩, ?_⟩⟩
    rintro a ⟨rfl, -⟩ b ⟨rfl, -⟩
    exact ⟨(), ⟨rfl, by simp⟩, le_rfl, le_rfl⟩
  have hT : ((fun _ : Unit => false) '' {()} : Set Bool) = {false} := by simp
  intro H
  obtain ⟨y, hy, -⟩ :=
    H {()} (Set.finite_singleton _) hA Bool {false, true} (Set.toFinite _)
      (fun _ => false) true
      (by rintro a rfl b rfl; simp)
      (by
        rw [hT]
        refine ⟨by intro z hz; simp at hz; simp [hz], ?_⟩
        rintro x (rfl | rfl)
        · exact ⟨⟨false, rfl, Set.mem_Iic.mpr le_rfl⟩,
            by rintro a ⟨rfl, -⟩ b ⟨rfl, -⟩
               exact ⟨false, ⟨rfl, Set.mem_Iic.mpr le_rfl⟩, le_rfl, le_rfl⟩⟩
        · exact ⟨⟨false, rfl, Set.mem_Iic.mpr (by decide)⟩,
            by rintro a ⟨rfl, -⟩ b ⟨rfl, -⟩
               exact ⟨false, ⟨rfl, Set.mem_Iic.mpr (by decide)⟩, le_rfl, le_rfl⟩⟩)
      (by
        rw [hT, Set.pair_comm true false]
        exact IsNormalIn.refl _)
  have h := (hy () rfl).2
  simp only [le_refl, true_iff] at h
  exact absurd h (by decide)

end Properties

/-! ## Proposition 21 turns one-point realization into finite extension

The induction is Gunter's, on `|B − A|`, but run on the realization property
rather than on the posets: each singleton step of Proposition 21 is one appeal to
`HasNormalRealizations`, and the ambient poset `β` never changes. That is what
makes the step cheap — no auxiliary poset has to be constructed to witness
normality of the type, because `β` itself already witnesses it. -/

section Extension

variable {α : Type} [PartialOrder α]

/-- **One singleton step.** Given a finite normal `S ⊆ β` and a normal embedding
`k` of `S` into `α`, and a point of `β` outside `S`, the realization property
extends `k` by one point of `β`, keeping both invariants.

`Function.invFunOn k S` is the partial inverse of `k` that presents `S` as
`g '' (k '' S)`, which is the shape `HasNormalRealizations` asks for. -/
theorem exists_step (H : HasNormalRealizations α) {β : Type} [PartialOrder β]
    {T S : Set β} (hTfin : T.Finite) (hSnorm : S ◁ T) (hne : (T \ S).Nonempty)
    (k : β → α) (hk : ∀ b ∈ S, ∀ b' ∈ S, (k b ≤ k b' ↔ b ≤ b'))
    (hkn : k '' S ◁ (Set.univ : Set α)) :
    ∃ (X : β) (k' : β → α), X ∈ T \ S ∧ (∀ b ∈ S, k' b = k b) ∧
      insert X S ◁ T ∧
      (∀ b ∈ insert X S, ∀ b' ∈ insert X S, (k' b ≤ k' b' ↔ b ≤ b')) ∧
      k' '' insert X S ◁ (Set.univ : Set α) := by
  classical
  have hSfin : S.Finite := hTfin.subset hSnorm.subset
  obtain ⟨x₀, hx₀⟩ := hne
  haveI : Nonempty β := ⟨x₀⟩
  -- Proposition 21 picks the point to adjoin.
  obtain ⟨X, hXmem, _hSX, hXnorm⟩ :=
    exists_singleton_step hSnorm (hTfin.subset fun z hz => hz.1) ⟨x₀, hx₀⟩
  have hXS : X ∉ S := hXmem.2
  have hbne : ∀ b ∈ S, b ≠ X := by rintro b hb rfl; exact hXS hb
  -- `k` is injective on `S`, so `Function.invFunOn k S` inverts it there.
  have hinj : Set.InjOn k S := fun b hb b' hb' hkk =>
    le_antisymm ((hk b hb b' hb').mp hkk.le) ((hk b' hb' b hb).mp hkk.ge)
  set g : α → β := Function.invFunOn k S with hgdef
  have hgk : ∀ b ∈ S, g (k b) = b := hinj.leftInvOn_invFunOn
  have himg : g '' (k '' S) = S := by
    ext b
    constructor
    · rintro ⟨_, ⟨b', hb', rfl⟩, rfl⟩
      rw [hgk b' hb']
      exact hb'
    · exact fun hb => ⟨k b, ⟨b, hb, rfl⟩, hgk b hb⟩
  -- The realization property, at `A := k '' S` and the witness `(β, g, X)`.
  obtain ⟨y, hy, hyn⟩ :=
    H (k '' S) (hSfin.image k) hkn β T hTfin g X
      (by
        rintro _ ⟨b, hb, rfl⟩ _ ⟨b', hb', rfl⟩
        rw [hgk b hb, hgk b' hb']
        exact (hk b hb b' hb').symm)
      (by rw [himg]; exact hSnorm)
      (by rw [himg]; exact hXnorm)
  have hupd : ∀ b ∈ S, Function.update k X y b = k b :=
    fun b hb => Function.update_of_ne (hbne b hb) _ _
  have hupdX : Function.update k X y X = y := Function.update_self _ _ _
  refine ⟨X, Function.update k X y, hXmem, hupd, hXnorm, ?_, ?_⟩
  · -- Order reflection on `insert X S`: four cases, and the two mixed ones are
    -- exactly the two biconditionals of `SameTypeOver`.
    rintro b (rfl | hb) b' (rfl | hb')
    · simp
    · rw [hupdX, hupd b' hb']
      have hty := (hy (k b') ⟨b', hb', rfl⟩).2
      rwa [hgk b' hb'] at hty
    · rw [hupdX, hupd b hb]
      have hty := (hy (k b) ⟨b, hb, rfl⟩).1
      rwa [hgk b hb] at hty
    · rw [hupd b hb, hupd b' hb']
      exact hk b hb b' hb'
  · have himg' : Function.update k X y '' insert X S = insert y (k '' S) := by
      rw [Set.image_insert_eq, hupdX]
      exact congrArg (insert y) (Set.image_congr hupd)
    rw [himg']
    exact hyn

/-- **`HasNormalRealizations` implies `HasFiniteExtensions`.** Gunter's
Proposition 21, applied `|β ∖ g '' A|` times.

The induction is on a bound for `(T ∖ S).ncard`, decreasing by one at each appeal
to `exists_step`; the invariants carried are exactly the hypotheses that step
needs, so nothing else has to be re-established along the way. -/
theorem hasFiniteExtensions_of_hasNormalRealizations (H : HasNormalRealizations α) :
    HasFiniteExtensions α := by
  classical
  intro A hAfin hAnorm β _ T hTfin hTne g hg hgA
  -- `T` non-empty makes `g '' A`, hence `A`, hence `α` non-empty; that is what
  -- `Function.invFunOn` needs, and it is the only use of the hypothesis.
  obtain ⟨t₀, ht₀⟩ := hTne
  obtain ⟨_, ⟨a₀, ha₀, rfl⟩, _⟩ := hgA.nonempty ht₀
  haveI : Nonempty α := ⟨a₀⟩
  -- Nothing left to realize: `S` is all of `T` and the current `k` is the answer.
  have finish : ∀ S : Set β, S ◁ T → (T \ S) = ∅ → ∀ k : β → α,
      (∀ b ∈ S, ∀ b' ∈ S, (k b ≤ k b' ↔ b ≤ b')) → k '' S ◁ (Set.univ : Set α) →
      ∃ h : β → α, (∀ b ∈ S, h b = k b) ∧
        (∀ b ∈ T, ∀ b' ∈ T, (h b ≤ h b' ↔ b ≤ b')) ∧ h '' T ◁ (Set.univ : Set α) := by
    intro S hSnorm hempty k hk hkn
    have hST : S = T := Set.Subset.antisymm hSnorm.subset (Set.sdiff_eq_empty.mp hempty)
    subst hST
    exact ⟨k, fun _ _ => rfl, hk, hkn⟩
  have key : ∀ n : ℕ, ∀ S : Set β, Set.ncard (T \ S) ≤ n → S ◁ T → ∀ k : β → α,
      (∀ b ∈ S, ∀ b' ∈ S, (k b ≤ k b' ↔ b ≤ b')) → k '' S ◁ (Set.univ : Set α) →
      ∃ h : β → α, (∀ b ∈ S, h b = k b) ∧
        (∀ b ∈ T, ∀ b' ∈ T, (h b ≤ h b' ↔ b ≤ b')) ∧ h '' T ◁ (Set.univ : Set α) := by
    intro n
    induction n with
    | zero =>
      intro S hcard hSnorm k hk hkn
      refine finish S hSnorm ?_ k hk hkn
      by_contra hcon
      have hpos : 0 < Set.ncard (T \ S) :=
        (Set.ncard_pos (hTfin.subset fun z hz => hz.1)).mpr
          (Set.nonempty_iff_ne_empty.mpr hcon)
      omega
    | succ n ih =>
      intro S hcard hSnorm k hk hkn
      rcases Set.eq_empty_or_nonempty (T \ S) with hempty | hne
      · exact finish S hSnorm hempty k hk hkn
      · obtain ⟨X, k', hXmem, hagree, hXnorm, hk', hk'n⟩ :=
          exists_step H hTfin hSnorm hne k hk hkn
        have hsub : (T \ insert X S) ⊆ (T \ S) :=
          fun z hz => ⟨hz.1, fun hzS => hz.2 (Set.mem_insert_of_mem _ hzS)⟩
        have hlt : Set.ncard (T \ insert X S) < Set.ncard (T \ S) :=
          Set.ncard_lt_ncard
            ((Set.ssubset_iff_of_subset hsub).mpr
              ⟨X, hXmem, fun hz => hz.2 (Set.mem_insert _ _)⟩)
            (hTfin.subset fun z hz => hz.1)
        obtain ⟨h, hh, hhrefl, hhn⟩ := ih (insert X S) (by omega) hXnorm k' hk' hk'n
        exact ⟨h, fun b hb => (hh b (Set.mem_insert_of_mem _ hb)).trans (hagree b hb),
          hhrefl, hhn⟩
  -- Start the induction from `S := g '' A`, with `k` the partial inverse of `g`.
  have hginj : Set.InjOn g A := fun a ha a' ha' hgg =>
    le_antisymm ((hg a ha a' ha').mp hgg.le) ((hg a' ha' a ha).mp hgg.ge)
  have hgg : ∀ a ∈ A, Function.invFunOn g A (g a) = a := hginj.leftInvOn_invFunOn
  have himg : Function.invFunOn g A '' (g '' A) = A := by
    ext a
    constructor
    · rintro ⟨_, ⟨a', ha', rfl⟩, rfl⟩
      rw [hgg a' ha']
      exact ha'
    · exact fun ha => ⟨g a, ⟨a, ha, rfl⟩, hgg a ha⟩
  obtain ⟨h, hh, hhrefl, hhn⟩ :=
    key (Set.ncard (T \ g '' A)) (g '' A) le_rfl hgA (Function.invFunOn g A)
      (by
        rintro _ ⟨a, ha, rfl⟩ _ ⟨a', ha', rfl⟩
        rw [hgg a ha, hgg a' ha']
        exact (hg a ha a' ha').symm)
      (by rw [himg]; exact hAnorm)
  exact ⟨h, hhrefl, fun a ha => (hh (g a) ⟨a, ha, rfl⟩).trans (hgg a ha), hhn⟩

end Extension

/-! ## Theorem 22's chain: a countable Plotkin order is exhausted by finite normal
subposets

Gunter's Enumeration Theorem (p. 19) produces a chain whose steps are singletons,
because his Theorem 25 realizes one point at a time. `HasFiniteExtensions`
realizes a whole finite normal extension at once, so the chain below is the crude
one — a finite normal subposet containing the previous stage and the next point
of an enumeration — and Proposition 21 has already been spent, inside
`hasFiniteExtensions_of_hasNormalRealizations`. -/

section Chain

variable {γ : Type} [PartialOrder γ]

/-- A finite normal subposet, packaged with its two properties so that the
recursion below can be defined by structural recursion on `ℕ`. -/
abbrev FinNormal (γ : Type) [PartialOrder γ] : Type :=
  { S : Set γ // S.Finite ∧ S ◁ (Set.univ : Set γ) }

/-- One step of the chain: a finite normal subposet containing `insert x S`,
which is what `IsPlotkinOrder` supplies. -/
noncomputable def coverStep (hP : IsPlotkinOrder (Set.univ : Set γ)) (x : γ)
    (S : FinNormal γ) : FinNormal γ :=
  ⟨(hP (insert x S.1) (S.2.1.insert x) (Set.subset_univ _)).choose,
    (hP (insert x S.1) (S.2.1.insert x) (Set.subset_univ _)).choose_spec.1,
    (hP (insert x S.1) (S.2.1.insert x) (Set.subset_univ _)).choose_spec.2.1⟩

theorem subset_coverStep (hP : IsPlotkinOrder (Set.univ : Set γ)) (x : γ) (S : FinNormal γ) :
    insert x S.1 ⊆ (coverStep hP x S).1 :=
  (hP (insert x S.1) (S.2.1.insert x) (Set.subset_univ _)).choose_spec.2.2

/-- **The chain.** `cover hP e k` is a finite normal subposet containing
`cover hP e (k-1)` and the `(k-1)`-st point of the enumeration `e`, so the chain
is increasing and — when `e` is surjective — exhausts the poset. -/
noncomputable def cover (hP : IsPlotkinOrder (Set.univ : Set γ)) (e : ℕ → γ) :
    ℕ → FinNormal γ
  | 0 => ⟨(hP ∅ Set.finite_empty (Set.empty_subset _)).choose,
      (hP ∅ Set.finite_empty (Set.empty_subset _)).choose_spec.1,
      (hP ∅ Set.finite_empty (Set.empty_subset _)).choose_spec.2.1⟩
  | (k + 1) => coverStep hP (e k) (cover hP e k)

variable {hP : IsPlotkinOrder (Set.univ : Set γ)} {e : ℕ → γ}

theorem cover_subset_succ (k : ℕ) : (cover hP e k).1 ⊆ (cover hP e (k + 1)).1 :=
  fun _ hz => subset_coverStep hP (e k) (cover hP e k) (Set.mem_insert_of_mem _ hz)

theorem mem_cover_succ (k : ℕ) : e k ∈ (cover hP e (k + 1)).1 :=
  subset_coverStep hP (e k) (cover hP e k) (Set.mem_insert _ _)

theorem cover_mono {j k : ℕ} (h : j ≤ k) : (cover hP e j).1 ⊆ (cover hP e k).1 := by
  induction k with
  | zero =>
    obtain rfl : j = 0 := Nat.le_zero.mp h
    exact subset_rfl
  | succ k ih =>
    rcases Nat.lt_or_ge j (k + 1) with hlt | hge
    · exact (ih (Nat.lt_succ_iff.mp hlt)).trans (cover_subset_succ k)
    · obtain rfl : j = k + 1 := Nat.le_antisymm h hge
      exact subset_rfl

/-- Every point of the poset lies in some stage of the chain, provided the
enumeration is surjective. -/
theorem exists_mem_cover (he : Function.Surjective e) (c : γ) :
    ∃ k, c ∈ (cover hP e k).1 := by
  obtain ⟨n, rfl⟩ := he c
  exact ⟨n + 1, mem_cover_succ n⟩

/-- Each stage is normal in the next, which is what the extension step consumes. -/
theorem cover_isNormalIn_succ (k : ℕ) : (cover hP e k).1 ◁ (cover hP e (k + 1)).1 :=
  IsNormalIn.mono_right (cover_subset_succ k) (Set.subset_univ _) (cover hP e k).2.2

theorem cover_nonempty [Nonempty γ] (k : ℕ) : (cover hP e k).1.Nonempty := by
  obtain ⟨c⟩ := ‹Nonempty γ›
  obtain ⟨x, hx, _⟩ := (cover hP e k).2.2.nonempty (Set.mem_univ c)
  exact ⟨x, hx⟩

theorem bot_mem_cover [OrderBot γ] (k : ℕ) : (⊥ : γ) ∈ (cover hP e k).1 :=
  (cover hP e k).2.2.bot_mem (Set.mem_univ _)

end Chain

/-! ## The reduction: `HasFiniteExtensions A∞` yields `Thm29Normal`

This is Gunter's Theorem 25 (p. 21) in the form this development needs. His
recursion builds an ω-sequence of isomorphisms `fₙ : Aₙ ≅ Vₙ` between finite
normal subposets of `B` and of `V`; here each `fₙ` is carried as a *total* map
`K(E) → A∞` that is order-reflecting on the `n`-th stage, so the union at the end
is an ordinary function rather than a colimit of partial ones.

Theorem 25's other hypothesis, `rt(B) ≅ rt(V)`, is discharged by
`isRoot_singleton_bot`: `K(E)` and `A∞` both have least elements, so both roots
are single points, and the base case of the recursion is the map that carries
`⊥` to `⊥`. -/

section Reduction

open Colimit

/-- The data the recursion carries at each stage: a total map, order-reflecting
on the stage, with normal image. -/
structure Stage (γ : Type) [PartialOrder γ] (S : Set γ) where
  /-- The map, total on the carrier and constrained only on `S`. -/
  toFun : γ → Ainf
  /-- Order reflection on `S`, which is Gunter's `fₙ : Aₙ ≅ Vₙ`. -/
  reflects : ∀ a ∈ S, ∀ b ∈ S, (toFun a ≤ toFun b ↔ a ≤ b)
  /-- Normality of the image, which is Gunter's `Vₙ ◁ V`. -/
  normal : toFun '' S ◁ (Set.univ : Set Ainf)

variable {γ : Type} [PartialOrder γ]

/-- **The base of the recursion.** `{⊥}` is the root on both sides
(`isRoot_singleton_bot`), so the finite extension property applied at
`A := {⊥ : A∞}` embeds the whole first stage. -/
theorem exists_base (H : HasFiniteExtensions Ainf) [OrderBot γ] {T : Set γ}
    (hTfin : T.Finite) (hTbot : (⊥ : γ) ∈ T) :
    ∃ f : γ → Ainf, (∀ a ∈ T, ∀ b ∈ T, (f a ≤ f b ↔ a ≤ b)) ∧
      f '' T ◁ (Set.univ : Set Ainf) := by
  obtain ⟨h, hrefl, _, hn⟩ :=
    H {(⊥ : Ainf)} (Set.finite_singleton _) (singleton_bot_isNormalIn (Set.mem_univ _))
      γ T hTfin ⟨⊥, hTbot⟩ (fun _ => (⊥ : γ))
      (by rintro a rfl b rfl; simp)
      (by
        have himg : (fun _ : Ainf => (⊥ : γ)) '' {(⊥ : Ainf)} = {(⊥ : γ)} := by simp
        rw [himg]
        exact singleton_bot_isNormalIn hTbot)
  exact ⟨h, hrefl, hn⟩

/-- **One step of the recursion.** The previous stage's map is inverted on its
own stage to present it as `g '' A`, and the finite extension property carries
the next stage across. -/
theorem exists_extend (H : HasFiniteExtensions Ainf) [Nonempty γ] {S T : Set γ}
    (hSfin : S.Finite) (hTfin : T.Finite) (hTne : T.Nonempty) (hST : S ◁ T)
    (F : Stage γ S) :
    ∃ f : γ → Ainf, (∀ b ∈ S, f b = F.toFun b) ∧
      (∀ a ∈ T, ∀ b ∈ T, (f a ≤ f b ↔ a ≤ b)) ∧ f '' T ◁ (Set.univ : Set Ainf) := by
  classical
  have hinj : Set.InjOn F.toFun S := fun b hb b' hb' hkk =>
    le_antisymm ((F.reflects b hb b' hb').mp hkk.le) ((F.reflects b' hb' b hb).mp hkk.ge)
  have hfg : ∀ b ∈ S, Function.invFunOn F.toFun S (F.toFun b) = b := hinj.leftInvOn_invFunOn
  have himg : Function.invFunOn F.toFun S '' (F.toFun '' S) = S := by
    ext b
    constructor
    · rintro ⟨_, ⟨b', hb', rfl⟩, rfl⟩
      rw [hfg b' hb']
      exact hb'
    · exact fun hb => ⟨F.toFun b, ⟨b, hb, rfl⟩, hfg b hb⟩
  obtain ⟨h, hrefl, hagree, hn⟩ :=
    H (F.toFun '' S) (hSfin.image _) F.normal γ T hTfin hTne
      (Function.invFunOn F.toFun S)
      (by
        rintro _ ⟨b, hb, rfl⟩ _ ⟨b', hb', rfl⟩
        rw [hfg b hb, hfg b' hb']
        exact (F.reflects b hb b' hb').symm)
      (by rw [himg]; exact hST)
  refine ⟨h, fun b hb => ?_, hrefl, hn⟩
  have hb' := hagree (F.toFun b) ⟨b, hb, rfl⟩
  rwa [hfg b hb] at hb'

/-- The base stage, as data. -/
noncomputable def baseStage (H : HasFiniteExtensions Ainf) [OrderBot γ] {T : Set γ}
    (hTfin : T.Finite) (hTbot : (⊥ : γ) ∈ T) : Stage γ T :=
  ⟨(exists_base H hTfin hTbot).choose, (exists_base H hTfin hTbot).choose_spec.1,
    (exists_base H hTfin hTbot).choose_spec.2⟩

/-- The successor stage, as data. -/
noncomputable def extendStage (H : HasFiniteExtensions Ainf) [Nonempty γ] {S T : Set γ}
    (hSfin : S.Finite) (hTfin : T.Finite) (hTne : T.Nonempty) (hST : S ◁ T)
    (F : Stage γ S) : Stage γ T :=
  ⟨(exists_extend H hSfin hTfin hTne hST F).choose,
    (exists_extend H hSfin hTfin hTne hST F).choose_spec.2.1,
    (exists_extend H hSfin hTfin hTne hST F).choose_spec.2.2⟩

theorem extendStage_agree (H : HasFiniteExtensions Ainf) [Nonempty γ] {S T : Set γ}
    (hSfin : S.Finite) (hTfin : T.Finite) (hTne : T.Nonempty) (hST : S ◁ T)
    (F : Stage γ S) :
    ∀ b ∈ S, (extendStage H hSfin hTfin hTne hST F).toFun b = F.toFun b :=
  (exists_extend H hSfin hTfin hTne hST F).choose_spec.1

/-- **The ω-sequence of stages.** Gunter's `fₙ`, with `V₀ = rt(V) = {⊥}` as the
base and the finite extension property as the step. -/
noncomputable def stage (H : HasFiniteExtensions Ainf) [OrderBot γ] [Nonempty γ]
    (hP : IsPlotkinOrder (Set.univ : Set γ)) (e : ℕ → γ) :
    (k : ℕ) → Stage γ (cover hP e k).1
  | 0 => baseStage H (cover hP e 0).2.1 (bot_mem_cover 0)
  | (k + 1) =>
      extendStage H (cover hP e k).2.1 (cover hP e (k + 1)).2.1 (cover_nonempty (k + 1))
        (cover_isNormalIn_succ k) (stage H hP e k)

variable [OrderBot γ] [Nonempty γ] {hP : IsPlotkinOrder (Set.univ : Set γ)} {e : ℕ → γ}

theorem stage_agree (H : HasFiniteExtensions Ainf) (k : ℕ) :
    ∀ b ∈ (cover hP e k).1, (stage H hP e (k + 1)).toFun b = (stage H hP e k).toFun b :=
  extendStage_agree H _ _ _ _ (stage H hP e k)

/-- **The sequence is stable**: once a point has entered a stage, no later stage
moves it. This is what makes the union a function. -/
theorem stage_stable (H : HasFiniteExtensions Ainf) (j : ℕ) :
    ∀ (k : ℕ), j ≤ k → ∀ b ∈ (cover hP e j).1,
      (stage H hP e k).toFun b = (stage H hP e j).toFun b := by
  intro k
  induction k with
  | zero =>
    intro hjk _ _
    obtain rfl : j = 0 := Nat.le_zero.mp hjk
    rfl
  | succ k ih =>
    intro hjk b hb
    rcases Nat.lt_or_ge j (k + 1) with hlt | hge
    · have hjk' := Nat.lt_succ_iff.mp hlt
      rw [stage_agree H k b (cover_mono hjk' hb), ih hjk' b hb]
    · obtain rfl : j = k + 1 := Nat.le_antisymm hjk hge
      rfl

/-- The stage images increase, which makes the family `◁`-directed and its union
normal by Lemma 4.4 (`isNormalIn_sUnion`). -/
theorem stageImage_subset (H : HasFiniteExtensions Ainf) {m l : ℕ} (h : m ≤ l) :
    (stage H hP e m).toFun '' (cover hP e m).1 ⊆
      (stage H hP e l).toFun '' (cover hP e l).1 := by
  rintro _ ⟨c, hc, rfl⟩
  exact ⟨c, cover_mono h hc, stage_stable H m l h c hc⟩

open scoped Classical in
/-- **The union of the stages**, as a total map. `c` is sent by the earliest
stage that contains it; `limitMap_eq` says every later stage agrees. -/
noncomputable def limitMap (H : HasFiniteExtensions Ainf)
    (hP : IsPlotkinOrder (Set.univ : Set γ)) (e : ℕ → γ) (he : Function.Surjective e)
    (c : γ) : Ainf :=
  (stage H hP e (Nat.find (exists_mem_cover (hP := hP) he c))).toFun c

open scoped Classical in
theorem limitMap_eq (H : HasFiniteExtensions Ainf) (he : Function.Surjective e)
    {k : ℕ} {c : γ} (hc : c ∈ (cover hP e k).1) :
    limitMap H hP e he c = (stage H hP e k).toFun c :=
  (stage_stable H _ k (Nat.find_le hc) c
    (Nat.find_spec (exists_mem_cover (hP := hP) he c))).symm

end Reduction

/-! ## `Thm29Normal`, reduced

`LemThirty.Thm29Normal` is used exactly as `LemThirty.lean:464` states it: the
same `E`, the same instance binders `[CompletePartialOrder E] [Domain E]`, the
same conclusion. No binder is added, and no hypothesis is weakened. -/

section Main

open Colimit

/-- **Gunter 1987, Theorem 25, in this development's terms:
`HasFiniteExtensions A∞` implies `LemThirty.Thm29Normal`.**

Both halves of "bifinite **domain**" are spent, and in different places:

* `IsBifinite E` makes `K(E)` a Plotkin order
  (`BifiniteUniversal.isPlotkinOrder_univ_subtype`), which is what supplies the
  chain of finite normal subposets;
* `[Domain E]` makes `K(E)` countable, which is what supplies the enumeration
  `e` the chain runs along. `LemThirty.countable_compacts_of_reflects` and
  `A3Thm29.not_thm29NormalWithoutDomain` already show this half is not optional
  — without it the conclusion is refutable.

The root hypothesis of Gunter's Theorem 25, `rt(B) ≅ rt(V)`, is discharged by
`isRoot_singleton_bot` on both sides and appears here only as `exists_base`,
which starts the recursion at `⊥ ↦ ⊥`. -/
theorem thm29Normal_of_hasFiniteExtensions (H : HasFiniteExtensions Ainf) :
    LemThirty.Thm29Normal := by
  intro E _ _ hE
  haveI : Countable ↥(compacts E) := (Domain.countable_compacts (α := E)).to_subtype
  have hP : IsPlotkinOrder (Set.univ : Set ↥(compacts E)) :=
    BifiniteUniversal.isPlotkinOrder_univ_subtype hE
  obtain ⟨e, he⟩ := exists_surjective_nat ↥(compacts E)
  refine ⟨limitMap H hP e he, fun a b => ?_, ?_⟩
  · -- Order reflection: put both points in one stage and use that stage's.
    obtain ⟨ka, hka⟩ := exists_mem_cover (hP := hP) he a
    obtain ⟨kb, hkb⟩ := exists_mem_cover (hP := hP) he b
    have ha : a ∈ (cover hP e (max ka kb)).1 := cover_mono (le_max_left _ _) hka
    have hb : b ∈ (cover hP e (max ka kb)).1 := cover_mono (le_max_right _ _) hkb
    rw [limitMap_eq H he ha, limitMap_eq H he hb]
    exact (stage H hP e (max ka kb)).reflects a ha b hb
  · -- Normality: the range is the union of the stage images, which is `◁`-directed.
    have hrange : Set.range (limitMap H hP e he) =
        ⋃₀ {N | ∃ k : ℕ, N = (stage H hP e k).toFun '' (cover hP e k).1} := by
      ext x
      constructor
      · rintro ⟨c, rfl⟩
        obtain ⟨k, hk⟩ := exists_mem_cover (hP := hP) he c
        exact ⟨_, ⟨k, rfl⟩, c, hk, (limitMap_eq H he hk).symm⟩
      · rintro ⟨_, ⟨k, rfl⟩, c, hc, rfl⟩
        exact ⟨c, limitMap_eq H he hc⟩
    rw [hrange]
    refine isNormalIn_sUnion ⟨_, 0, rfl⟩ ?_ ?_
    · rintro _ ⟨k, rfl⟩
      exact (stage H hP e k).normal
    · rintro _ ⟨m, rfl⟩ _ ⟨n, rfl⟩
      refine ⟨(stage H hP e (max m n)).toFun '' (cover hP e (max m n)).1,
        ⟨max m n, rfl⟩, ?_, ?_⟩
      · exact IsNormalIn.mono_right (stageImage_subset H (le_max_left m n))
          (Set.subset_univ _) (stage H hP e m).normal
      · exact IsNormalIn.mono_right (stageImage_subset H (le_max_right m n))
          (Set.subset_univ _) (stage H hP e n).normal

/-- **The reduction, from the missing input itself.**
`HasNormalRealizations A∞ → LemThirty.Thm29Normal`, by
`hasFiniteExtensions_of_hasNormalRealizations` (Gunter's Proposition 21) followed
by `thm29Normal_of_hasFiniteExtensions` (his Theorem 25).

This is the round's result: `Thm29Normal` is no longer open, it is *reduced* — to
one precisely stated property of `A∞`, which Gunter 1987 proves of `M(A)` in
Lemma 24 and p. 23. -/
theorem thm29Normal_of_hasNormalRealizations (H : HasNormalRealizations Ainf) :
    LemThirty.Thm29Normal :=
  thm29Normal_of_hasFiniteExtensions (hasFiniteExtensions_of_hasNormalRealizations H)

/-- **The residue, localized to one stage.** `HasNormalRealizations A∞` follows
from the same property asked of the stages alone: realize the type inside *some*
stage, and `A∞` inherits it.

This is Gunter's Corollary 26 (p. 21) — "Suppose `C ◁ V_A` is finite. Then
`C ◁ Aₙ` for some `n`" — with `exists_stage_ge_of_finite` supplying the stage and
`isNormalIn_range_incl` carrying the conclusion back. Its hypothesis is
`LemThirty.lean:426`'s sentence exactly: the extension of a normal embedding of a
finite normal subposet from one stage to the next, i.e. **the universal property
of `M` among finite posets under normal embedding**, which is Gunter's Lemma 24
(p. 20) at the explicit `A⁺ = M(A)` of his p. 23.

Stated as a hypothesis rather than a named `Prop` so that it adds nothing to the
count of propositions this development asserts without proof. -/
theorem hasNormalRealizations_of_stages
    (h : ∀ (n : ℕ) (A : Set Ainf), A.Finite → A ◁ Set.range (incl n) →
      ∀ (β : Type) [PartialOrder β] (T : Set β), T.Finite → ∀ (g : Ainf → β) (z : β),
        (∀ a ∈ A, ∀ b ∈ A, (g a ≤ g b ↔ a ≤ b)) →
        g '' A ◁ T → insert z (g '' A) ◁ T →
        ∃ y : Ainf, SameTypeOver A g z y ∧ ∃ m : ℕ, insert y A ◁ Set.range (incl m)) :
    HasNormalRealizations Ainf := by
  intro A hAfin hAnorm β _ T hTfin g z hg hgA hzA
  obtain ⟨n, -, hAn⟩ := LemThirty.exists_stage_ge_of_finite hAfin 0
  obtain ⟨y, hy, m, hm⟩ :=
    h n A hAfin (IsNormalIn.mono_right hAn (Set.subset_univ _) hAnorm)
      β T hTfin g z hg hgA hzA
  exact ⟨y, hy, hm.trans (isNormalIn_range_incl m)⟩

/-- **What the reduction buys downstream**: Theorem 29's second sentence at the
paper's own hypothesis, by `LemThirty.thm29SecondAtDomains_of_thm29Normal`. With
`A3Thm29.five_conjuncts_of_thm29Normal` this makes five of Lemma 30's ten
conjuncts consequences of the realization property of `A∞` alone. -/
theorem thm29SecondAtDomains_of_hasNormalRealizations (H : HasNormalRealizations Ainf) :
    LemThirty.Thm29SecondAtDomains :=
  LemThirty.thm29SecondAtDomains_of_thm29Normal (thm29Normal_of_hasNormalRealizations H)

end Main

end ScottDomains.R46.Agent2
