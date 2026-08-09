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

Three hypotheses beyond Gunter's are carried, each of which makes this property
**weaker**, so that what is asked for is no more than Lemma 24 delivers:
`Finite β`; `g '' A ◁ Set.univ`, which is Gunter's `A ◁ β` in the image; and
`insert z (g '' A) ◁ Set.univ`, which is the shape the reduction always presents
(there the extension is a one-point normal extension of `A` inside `β`).

**Nothing in this file proves this property of `A∞`.** It is recorded as a `Prop`
exactly as `LemThirty.Thm29Normal` is, per this development's convention: the
statement is fixed and citable, and nothing asserts it. -/
def HasNormalRealizations (α : Type) [PartialOrder α] : Prop :=
  ∀ A : Set α, A.Finite → A ◁ (Set.univ : Set α) →
    ∀ (β : Type) [PartialOrder β] [Finite β] (g : α → β) (z : β),
      (∀ a ∈ A, ∀ b ∈ A, (g a ≤ g b ↔ a ≤ b)) →
      g '' A ◁ (Set.univ : Set β) →
      insert z (g '' A) ◁ (Set.univ : Set β) →
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
    ∀ (β : Type) [PartialOrder β] [Finite β] [Nonempty β] (g : α → β),
      (∀ a ∈ A, ∀ b ∈ A, (g a ≤ g b ↔ a ≤ b)) →
      g '' A ◁ (Set.univ : Set β) →
      ∃ h : β → α, (∀ b b' : β, h b ≤ h b' ↔ b ≤ b') ∧
        (∀ a ∈ A, h (g a) = a) ∧ Set.range h ◁ (Set.univ : Set α)

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
    [Finite β] [Nonempty β] {S : Set β} (hSnorm : S ◁ (Set.univ : Set β))
    (hSfin : S.Finite) (hne : (Set.univ \ S : Set β).Nonempty)
    (k : β → α) (hk : ∀ b ∈ S, ∀ b' ∈ S, (k b ≤ k b' ↔ b ≤ b'))
    (hkn : k '' S ◁ (Set.univ : Set α)) :
    ∃ (X : β) (k' : β → α), X ∈ Set.univ \ S ∧ (∀ b ∈ S, k' b = k b) ∧
      insert X S ◁ (Set.univ : Set β) ∧
      (∀ b ∈ insert X S, ∀ b' ∈ insert X S, (k' b ≤ k' b' ↔ b ≤ b')) ∧
      k' '' insert X S ◁ (Set.univ : Set α) := by
  classical
  -- Proposition 21 picks the point to adjoin.
  obtain ⟨X, hXmem, _hSX, hXnorm⟩ :=
    exists_singleton_step hSnorm (Set.toFinite _) hne
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
    H (k '' S) (hSfin.image k) hkn β g X
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

The induction is on a bound for `(Set.univ ∖ S).ncard`, decreasing by one at each
appeal to `exists_step`; the invariants carried are exactly the hypotheses that
step needs, so nothing else has to be re-established along the way. -/
theorem hasFiniteExtensions_of_hasNormalRealizations (H : HasNormalRealizations α) :
    HasFiniteExtensions α := by
  classical
  intro A hAfin hAnorm β _ _ _ g hg hgA
  -- `α` is non-empty because `β` is and `g '' A` is normal in it.
  have hAne : (g '' A).Nonempty := by
    obtain ⟨b⟩ := ‹Nonempty β›
    obtain ⟨c, hc, _⟩ := hgA.nonempty (Set.mem_univ b)
    exact ⟨c, hc⟩
  obtain ⟨_, a₀, ha₀, _⟩ := hAne
  haveI : Nonempty α := ⟨a₀⟩
  -- The induction, on a bound for the number of points still to be realized.
  -- Nothing left to realize: `S` is everything and the current `k` is the answer.
  have finish : ∀ S : Set β, (Set.univ \ S : Set β) = ∅ → ∀ k : β → α,
      (∀ b ∈ S, ∀ b' ∈ S, (k b ≤ k b' ↔ b ≤ b')) → k '' S ◁ (Set.univ : Set α) →
      ∃ h : β → α, (∀ b ∈ S, h b = k b) ∧ (∀ b b' : β, h b ≤ h b' ↔ b ≤ b') ∧
        Set.range h ◁ (Set.univ : Set α) := by
    intro S hempty k hk hkn
    have huniv : S = Set.univ := Set.univ_subset_iff.mp (Set.sdiff_eq_empty.mp hempty)
    subst huniv
    refine ⟨k, fun _ _ => rfl, fun b b' => hk b (Set.mem_univ b) b' (Set.mem_univ b'), ?_⟩
    rwa [← Set.image_univ]
  have key : ∀ n : ℕ, ∀ S : Set β, Set.ncard (Set.univ \ S : Set β) ≤ n →
      S ◁ (Set.univ : Set β) → ∀ k : β → α,
      (∀ b ∈ S, ∀ b' ∈ S, (k b ≤ k b' ↔ b ≤ b')) → k '' S ◁ (Set.univ : Set α) →
      ∃ h : β → α, (∀ b ∈ S, h b = k b) ∧ (∀ b b' : β, h b ≤ h b' ↔ b ≤ b') ∧
        Set.range h ◁ (Set.univ : Set α) := by
    intro n
    induction n with
    | zero =>
      intro S hcard _ k hk hkn
      refine finish S ?_ k hk hkn
      by_contra hcon
      have hpos : 0 < Set.ncard (Set.univ \ S : Set β) :=
        (Set.ncard_pos (Set.toFinite _)).mpr (Set.nonempty_iff_ne_empty.mpr hcon)
      omega
    | succ n ih =>
      intro S hcard hSnorm k hk hkn
      rcases Set.eq_empty_or_nonempty (Set.univ \ S : Set β) with hempty | hne
      · exact finish S hempty k hk hkn
      · obtain ⟨X, k', hXmem, hagree, hXnorm, hk', hk'n⟩ :=
          exists_step H hSnorm (Set.toFinite S) hne k hk hkn
        have hsub : (Set.univ \ insert X S : Set β) ⊆ (Set.univ \ S : Set β) :=
          fun z hz => ⟨hz.1, fun hzS => hz.2 (Set.mem_insert_of_mem _ hzS)⟩
        have hlt : Set.ncard (Set.univ \ insert X S : Set β) <
            Set.ncard (Set.univ \ S : Set β) :=
          Set.ncard_lt_ncard
            ((Set.ssubset_iff_of_subset hsub).mpr
              ⟨X, hXmem, fun hz => hz.2 (Set.mem_insert _ _)⟩)
            (Set.toFinite _)
        obtain ⟨h, hh, hhrefl, hhn⟩ :=
          ih (insert X S) (by omega) hXnorm k' hk' hk'n
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
    key (Set.ncard (Set.univ \ g '' A : Set β)) (g '' A) le_rfl hgA (Function.invFunOn g A)
      (by
        rintro _ ⟨a, ha, rfl⟩ _ ⟨a', ha', rfl⟩
        rw [hgg a ha, hgg a' ha']
        exact (hg a ha a' ha').symm)
      (by rw [himg]; exact hAnorm)
  exact ⟨h, hhrefl, fun a ha => (hh (g a) ⟨a, ha, rfl⟩).trans (hgg a ha), hhn⟩

end Extension

end ScottDomains.R46.Agent2
