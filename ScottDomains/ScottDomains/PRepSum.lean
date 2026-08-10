import ScottDomains.PRep
import ScottDomains.Atomless
import ScottDomains.Isomorphism.Copair

/-!
# Lemma 28 at §7.3's own `U`, and the sum conjuncts

Gunter & Scott, *Semantic Domains*, §7.3. This file supplies two things
`ScottDomains.PRep` could not: the **instantiation of Lemma 28's conjuncts at the
paper's `U`**, and the sum operators' conjuncts.

## The statement, re-read from the source

Page 42 of `Gunter Scott 1990.pdf` rendered at 600 dpi and read as an image —
`pdftotext` mangles every operator glyph on the line, since the file's Type 3
bitmap fonts carry no usable `ToUnicode` map:

> **Lemma 28** The following operators are representable over `U`:
> `→`, `∘→`, `×`, `⊗`, `+`, `⊕`, `(·)⊥`, `(·)♯`, `(·)♭`.

Nine operators, `♯` and `♭` and no `♮`, and `∘→` (the strict function space,
`⇸`) present. This is an independent re-measurement of r0036's reading and it
agrees with it, hence with `PRep.Lemma28`'s nine conjuncts.

The same page states the representation scheme this file consumes, in the
paragraph two above Lemma 28 — the paper writes it out for `+` specifically:

> To get a representation for `+`, take a pair of continuous functions
> `Φ₊ : U → (U + U)`, `Ψ₊ : (U + U) → U` such that `Φ₊ ∘ Ψ₊ = id` and
> `Ψ₊ ∘ Φ₊ ⊑ id`. Then take `R₊(r, s) = Ψ₊ ∘ (r + s) ∘ Φ₊`.

`PRep.isPRepresentable₂_of_repFamily` is exactly that displayed recipe with
`(Φ₊, Ψ₊)` abstracted to `(fn, gr)`, so every conjunct here is the paper's own
construction with the pair supplied rather than assumed.

## The headline: where the pair comes from, and why it is now free

`PRep.lean`'s conjuncts are all conditional on that pair. Until r0036 there was
no way to produce it at `U`: `Dyadic.thm27` carried the hypothesis
`IsNormallyRepresented ↥(compacts D)`, so the instantiation was recorded in
`PRep.lean` as "blocked one level below this file". **That note was retired in
the same round it was written.** `Atomless.isNormallyRepresented_compacts`
discharges the hypothesis for every bounded complete domain, and
`Atomless.thm27` is therefore Theorem 27 with no hypothesis at all:

    ∀ D, [CompletePartialOrder D] [Domain D] [BoundedComplete D] →
      ∃ e p, ScottHom.IsEmbeddingProjectionPair e p

Unfolding `IsEmbeddingProjectionPair e p` gives `p ∘ e = id` and `e ∘ p ⊑ id`
with `e : D → U` and `p : U → D`. Setting `fn := p` and `gr := e` is **verbatim**
the paper's `(Φ, Ψ)`: the two conditions match, in that order, with no
adjustment. `pairAtU` below is that one-line transposition, and it is what turns
every conditional conjunct of `PRep` into an unconditional statement about `U`.

The condition to be met is that the operator's *result* be a bounded complete
domain — which is exactly **Lemma 10**, already proved here as
`ClosureProperties.lemma10`. So each conjunct at `U` costs one `Domain` instance
plus one `lem10_*`, and Lemma 10 and Lemma 28 compose: Lemma 10 says the operator
lands in the class Theorem 27 quantifies over, Theorem 27 supplies the retraction
pair, and `PRep`'s scheme turns the pair into a representation.

## What this file proves

| # | Result | Statement |
| - | ------ | --------- |
| 1 | `pairAtU` | Theorem 27 transposed into `PRep`'s `(fn, gr)` shape |
| 2 | `repProdAtU` | conjunct 3, `×` — **no hypothesis** |
| 3 | `repSepSumAtU` | conjunct 5, `+` — **no hypothesis** |
| 4 | `repCoalSumAtU` | conjunct 6, `⊕` — **no hypothesis** |
| 5 | `repLiftAtU` | conjunct 7, `(·)⊥` — **no hypothesis** |
| 6 | `lemma28AtU_of` | `Lemma28AtU` from the five conjuncts still open |

Conjuncts 5 and 6 are proved here for the first time, at any carrier:
`rep_coalSum` and `rep_sepSum` are the abstract forms, `domain_coalescedSum` is
the closure property they need, and the two `AtU` theorems are their
instantiations.

`lemma28AtU_of` is the deliverable the conjunct work feeds: its arity is the
count of what remains — `→`, `⇸`, `⊗`, `(·)♯`, `(·)♭`, five of nine — and it
drops by one each time a conjunct is proved.

## The closure property the library was missing

`IsPRepresentable` routes through a `Domain` on the operator's image, and
`Domain` is `IsAlgebraic` together with a countable basis. The coalesced sum
carries **Lemma 10** (bounded completeness, `lem10_sum`) and **Lemma 17**
(bifiniteness, `lem17_sum`) and nothing else: `IsAlgebraic (CoalescedSum A B)` is
proved nowhere in the development, because §4.5 and §6.2 are the only closure
properties the paper states for it and neither is algebraicity. That is the one
real gap the `⊕` conjunct hits, and it is a gap in the library rather than in the
notion. `isAlgebraic_coalescedSum` and `domain_coalescedSum` below close it, from
`Skeleton/Sum.lean`'s compactness criterion. `+` inherits the result rather than
routing around it, since `SeparatedSum A B` *is* `CoalescedSum A⊥ B⊥`.

## No conjunct is stubbed

There is no `sorry` in this file. A conjunct not proved is a hypothesis of
`lemma28AtU_of` and is named in the table above; it is never a hole in a claimed
proof, and no algebraicity obligation is carried as an unproved assumption.
-/

namespace ScottDomains.PRepSum

open ScottDomains ScottDomains.BifiniteUniversal ScottDomains.PRep

universe u

/-! ## §7.3's retraction pair at `U`, from Theorem 27

The paper introduces `(Φ₊, Ψ₊)` by saying "take a pair of continuous functions
… such that `Φ₊ ∘ Ψ₊ = id` and `Ψ₊ ∘ Φ₊ ⊑ id`", and leaves the existence to
Theorem 27 on the same page. `pairAtU` is that step: the *only* content is
matching `IsEmbeddingProjectionPair`'s two components to `PRep`'s two hypotheses,
and they match without reordering or reversing anything.

Note which way the arrows run. Theorem 27 produces an embedding `e : D → U` and a
projection `p : U → D` — `D` sits *inside* `U`. `PRep`'s scheme wants
`fn : U → V` and `gr : V → U` with `fn ∘ gr = id` and `gr ∘ fn ⊑ id`, so `fn` is
the projection and `gr` the embedding: the composite `gr ∘ fn : U → U` is the
projection onto the copy of `V` inside `U`, which is what makes
`repOf fn gr C = gr ∘ C ∘ fn` land in `Fp(U)` at all. -/

/-- **Theorem 27 in `PRep`'s coordinates.** For any bounded complete domain `V`
there is a pair `fn : U → V`, `gr : V → U` with `fn ∘ gr = id` and
`gr ∘ fn ⊑ id` — the hypotheses of every conjunct in `ScottDomains.PRep`.

The proof is `Atomless.thm27` with the two components of
`ScottHom.IsEmbeddingProjectionPair` handed over in place. What was blocked
before r0036 is `Atomless.thm27` itself, not this transposition. -/
theorem pairAtU (V : Type) [CompletePartialOrder V] [Domain V] [BoundedComplete V] :
    ∃ (fn : ScottHom Dyadic.U V) (gr : ScottHom V Dyadic.U),
      (∀ y, fn (gr y) = y) ∧ ∀ x, gr (fn x) ≤ x := by
  obtain ⟨e, p, hpe, hep⟩ := Atomless.thm27 V
  exact ⟨p, e, hpe, hep⟩

/-! ## Conjuncts 3 and 7 at `U`

`PRep.rep_prod` and `PRep.rep_lift` are proved; each takes the pair as a
hypothesis. Here the pair is produced, so the conjunct becomes a closed
statement about the paper's carrier.

The `Domain` and `BoundedComplete` instances the pair needs on the *result* are
where Lemma 10 is spent, one conjunct each:

| # | Operator | `Domain` of the result | `BoundedComplete` of the result |
| - | -------- | ---------------------- | ------------------------------- |
| 1 | `×`      | `PowerdomainRep.domain_prod` | `lem10_prod` (Lemma 10, conjunct 3) |
| 2 | `(·)⊥`   | `ClosureProperties.liftDomain` (an instance) | `lem10_lift` (Lemma 10, conjunct 7) |
-/

/-- **`×` is p-representable over `U`** — conjunct 3 of Lemma 28, at the paper's
own carrier and with no hypothesis.

`U × U` is a bounded complete domain (`domain_prod` and Lemma 10's third
conjunct), so Theorem 27 gives the pair `(×⁻, ×⁺)` the paper's `R×(r, s) =
×⁺ ∘ (r × s) ∘ ×⁻` needs, and `PRep.rep_prod` consumes it. -/
theorem repProdAtU : IsPRepresentable₂ Dyadic.U prodOp := by
  haveI : Domain (Dyadic.U × Dyadic.U) := PowerdomainRep.domain_prod
  haveI : BoundedComplete (Dyadic.U × Dyadic.U) := lem10_prod
  obtain ⟨_fn, _gr, hfg, hgf⟩ := pairAtU (Dyadic.U × Dyadic.U)
  exact rep_prod hfg hgf

/-- **`(·)⊥` is p-representable over `U`** — conjunct 7 of Lemma 28, at the
paper's own carrier and with no hypothesis. Same route as `repProdAtU`, with
`liftDomain` and Lemma 10's seventh conjunct in place of the product's. -/
theorem repLiftAtU : IsPRepresentable Dyadic.U liftOp := by
  haveI : BoundedComplete (WithBot Dyadic.U) := lem10_lift
  obtain ⟨_fn, _gr, hfg, hgf⟩ := pairAtU (WithBot Dyadic.U)
  exact rep_lift hfg hgf

/-! ## `A ⊕ B` is a domain when `A` and `B` are

Lemma 10 gives *bounded completeness* of `A ⊕ B` (`lem10_sum`) and Lemma 17 gives
*bifiniteness* (`lem17_sum`), but nothing in the development gives the coalesced
sum a `Domain` — the paper never needs it, since §4.5 and §6.2 each state their
own closure property and neither is algebraicity. `Fp` needs it: the second
component of `IsFinitaryProjection (R (r ⊕ s))` is a `Domain` on the image, and
the image is a coalesced sum of the two images.

The argument is entirely a case split on `WithBot` and on the side of the
injection. What makes it short is that `Skeleton/Sum.lean` already proves the
compactness criterion — `isCompactElement_coe_inl_iff`, `↑(inl x)` compact in
`A ⊕ B` iff `x` compact in `A` — so the compacts of the sum below `↑(inl x)` are
exactly the injections of the non-`⊥` compacts of `A` below `x`, plus the
adjoined bottom. `⊥` has to be added and removed by hand at each step, because
the injection does not carry `⊥_A` into the sum: that is what `isLUB_diff_bot`
is for, and it is the only step where anything could go wrong. -/

section CoalescedSumDomain

variable {A B : Type*} [CompletePartialOrder A] [CompletePartialOrder B]

/-- A non-`⊥` compact of `A` injects to a compact of `A ⊕ B`. -/
theorem isCompactElement_sumInl {x : A} (hx : x ≠ ⊥) (hk : IsCompactElement x) :
    IsCompactElement (sumInl B x : CoalescedSum A B) := by
  rw [sumInl_of_ne_bot hx]
  exact (isCompactElement_coe_inl_iff (r := ⟨Sum.inl x, hx⟩) rfl).mpr hk

/-- The mirror image of `isCompactElement_sumInl`. -/
theorem isCompactElement_sumInr {y : B} (hy : y ≠ ⊥) (hk : IsCompactElement y) :
    IsCompactElement (sumInr A y : CoalescedSum A B) := by
  rw [sumInr_of_ne_bot hy]
  exact (isCompactElement_coe_inr_iff (r := ⟨Sum.inr y, hy⟩) rfl).mpr hk

/-- The injection of a non-`⊥` compact approximant of `x` is a compact
approximant of `↑(inl x)`. -/
theorem mem_compactsBelow_sumInl {q : NonBotSum A B} {x : A} (hq : q.val = Sum.inl x)
    {k : A} (hk : k ∈ compactsBelow x) (hkb : k ≠ ⊥) :
    (sumInl B k : CoalescedSum A B) ∈ compactsBelow (↑q : CoalescedSum A B) := by
  refine ⟨isCompactElement_sumInl hkb hk.1, ?_⟩
  rw [sumInl_of_ne_bot hkb]
  refine (WithBot.coe_le_coe (α := NonBotSum A B)).mpr ?_
  show (Sum.inl k : A ⊕ B) ≤ q.val
  rw [hq]
  exact Sum.inl_le_inl_iff.mpr hk.2

/-- The mirror image of `mem_compactsBelow_sumInl`. -/
theorem mem_compactsBelow_sumInr {q : NonBotSum A B} {y : B} (hq : q.val = Sum.inr y)
    {k : B} (hk : k ∈ compactsBelow y) (hkb : k ≠ ⊥) :
    (sumInr A k : CoalescedSum A B) ∈ compactsBelow (↑q : CoalescedSum A B) := by
  refine ⟨isCompactElement_sumInr hkb hk.1, ?_⟩
  rw [sumInr_of_ne_bot hkb]
  refine (WithBot.coe_le_coe (α := NonBotSum A B)).mpr ?_
  show (Sum.inr k : A ⊕ B) ≤ q.val
  rw [hq]
  exact Sum.inr_le_inr_iff.mpr hk.2

/-- **Every compact approximant of `↑(inl x)` is `⊥` or the injection of one of
`x`'s.** The converse of `mem_compactsBelow_sumInl`, and the inversion the
algebraicity proof runs on. -/
theorem eq_bot_or_sumInl_of_mem_compactsBelow {q : NonBotSum A B} {x : A}
    (hq : q.val = Sum.inl x) {w : CoalescedSum A B}
    (hw : w ∈ compactsBelow (↑q : CoalescedSum A B)) :
    w = ⊥ ∨ ∃ k : A, k ∈ compactsBelow x ∧ k ≠ ⊥ ∧ w = sumInl B k := by
  induction w using WithBot.recBotCoe with
  | bot => exact Or.inl rfl
  | coe t =>
    have hle : t.val ≤ q.val := (WithBot.coe_le_coe (α := NonBotSum A B)).mp hw.2
    rw [hq] at hle
    obtain ⟨k, hk, hkx⟩ := exists_inl_of_le_inl hle
    have hkb : k ≠ ⊥ := ne_bot_of_val_eq_inl hk
    refine Or.inr ⟨k, ⟨(isCompactElement_coe_inl_iff hk).mp hw.1, hkx⟩, hkb, ?_⟩
    rw [sumInl_of_ne_bot hkb]
    exact congrArg _ (Subtype.ext hk)

/-- The mirror image of `eq_bot_or_sumInl_of_mem_compactsBelow`. -/
theorem eq_bot_or_sumInr_of_mem_compactsBelow {q : NonBotSum A B} {y : B}
    (hq : q.val = Sum.inr y) {w : CoalescedSum A B}
    (hw : w ∈ compactsBelow (↑q : CoalescedSum A B)) :
    w = ⊥ ∨ ∃ k : B, k ∈ compactsBelow y ∧ k ≠ ⊥ ∧ w = sumInr A k := by
  induction w using WithBot.recBotCoe with
  | bot => exact Or.inl rfl
  | coe t =>
    have hle : t.val ≤ q.val := (WithBot.coe_le_coe (α := NonBotSum A B)).mp hw.2
    rw [hq] at hle
    obtain ⟨k, hk, hky⟩ := exists_inr_of_le_inr hle
    have hkb : k ≠ ⊥ := ne_bot_of_val_eq_inr hk
    refine Or.inr ⟨k, ⟨(isCompactElement_coe_inr_iff hk).mp hw.1, hky⟩, hkb, ?_⟩
    rw [sumInr_of_ne_bot hkb]
    exact congrArg _ (Subtype.ext hk)

/-- **A non-`⊥` element of an algebraic cpo has a non-`⊥` compact approximant.**
Otherwise `compactsBelow x = {⊥}` and algebraicity would make `x = ⊥`.
`isLUB_diff_bot` is exactly this statement, applied to `compactsBelow x`. -/
theorem compactsBelow_diff_bot_nonempty [IsAlgebraic A] {x : A} (hx : x ≠ ⊥) :
    (compactsBelow x \ {(⊥ : A)}).Nonempty :=
  (isLUB_diff_bot (IsAlgebraic.directedOn_compactsBelow x)
    (IsAlgebraic.isLUB_compactsBelow x) hx).1

theorem directedOn_compactsBelow_coe_inl [IsAlgebraic A] {q : NonBotSum A B} {x : A}
    (hq : q.val = Sum.inl x) :
    DirectedOn (· ≤ ·) (compactsBelow (↑q : CoalescedSum A B)) := by
  intro w₁ h₁ w₂ h₂
  rcases eq_bot_or_sumInl_of_mem_compactsBelow hq h₁ with rfl | ⟨k₁, hk₁, hkb₁, rfl⟩
  · exact ⟨w₂, h₂, bot_le, le_rfl⟩
  rcases eq_bot_or_sumInl_of_mem_compactsBelow hq h₂ with rfl | ⟨k₂, hk₂, hkb₂, rfl⟩
  · exact ⟨sumInl B k₁, h₁, le_rfl, bot_le⟩
  obtain ⟨k, hk, h1k, h2k⟩ := IsAlgebraic.directedOn_compactsBelow x k₁ hk₁ k₂ hk₂
  have hkb : k ≠ ⊥ := fun hb => hkb₁ (le_bot_iff.mp (h1k.trans_eq hb))
  exact ⟨sumInl B k, mem_compactsBelow_sumInl hq hk hkb, monotone_sumInl h1k, monotone_sumInl h2k⟩

theorem directedOn_compactsBelow_coe_inr [IsAlgebraic B] {q : NonBotSum A B} {y : B}
    (hq : q.val = Sum.inr y) :
    DirectedOn (· ≤ ·) (compactsBelow (↑q : CoalescedSum A B)) := by
  intro w₁ h₁ w₂ h₂
  rcases eq_bot_or_sumInr_of_mem_compactsBelow hq h₁ with rfl | ⟨k₁, hk₁, hkb₁, rfl⟩
  · exact ⟨w₂, h₂, bot_le, le_rfl⟩
  rcases eq_bot_or_sumInr_of_mem_compactsBelow hq h₂ with rfl | ⟨k₂, hk₂, hkb₂, rfl⟩
  · exact ⟨sumInr A k₁, h₁, le_rfl, bot_le⟩
  obtain ⟨k, hk, h1k, h2k⟩ := IsAlgebraic.directedOn_compactsBelow y k₁ hk₁ k₂ hk₂
  have hkb : k ≠ ⊥ := fun hb => hkb₁ (le_bot_iff.mp (h1k.trans_eq hb))
  exact ⟨sumInr A k, mem_compactsBelow_sumInr hq hk hkb, monotone_sumInr h1k, monotone_sumInr h2k⟩

theorem isLUB_compactsBelow_coe_inl [IsAlgebraic A] {q : NonBotSum A B} {x : A}
    (hq : q.val = Sum.inl x) :
    IsLUB (compactsBelow (↑q : CoalescedSum A B)) (↑q : CoalescedSum A B) := by
  refine ⟨fun w hw => hw.2, fun u hu => ?_⟩
  have hx : x ≠ ⊥ := ne_bot_of_val_eq_inl hq
  obtain ⟨k₀, hk₀, hk₀b⟩ := compactsBelow_diff_bot_nonempty (A := A) hx
  have hle₀ : (sumInl B k₀ : CoalescedSum A B) ≤ u := hu (mem_compactsBelow_sumInl hq hk₀ hk₀b)
  rw [sumInl_of_ne_bot hk₀b] at hle₀
  obtain ⟨t, rfl⟩ := exists_coe_of_coe_le hle₀
  have h₁ : (Sum.inl k₀ : A ⊕ B) ≤ t.val := (WithBot.coe_le_coe (α := NonBotSum A B)).mp hle₀
  obtain ⟨x', hx', _⟩ := exists_inl_of_inl_le h₁
  have hub : x' ∈ upperBounds (compactsBelow x) := by
    intro k hk
    by_cases hkb : k = ⊥
    · rw [hkb]; exact bot_le
    · have hkle := hu (mem_compactsBelow_sumInl hq hk hkb)
      rw [sumInl_of_ne_bot hkb] at hkle
      have h2 : (Sum.inl k : A ⊕ B) ≤ t.val := (WithBot.coe_le_coe (α := NonBotSum A B)).mp hkle
      rw [hx'] at h2
      exact Sum.inl_le_inl_iff.mp h2
  refine (WithBot.coe_le_coe (α := NonBotSum A B)).mpr ?_
  show q.val ≤ t.val
  rw [hq, hx']
  exact Sum.inl_le_inl_iff.mpr ((IsAlgebraic.isLUB_compactsBelow x).2 hub)

theorem isLUB_compactsBelow_coe_inr [IsAlgebraic B] {q : NonBotSum A B} {y : B}
    (hq : q.val = Sum.inr y) :
    IsLUB (compactsBelow (↑q : CoalescedSum A B)) (↑q : CoalescedSum A B) := by
  refine ⟨fun w hw => hw.2, fun u hu => ?_⟩
  have hy : y ≠ ⊥ := ne_bot_of_val_eq_inr hq
  obtain ⟨k₀, hk₀, hk₀b⟩ := compactsBelow_diff_bot_nonempty (A := B) hy
  have hle₀ : (sumInr A k₀ : CoalescedSum A B) ≤ u := hu (mem_compactsBelow_sumInr hq hk₀ hk₀b)
  rw [sumInr_of_ne_bot hk₀b] at hle₀
  obtain ⟨t, rfl⟩ := exists_coe_of_coe_le hle₀
  have h₁ : (Sum.inr k₀ : A ⊕ B) ≤ t.val := (WithBot.coe_le_coe (α := NonBotSum A B)).mp hle₀
  obtain ⟨y', hy', _⟩ := exists_inr_of_inr_le h₁
  have hub : y' ∈ upperBounds (compactsBelow y) := by
    intro k hk
    by_cases hkb : k = ⊥
    · rw [hkb]; exact bot_le
    · have hkle := hu (mem_compactsBelow_sumInr hq hk hkb)
      rw [sumInr_of_ne_bot hkb] at hkle
      have h2 : (Sum.inr k : A ⊕ B) ≤ t.val := (WithBot.coe_le_coe (α := NonBotSum A B)).mp hkle
      rw [hy'] at h2
      exact Sum.inr_le_inr_iff.mp h2
  refine (WithBot.coe_le_coe (α := NonBotSum A B)).mpr ?_
  show q.val ≤ t.val
  rw [hq, hy']
  exact Sum.inr_le_inr_iff.mpr ((IsAlgebraic.isLUB_compactsBelow y).2 hub)

/-- **`A ⊕ B` is algebraic when `A` and `B` are.** Three cases: the adjoined
bottom, whose only compact approximant is itself, and the two injections, each
handled by the pair of lemmas above. -/
theorem isAlgebraic_coalescedSum [IsAlgebraic A] [IsAlgebraic B] :
    IsAlgebraic (CoalescedSum A B) where
  directedOn_compactsBelow z := by
    induction z using WithBot.recBotCoe with
    | bot => exact fun w₁ h₁ w₂ h₂ => ⟨⊥, bot_mem_compactsBelow ⊥, h₁.2, h₂.2⟩
    | coe q =>
      cases hq : q.val with
      | inl x => exact directedOn_compactsBelow_coe_inl hq
      | inr y => exact directedOn_compactsBelow_coe_inr hq
  isLUB_compactsBelow z := by
    induction z using WithBot.recBotCoe with
    | bot => exact ⟨fun w hw => hw.2, fun _ _ => bot_le⟩
    | coe q =>
      cases hq : q.val with
      | inl x => exact isLUB_compactsBelow_coe_inl hq
      | inr y => exact isLUB_compactsBelow_coe_inr hq

/-- `K(A ⊕ B) ⊆ {⊥} ∪ inl(K A) ∪ inr(K B)`, the inclusion countability needs.
The companion of `ClosureProperties.compacts_withBot_subset`. -/
theorem compacts_coalescedSum_subset :
    compacts (CoalescedSum A B) ⊆
      insert ⊥ ((fun k : A => (sumInl B k : CoalescedSum A B)) '' compacts A ∪
        (fun k : B => (sumInr A k : CoalescedSum A B)) '' compacts B) := by
  intro z hz
  induction z using WithBot.recBotCoe with
  | bot => exact Set.mem_insert _ _
  | coe q =>
    cases hq : q.val with
    | inl x =>
      refine Set.mem_insert_of_mem _ (Or.inl ⟨x, (isCompactElement_coe_inl_iff hq).mp hz, ?_⟩)
      show (sumInl B x : CoalescedSum A B) = ↑q
      rw [sumInl_of_ne_bot (ne_bot_of_val_eq_inl hq)]
      exact (congrArg _ (Subtype.ext hq)).symm
    | inr y =>
      refine Set.mem_insert_of_mem _ (Or.inr ⟨y, (isCompactElement_coe_inr_iff hq).mp hz, ?_⟩)
      show (sumInr A y : CoalescedSum A B) = ↑q
      rw [sumInr_of_ne_bot (ne_bot_of_val_eq_inr hq)]
      exact (congrArg _ (Subtype.ext hq)).symm

/-- **`A ⊕ B` is a domain when `A` and `B` are.** Stated as a theorem rather than
an instance, following `PowerdomainRep.domain_prod`: it is consumed at two
specific carriers, and a `Domain` instance on every coalesced sum would be
resolved on every goal mentioning one. -/
theorem domain_coalescedSum [Domain A] [Domain B] : Domain (CoalescedSum A B) :=
  { __ := isAlgebraic_coalescedSum
    countable_compacts :=
      Set.Countable.mono compacts_coalescedSum_subset
        ((((Domain.countable_compacts (α := A)).image _).union
          ((Domain.countable_compacts (α := B)).image _)).insert ⊥) }

/-! ### The three shapes of a point of `A ⊕ B`, and how `≤` reads on them

Every point of `A ⊕ B` is the adjoined bottom or the injection of a non-`⊥` point
of a summand. Writing the two injections as `sumInl` / `sumInr` — total functions
sending `⊥` to `⊥` — rather than as `↑⟨Sum.inl x, h⟩` removes the `≠ ⊥` side
condition from every definition below and leaves it only in the two order lemmas,
where it is genuinely needed: `sumInl B ⊥ = ⊥` is below everything. -/

/-- **The case analysis on `A ⊕ B`.** -/
theorem coalescedSum_cases (z : CoalescedSum A B) :
    z = ⊥ ∨ (∃ x : A, x ≠ ⊥ ∧ z = sumInl B x) ∨ (∃ y : B, y ≠ ⊥ ∧ z = sumInr A y) := by
  induction z using WithBot.recBotCoe with
  | bot => exact Or.inl rfl
  | coe q =>
    cases hq : q.val with
    | inl x =>
      refine Or.inr (Or.inl ⟨x, ne_bot_of_val_eq_inl hq, ?_⟩)
      rw [sumInl_of_ne_bot (ne_bot_of_val_eq_inl hq)]
      exact congrArg _ (Subtype.ext hq)
    | inr y =>
      refine Or.inr (Or.inr ⟨y, ne_bot_of_val_eq_inr hq, ?_⟩)
      rw [sumInr_of_ne_bot (ne_bot_of_val_eq_inr hq)]
      exact congrArg _ (Subtype.ext hq)

theorem not_sumInl_le_bot {x : A} (hx : x ≠ ⊥) : ¬ (sumInl B x ≤ (⊥ : CoalescedSum A B)) := by
  rw [sumInl_of_ne_bot hx]; exact WithBot.not_coe_le_bot _

theorem not_sumInr_le_bot {y : B} (hy : y ≠ ⊥) : ¬ (sumInr A y ≤ (⊥ : CoalescedSum A B)) := by
  rw [sumInr_of_ne_bot hy]; exact WithBot.not_coe_le_bot _

/-- `inl` reflects the order away from `⊥`. -/
theorem sumInl_le_sumInl_iff {x x' : A} (hx : x ≠ ⊥) :
    (sumInl B x ≤ sumInl B x') ↔ x ≤ x' := by
  refine ⟨fun h => ?_, fun h => monotone_sumInl h⟩
  by_cases hx' : x' = ⊥
  · rw [hx', sumInl_bot] at h
    exact absurd h (not_sumInl_le_bot hx)
  · rw [sumInl_of_ne_bot hx, sumInl_of_ne_bot hx'] at h
    exact Sum.inl_le_inl_iff.mp ((WithBot.coe_le_coe (α := NonBotSum A B)).mp h)

theorem sumInr_le_sumInr_iff {y y' : B} (hy : y ≠ ⊥) :
    (sumInr A y ≤ sumInr A y') ↔ y ≤ y' := by
  refine ⟨fun h => ?_, fun h => monotone_sumInr h⟩
  by_cases hy' : y' = ⊥
  · rw [hy', sumInr_bot] at h
    exact absurd h (not_sumInr_le_bot hy)
  · rw [sumInr_of_ne_bot hy, sumInr_of_ne_bot hy'] at h
    exact Sum.inr_le_inr_iff.mp ((WithBot.coe_le_coe (α := NonBotSum A B)).mp h)

/-- The two summands are incomparable above `⊥`: `Sum`'s order relates only
same-side points, which is what keeps the coalesced sum's directed sets on one
side. -/
theorem not_sumInl_le_sumInr {x : A} (hx : x ≠ ⊥) (y : B) :
    ¬ (sumInl B x ≤ sumInr A y) := by
  by_cases hy : y = ⊥
  · rw [hy, sumInr_bot]; exact not_sumInl_le_bot hx
  · rw [sumInl_of_ne_bot hx, sumInr_of_ne_bot hy]
    intro h
    have h2 : (Sum.inl x : A ⊕ B) ≤ Sum.inr y := (WithBot.coe_le_coe (α := NonBotSum A B)).mp h
    simp at h2

theorem not_sumInr_le_sumInl {y : B} (hy : y ≠ ⊥) (x : A) :
    ¬ (sumInr A y ≤ sumInl B x) := by
  by_cases hx : x = ⊥
  · rw [hx, sumInl_bot]; exact not_sumInr_le_bot hy
  · rw [sumInr_of_ne_bot hy, sumInl_of_ne_bot hx]
    intro h
    have h2 : (Sum.inr y : A ⊕ B) ≤ Sum.inl x := (WithBot.coe_le_coe (α := NonBotSum A B)).mp h
    simp at h2

/-- `Skeleton/Sum.lean`'s `sumInl` and `Isomorphism/Copair.lean`'s `sumInlFun`
are the same function with the `dite` branches swapped. Recorded so that the
continuity proof written for one name serves the other, which is what lets the
compactness criterion (stated at `sumInl`) and the copairing construction
(stated at `sumInlFun`) be used in the same proof. -/
theorem sumInlFun_eq_sumInl (x : A) : Isomorphism.sumInlFun (β := A) (γ := B) x = sumInl B x := by
  by_cases h : x = ⊥
  · rw [h, Isomorphism.sumInlFun_bot, sumInl_bot]
  · rw [Isomorphism.sumInlFun_of_ne h, sumInl_of_ne_bot h]

theorem sumInrFun_eq_sumInr (y : B) : Isomorphism.sumInrFun (β := A) (γ := B) y = sumInr A y := by
  by_cases h : y = ⊥
  · rw [h, Isomorphism.sumInrFun_bot, sumInr_bot]
  · rw [Isomorphism.sumInrFun_of_ne h, sumInr_of_ne_bot h]

theorem scottContinuous_sumInl : ScottContinuous (sumInl B : A → CoalescedSum A B) := by
  have h : (sumInl B : A → CoalescedSum A B) = Isomorphism.sumInlFun :=
    funext fun x => (sumInlFun_eq_sumInl x).symm
  rw [h]
  exact Isomorphism.scottContinuous_sumInlFun

theorem scottContinuous_sumInr : ScottContinuous (sumInr A : B → CoalescedSum A B) := by
  have h : (sumInr A : B → CoalescedSum A B) = Isomorphism.sumInrFun :=
    funext fun y => (sumInrFun_eq_sumInr y).symm
  rw [h]
  exact Isomorphism.scottContinuous_sumInrFun

end CoalescedSumDomain

/-! ## Conjunct 6: `⊕` is p-representable

The paper's recipe verbatim, at the coalesced sum: `R⊕(r, s) = Ψ⊕ ∘ (r ⊕ s) ∘ Φ⊕`
with `(Φ⊕, Ψ⊕)` the pair Theorem 27 supplies at `U ⊕ U`. What has to be built is
the conjugating family `r ⊕ s` and its two properties.

**This conjunct was refuted in r0034 and the refutation does not apply here.**
That round's three-chain counterexample is a statement about the *closure*
notion, where the operator has to satisfy `id ⊑ r` and therefore `⊥ ⊑ r ⊥` with
nothing forcing equality — the coalesced sum's two summands then get glued to
different points. A projection satisfies `r ⊥ ⊑ ⊥`, hence `r ⊥ = ⊥`
(`isStrict_of_isProjection`), so `r ⊕ s` is well defined by the copairing
`[inl ∘ r, inr ∘ s]` and `Isomorphism.copair` supplies its continuity. The
notion, not the operator, was the obstruction.

| # | Obligation | Discharged by |
| - | ---------- | ------------- |
| 1 | `r ⊕ s` continuous | `Isomorphism.copair`, whose whole point is this |
| 2 | `r ⊕ s` a projection | `isProjection_coalSumMap`, three cases |
| 3 | `im(r ⊕ s) ≅ im(r) ⊕ im(s)` | `coalSumRangeOrderIso` |
| 4 | `im(r ⊕ s)` a domain | `domain_coalescedSum` through 3 |
| 5 | continuity in the `Fp(U)` index | `isLUB_coalSumFamily`, spending `isFinitaryProjection_sSup` |
-/

section CoalSumConjunct

open ScottHom

variable {U : Type u} [CompletePartialOrder U]

/-- The image of a projection as a `Cpo`. At `p ∈ Fp(U)` this is `FpImage p`
definitionally; it is stated at a bare projection because the range isomorphism
below is a fact about `r` and `s`, not about their memberships.

Deliberately **not** reducible. `Cpo.str` is an instance, so instance search
resolves `CompletePartialOrder (projCpo hp).carrier` by matching the head
`Cpo.carrier ?D` — which is exactly what a reducible definition would destroy by
unfolding to the bare subtype before the match is attempted. Keeping it opaque is
what lets the coalesced sum of two images typecheck with no `letI` at all. -/
def projCpo {p : ScottHom U U} (hp : IsProjection p) : Cpo.{u} :=
  ⟨↥(Set.range ⇑p), hp.rangeCompletePartialOrder⟩

/-- **A projection is strict.** `p ⊥ ⊑ ⊥` from `p ⊑ id`. This one line is what
separates the projection notion from the closure notion for `⊕`. -/
theorem isStrict_of_isProjection {p : ScottHom U U} (hp : IsProjection p) : IsStrict p :=
  hp.map_bot

/-- A point of `im(p)` is `⊥` exactly when it is `⊥` in `U`: the bottom of the
image cpo is `⟨⊥, _⟩`, since a projection fixes `⊥`. -/
theorem val_ne_bot_of_ne_bot {p : ScottHom U U} (hp : IsProjection p)
    {a : (projCpo hp).carrier} (ha : a ≠ ⊥) : a.val ≠ ⊥ :=
  fun hb => ha (Subtype.ext hb)

/-! ### `r ⊕ s`, the conjugating family -/

/-- `x ↦ inl (r x)`, strict and continuous. -/
noncomputable def inlHom (r : ScottHom U U) (hr : IsStrict r) :
    StrictHom U (CoalescedSum U U) :=
  ⟨⟨fun x => sumInl U (r x), r.scottContinuous.comp scottContinuous_sumInl⟩,
    show sumInl U (r ⊥) = (⊥ : CoalescedSum U U) by rw [hr, sumInl_bot]⟩

/-- `y ↦ inr (s y)`, strict and continuous. -/
noncomputable def inrHom (s : ScottHom U U) (hs : IsStrict s) :
    StrictHom U (CoalescedSum U U) :=
  ⟨⟨fun y => sumInr U (s y), s.scottContinuous.comp scottContinuous_sumInr⟩,
    show sumInr U (s ⊥) = (⊥ : CoalescedSum U U) by rw [hs, sumInr_bot]⟩

/-- **`r ⊕ s`**, the copairing `[inl ∘ r, inr ∘ s]`. Strictness of `r` and `s` is
what makes the two components strict, which is what `Isomorphism.copair`
requires — and it is exactly what a projection supplies for free. -/
noncomputable def coalSumMap (r s : ScottHom U U) (hr : IsStrict r) (hs : IsStrict s) :
    ScottHom (CoalescedSum U U) (CoalescedSum U U) :=
  (Isomorphism.copair (inlHom r hr) (inrHom s hs)).val

variable {r s : ScottHom U U} {hr : IsStrict r} {hs : IsStrict s}

@[simp] theorem coalSumMap_bot : coalSumMap r s hr hs (⊥ : CoalescedSum U U) = ⊥ := rfl

theorem coalSumMap_coe (q : NonBotSum U U) :
    coalSumMap r s hr hs (↑q : CoalescedSum U U) =
      Sum.elim (fun x => sumInl U (r x)) (fun y => sumInr U (s y)) q.val := rfl

@[simp] theorem coalSumMap_sumInl (x : U) :
    coalSumMap r s hr hs (sumInl U x) = sumInl U (r x) := by
  by_cases hx : x = ⊥
  · rw [hx, sumInl_bot, coalSumMap_bot, hr, sumInl_bot]
  · rw [sumInl_of_ne_bot hx, coalSumMap_coe]
    rfl

@[simp] theorem coalSumMap_sumInr (y : U) :
    coalSumMap r s hr hs (sumInr U y) = sumInr U (s y) := by
  by_cases hy : y = ⊥
  · rw [hy, sumInr_bot, coalSumMap_bot, hs, sumInr_bot]
  · rw [sumInr_of_ne_bot hy, coalSumMap_coe]
    rfl

/-- **`r ⊕ s` is a projection when `r` and `s` are.** Both laws hold summand by
summand, with the adjoined bottom a fixed point of every case. -/
theorem isProjection_coalSumMap (hpr : IsProjection r) (hps : IsProjection s) :
    IsProjection (coalSumMap r s hpr.map_bot hps.map_bot) := by
  constructor
  · intro z
    rcases coalescedSum_cases z with rfl | ⟨x, _, rfl⟩ | ⟨y, _, rfl⟩
    · rfl
    · rw [coalSumMap_sumInl, coalSumMap_sumInl, hpr.idem]
    · rw [coalSumMap_sumInr, coalSumMap_sumInr, hps.idem]
  · intro z
    rcases coalescedSum_cases z with rfl | ⟨x, _, rfl⟩ | ⟨y, _, rfl⟩
    · exact le_rfl
    · rw [coalSumMap_sumInl]; exact monotone_sumInl (hpr.le x)
    · rw [coalSumMap_sumInr]; exact monotone_sumInr (hps.le y)

/-- `r ⊕ s` is monotone in `(r, s)`, summand by summand. -/
theorem coalSumMap_mono {r' s' : ScottHom U U} {hr' : IsStrict r'} {hs' : IsStrict s'}
    (hrr : r ≤ r') (hss : s ≤ s') :
    coalSumMap r s hr hs ≤ coalSumMap r' s' hr' hs' := by
  intro z
  rcases coalescedSum_cases z with rfl | ⟨x, _, rfl⟩ | ⟨y, _, rfl⟩
  · exact le_rfl
  · show coalSumMap r s hr hs (sumInl U x) ≤ coalSumMap r' s' hr' hs' (sumInl U x)
    rw [coalSumMap_sumInl, coalSumMap_sumInl]
    exact monotone_sumInl (hrr x)
  · show coalSumMap r s hr hs (sumInr U y) ≤ coalSumMap r' s' hr' hs' (sumInr U y)
    rw [coalSumMap_sumInr, coalSumMap_sumInr]
    exact monotone_sumInr (hss y)

/-! ### `im(r ⊕ s) ≅ im(r) ⊕ im(s)`

The map runs from `im(r) ⊕ im(s)` into `U ⊕ U`, forgetting which summand a point
came from. Writing it with `sumInl` / `sumInr` rather than with `↑⟨Sum.inl a, _⟩`
means the definition carries no proof obligation at all — the injections are total
and send `⊥` to `⊥` — and the three computation rules below hold without any
`≠ ⊥` hypothesis. -/

/-- `im(r) ⊕ im(s) → U ⊕ U`, forgetting the images. -/
noncomputable def rangeSumVal (hpr : IsProjection r) (hps : IsProjection s)
    (w : CoalescedSum (projCpo hpr).carrier (projCpo hps).carrier) : CoalescedSum U U :=
  WithBot.recBotCoe (C := fun _ => CoalescedSum U U) ⊥
    (fun t => Sum.elim (fun a : (projCpo hpr).carrier => sumInl U a.val)
      (fun b : (projCpo hps).carrier => sumInr U b.val) t.val) w

variable {hpr : IsProjection r} {hps : IsProjection s}

@[simp] theorem rangeSumVal_bot : rangeSumVal hpr hps ⊥ = (⊥ : CoalescedSum U U) := rfl

/-- The bottom of `im(p)` is `⊥` of `U`, since a projection fixes `⊥`. -/
theorem projCpo_bot_val {p : ScottHom U U} (hp : IsProjection p) :
    (⊥ : (projCpo hp).carrier).val = (⊥ : U) := rfl

@[simp] theorem rangeSumVal_sumInl (a : (projCpo hpr).carrier) :
    rangeSumVal hpr hps (sumInl _ a) = sumInl U a.val := by
  by_cases ha : a = ⊥
  · rw [ha, sumInl_bot, rangeSumVal_bot, projCpo_bot_val, sumInl_bot]
  · rw [sumInl_of_ne_bot ha]; rfl

@[simp] theorem rangeSumVal_sumInr (b : (projCpo hps).carrier) :
    rangeSumVal hpr hps (sumInr _ b) = sumInr U b.val := by
  by_cases hb : b = ⊥
  · rw [hb, sumInr_bot, rangeSumVal_bot, projCpo_bot_val, sumInr_bot]
  · rw [sumInr_of_ne_bot hb]; rfl

/-- **`rangeSumVal` lands in `im(r ⊕ s)`**, because each of its three values is a
fixed point: a projection fixes its own image, so `r a = a` for `a ∈ im(r)`. -/
theorem rangeSumVal_mem_range (w : CoalescedSum (projCpo hpr).carrier (projCpo hps).carrier) :
    rangeSumVal hpr hps w ∈ Set.range ⇑(coalSumMap r s hpr.map_bot hps.map_bot) := by
  refine ⟨rangeSumVal hpr hps w, ?_⟩
  rcases coalescedSum_cases w with rfl | ⟨a, _, rfl⟩ | ⟨b, _, rfl⟩
  · rfl
  · rw [rangeSumVal_sumInl, coalSumMap_sumInl, hpr.apply_of_mem_range a.2]
  · rw [rangeSumVal_sumInr, coalSumMap_sumInr, hps.apply_of_mem_range b.2]

/-- The map as a function into the subtype. -/
noncomputable def coalSumRangeMap (hpr : IsProjection r) (hps : IsProjection s)
    (w : CoalescedSum (projCpo hpr).carrier (projCpo hps).carrier) :
    ↥(Set.range ⇑(coalSumMap r s hpr.map_bot hps.map_bot)) :=
  ⟨rangeSumVal hpr hps w, rangeSumVal_mem_range w⟩

/-- **`rangeSumVal` preserves and reflects the order.** Nine cases, one per pair
of shapes; the six mixed ones are all closed by the incomparability of the two
summands, and the two same-side ones by `sumInl_le_sumInl_iff` applied on both
sides of the equivalence. -/
theorem coalSumRangeMap_le_iff
    (w w' : CoalescedSum (projCpo hpr).carrier (projCpo hps).carrier) :
    coalSumRangeMap hpr hps w ≤ coalSumRangeMap hpr hps w' ↔ w ≤ w' := by
  show rangeSumVal hpr hps w ≤ rangeSumVal hpr hps w' ↔ w ≤ w'
  rcases coalescedSum_cases w with rfl | ⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩
  · simp
  · have hav : a.val ≠ ⊥ := val_ne_bot_of_ne_bot hpr ha
    rcases coalescedSum_cases w' with rfl | ⟨a', _, rfl⟩ | ⟨b', _, rfl⟩
    · rw [rangeSumVal_sumInl, rangeSumVal_bot]
      exact iff_of_false (not_sumInl_le_bot hav) (not_sumInl_le_bot ha)
    · rw [rangeSumVal_sumInl, rangeSumVal_sumInl, sumInl_le_sumInl_iff hav,
        sumInl_le_sumInl_iff ha]
      exact Iff.rfl
    · rw [rangeSumVal_sumInl, rangeSumVal_sumInr]
      exact iff_of_false (not_sumInl_le_sumInr hav _) (not_sumInl_le_sumInr ha _)
  · have hbv : b.val ≠ ⊥ := val_ne_bot_of_ne_bot hps hb
    rcases coalescedSum_cases w' with rfl | ⟨a', _, rfl⟩ | ⟨b', _, rfl⟩
    · rw [rangeSumVal_sumInr, rangeSumVal_bot]
      exact iff_of_false (not_sumInr_le_bot hbv) (not_sumInr_le_bot hb)
    · rw [rangeSumVal_sumInr, rangeSumVal_sumInl]
      exact iff_of_false (not_sumInr_le_sumInl hbv _) (not_sumInr_le_sumInl hb _)
    · rw [rangeSumVal_sumInr, rangeSumVal_sumInr, sumInr_le_sumInr_iff hbv,
        sumInr_le_sumInr_iff hb]
      exact Iff.rfl

/-- **`rangeSumVal` is onto `im(r ⊕ s)`.** Every value of `r ⊕ s` is `⊥`,
`inl (r x)` or `inr (s y)`, and each is the image of the corresponding point of
`im(r) ⊕ im(s)`. -/
theorem coalSumRangeMap_surjective : Function.Surjective (coalSumRangeMap hpr hps) := by
  rintro ⟨_, y, rfl⟩
  rcases coalescedSum_cases y with rfl | ⟨x, _, rfl⟩ | ⟨z, _, rfl⟩
  · exact ⟨⊥, rfl⟩
  · refine ⟨sumInl (projCpo hps).carrier
      (⟨r x, Set.mem_range_self x⟩ : (projCpo hpr).carrier), Subtype.ext ?_⟩
    show rangeSumVal hpr hps (sumInl _ _) = coalSumMap r s hpr.map_bot hps.map_bot (sumInl U x)
    rw [rangeSumVal_sumInl, coalSumMap_sumInl]
  · refine ⟨sumInr (projCpo hpr).carrier
      (⟨s z, Set.mem_range_self z⟩ : (projCpo hps).carrier), Subtype.ext ?_⟩
    show rangeSumVal hpr hps (sumInr _ _) = coalSumMap r s hpr.map_bot hps.map_bot (sumInr U z)
    rw [rangeSumVal_sumInr, coalSumMap_sumInr]

/-- **`im(r ⊕ s) ≅ im(r) ⊕ im(s)`** — Lemma 28's `⊕` conjunct at the level of a
single pair of projections, and the third obligation of the representation
scheme. -/
noncomputable def coalSumRangeOrderIso (hpr : IsProjection r) (hps : IsProjection s) :
    ↥(Set.range ⇑(coalSumMap r s hpr.map_bot hps.map_bot)) ≃o
      CoalescedSum (projCpo hpr).carrier (projCpo hps).carrier :=
  (RelIso.ofSurjective
    (OrderEmbedding.ofMapLEIff (coalSumRangeMap hpr hps) (coalSumRangeMap_le_iff))
    coalSumRangeMap_surjective).symm

/-- **`im(r ⊕ s)` is a domain when `im(r)` and `im(s)` are** — the obligation `Fp`
adds and `Fc` does not. Through `coalSumRangeOrderIso` it reduces to
`domain_coalescedSum`. -/
theorem domain_range_coalSumMap (hpr : IsProjection r) (hps : IsProjection s)
    (hdr : @Domain _ (IsProjection.rangeCompletePartialOrder hpr))
    (hds : @Domain _ (IsProjection.rangeCompletePartialOrder hps)) :
    @Domain _ (IsProjection.rangeCompletePartialOrder (isProjection_coalSumMap hpr hps)) := by
  haveI : Domain (projCpo hpr).carrier := hdr
  haveI : Domain (projCpo hps).carrier := hds
  haveI : Domain (CoalescedSum (projCpo hpr).carrier (projCpo hps).carrier) :=
    domain_coalescedSum
  letI : CompletePartialOrder ↥(Set.range ⇑(coalSumMap r s hpr.map_bot hps.map_bot)) :=
    IsProjection.rangeCompletePartialOrder (isProjection_coalSumMap hpr hps)
  exact domain_orderIso (coalSumRangeOrderIso hpr hps).symm

/-! ### The family, indexed by `Fp(U) × Fp(U)` -/

/-- The conjugating family for `⊕`. -/
noncomputable def coalSumFamily (q : ↥(Fp U) × ↥(Fp U)) :
    ScottHom (CoalescedSum U U) (CoalescedSum U U) :=
  coalSumMap q.1.val q.2.val (mem_Fp.mp q.1.2).isProjection.map_bot
    (mem_Fp.mp q.2.2).isProjection.map_bot

theorem isProjection_coalSumFamily (q : ↥(Fp U) × ↥(Fp U)) : IsProjection (coalSumFamily q) :=
  isProjection_coalSumMap (mem_Fp.mp q.1.2).isProjection (mem_Fp.mp q.2.2).isProjection

theorem coalSumFamily_mono {q q' : ↥(Fp U) × ↥(Fp U)} (h : q ≤ q') :
    coalSumFamily q ≤ coalSumFamily q' := coalSumMap_mono h.1 h.2

/-- Pointwise Scott continuity of the family in its `Fp(U) × Fp(U)` index. The
adjoined bottom is constant; each summand is `isLUB_val_image_of_isLUB_fp'`
followed by `ScottHom.isLUB_eval_image_of_isLUB` and then Scott continuity of the
injection. This is where `isFinitaryProjection_sSup` is spent. -/
theorem isLUB_coalSumFamily [Domain U] {d : Set (↥(Fp U) × ↥(Fp U))}
    (hne : d.Nonempty) (hd : DirectedOn (· ≤ ·) d) {a : ↥(Fp U) × ↥(Fp U)}
    (ha : IsLUB d a) (z : CoalescedSum U U) :
    IsLUB ((fun q => coalSumFamily q z) '' d) (coalSumFamily a z) := by
  have hdfst : DirectedOn (· ≤ ·) (Prod.fst '' d) := by
    rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩
    obtain ⟨c, hc, hpc, hqc⟩ := hd p hp q hq
    exact ⟨c.1, ⟨c, hc, rfl⟩, hpc.1, hqc.1⟩
  have hdsnd : DirectedOn (· ≤ ·) (Prod.snd '' d) := by
    rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩
    obtain ⟨c, hc, hpc, hqc⟩ := hd p hp q hq
    exact ⟨c.2, ⟨c, hc, rfl⟩, hpc.2, hqc.2⟩
  have h₁ : IsLUB ((fun q : ↥(Fp U) × ↥(Fp U) => q.1.val) '' d) a.1.val := by
    have := isLUB_val_image_of_isLUB_fp' (hne.image _) hdfst (isLUB_prod.mp ha).1
    rwa [Set.image_image] at this
  have h₂ : IsLUB ((fun q : ↥(Fp U) × ↥(Fp U) => q.2.val) '' d) a.2.val := by
    have := isLUB_val_image_of_isLUB_fp' (hne.image _) hdsnd (isLUB_prod.mp ha).2
    rwa [Set.image_image] at this
  have hd₁ : DirectedOn (· ≤ ·) ((fun q : ↥(Fp U) × ↥(Fp U) => q.1.val) '' d) := by
    rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩
    obtain ⟨c, hc, hpc, hqc⟩ := hd p hp q hq
    exact ⟨c.1.val, ⟨c, hc, rfl⟩, hpc.1, hqc.1⟩
  have hd₂ : DirectedOn (· ≤ ·) ((fun q : ↥(Fp U) × ↥(Fp U) => q.2.val) '' d) := by
    rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩
    obtain ⟨c, hc, hpc, hqc⟩ := hd p hp q hq
    exact ⟨c.2.val, ⟨c, hc, rfl⟩, hpc.2, hqc.2⟩
  rcases coalescedSum_cases z with rfl | ⟨x, _, rfl⟩ | ⟨y, _, rfl⟩
  · refine ⟨?_, fun u _ => ?_⟩
    · rintro _ ⟨q, _, rfl⟩; exact le_rfl
    · exact bot_le
  · have hev := ScottHom.isLUB_eval_image_of_isLUB hd₁ h₁ x
    rw [Set.image_image] at hev
    have hdx : DirectedOn (· ≤ ·) ((fun q : ↥(Fp U) × ↥(Fp U) => q.1.val x) '' d) := by
      rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩
      obtain ⟨c, hc, hpc, hqc⟩ := hd p hp q hq
      exact ⟨c.1.val x, ⟨c, hc, rfl⟩, hpc.1 x, hqc.1 x⟩
    have := scottContinuous_sumInl (A := U) (B := U) (hne.image _) hdx hev
    rw [Set.image_image] at this
    simpa [coalSumFamily] using this
  · have hev := ScottHom.isLUB_eval_image_of_isLUB hd₂ h₂ y
    rw [Set.image_image] at hev
    have hdy : DirectedOn (· ≤ ·) ((fun q : ↥(Fp U) × ↥(Fp U) => q.2.val y) '' d) := by
      rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩
      obtain ⟨c, hc, hpc, hqc⟩ := hd p hp q hq
      exact ⟨c.2.val y, ⟨c, hc, rfl⟩, hpc.2 y, hqc.2 y⟩
    have := scottContinuous_sumInr (A := U) (B := U) (hne.image _) hdy hev
    rw [Set.image_image] at this
    simpa [coalSumFamily] using this

/-- **`⊕` is p-representable over any domain that retracts onto its own coalesced
square** — conjunct 6 of Lemma 28, at the notion §7.3 uses. -/
theorem rep_coalSum [Domain U] {fn : ScottHom U (CoalescedSum U U)}
    {gr : ScottHom (CoalescedSum U U) U}
    (hfg : ∀ y, fn (gr y) = y) (hgf : ∀ x, gr (fn x) ≤ x) :
    IsPRepresentable₂ U coalSumOp :=
  isPRepresentable₂_of_repFamily hfg
    (fun q => isFinitaryProjection_repOf hfg hgf (isProjection_coalSumFamily q)
      (domain_range_coalSumMap _ _ (mem_Fp.mp q.1.2).domain (mem_Fp.mp q.2.2).domain))
    coalSumFamily_mono isLUB_coalSumFamily
    fun q => ⟨coalSumRangeOrderIso (mem_Fp.mp q.1.2).isProjection
      (mem_Fp.mp q.2.2).isProjection⟩

end CoalSumConjunct

/-! ## The coalesced sum respects `≅`

Lemma 28's `+` conjunct *is* its `⊕` conjunct at the lifted maps, because §4.4
defines `D + E = D⊥ ⊕ E⊥` — an equation between cpos, which is why
`ClosureProperties.SeparatedSum` is an `abbrev`. Composing the two range
isomorphisms needs the coalesced sum to carry an isomorphism of its summands,
which it does: an order isomorphism preserves the least element, so it carries
the punctured copy to the punctured copy and the adjoined bottom to the adjoined
bottom.

The four cpos are **explicit** arguments. `A.carrier` is a projection applied to
its argument, so Lean cannot recover `A` from the type of `e : A.carrier ≃o
A'.carrier`; passing the cpos by hand is what keeps the instances on the
subtypes — which are never found by instance search — pinned to the ones the
statement means. -/

section CoalSumCongr

/-- An order isomorphism preserves `⊥`: `⊥` is the least element on both sides
and an order isomorphism is a surjection preserving `≤` both ways. -/
theorem orderIso_apply_bot (A A' : Cpo.{u}) (e : A.carrier ≃o A'.carrier) :
    e ⊥ = (⊥ : A'.carrier) :=
  le_antisymm
    (by
      have h : e ⊥ ≤ e (e.symm ⊥) := e.le_iff_le.mpr (bot_le : (⊥ : A.carrier) ≤ e.symm ⊥)
      rwa [e.apply_symm_apply] at h)
    bot_le

theorem orderIso_apply_ne_bot (A A' : Cpo.{u}) (e : A.carrier ≃o A'.carrier)
    {x : A.carrier} (hx : x ≠ ⊥) : e x ≠ ⊥ :=
  fun h => hx (e.injective (h.trans (orderIso_apply_bot A A' e).symm))

/-- `e ⊕ f`, on the underlying function. -/
noncomputable def coalSumCongrFun (A A' B B' : Cpo.{u})
    (e : A.carrier ≃o A'.carrier) (f : B.carrier ≃o B'.carrier)
    (w : CoalescedSum A.carrier B.carrier) : CoalescedSum A'.carrier B'.carrier :=
  WithBot.recBotCoe (C := fun _ => CoalescedSum A'.carrier B'.carrier) ⊥
    (fun t => Sum.elim (fun a : A.carrier => sumInl B'.carrier (e a))
      (fun b : B.carrier => sumInr A'.carrier (f b)) t.val) w

@[simp] theorem coalSumCongrFun_bot (A A' B B' : Cpo.{u})
    (e : A.carrier ≃o A'.carrier) (f : B.carrier ≃o B'.carrier) :
    coalSumCongrFun A A' B B' e f ⊥ = ⊥ := rfl

@[simp] theorem coalSumCongrFun_sumInl (A A' B B' : Cpo.{u})
    (e : A.carrier ≃o A'.carrier) (f : B.carrier ≃o B'.carrier) (x : A.carrier) :
    coalSumCongrFun A A' B B' e f (sumInl B.carrier x) = sumInl B'.carrier (e x) := by
  by_cases hx : x = ⊥
  · rw [hx, sumInl_bot, coalSumCongrFun_bot, orderIso_apply_bot, sumInl_bot]
  · rw [sumInl_of_ne_bot hx]; rfl

@[simp] theorem coalSumCongrFun_sumInr (A A' B B' : Cpo.{u})
    (e : A.carrier ≃o A'.carrier) (f : B.carrier ≃o B'.carrier) (y : B.carrier) :
    coalSumCongrFun A A' B B' e f (sumInr A.carrier y) = sumInr A'.carrier (f y) := by
  by_cases hy : y = ⊥
  · rw [hy, sumInr_bot, coalSumCongrFun_bot, orderIso_apply_bot, sumInr_bot]
  · rw [sumInr_of_ne_bot hy]; rfl

theorem coalSumCongrFun_le_iff (A A' B B' : Cpo.{u})
    (e : A.carrier ≃o A'.carrier) (f : B.carrier ≃o B'.carrier)
    (w w' : CoalescedSum A.carrier B.carrier) :
    coalSumCongrFun A A' B B' e f w ≤ coalSumCongrFun A A' B B' e f w' ↔ w ≤ w' := by
  rcases coalescedSum_cases w with rfl | ⟨x, hx, rfl⟩ | ⟨y, hy, rfl⟩
  · simp
  · have hex : e x ≠ ⊥ := orderIso_apply_ne_bot A A' e hx
    rcases coalescedSum_cases w' with rfl | ⟨x', _, rfl⟩ | ⟨y', _, rfl⟩
    · rw [coalSumCongrFun_sumInl, coalSumCongrFun_bot]
      exact iff_of_false (not_sumInl_le_bot hex) (not_sumInl_le_bot hx)
    · rw [coalSumCongrFun_sumInl, coalSumCongrFun_sumInl, sumInl_le_sumInl_iff hex,
        sumInl_le_sumInl_iff hx]
      exact e.le_iff_le
    · rw [coalSumCongrFun_sumInl, coalSumCongrFun_sumInr]
      exact iff_of_false (not_sumInl_le_sumInr hex _) (not_sumInl_le_sumInr hx _)
  · have hfy : f y ≠ ⊥ := orderIso_apply_ne_bot B B' f hy
    rcases coalescedSum_cases w' with rfl | ⟨x', _, rfl⟩ | ⟨y', _, rfl⟩
    · rw [coalSumCongrFun_sumInr, coalSumCongrFun_bot]
      exact iff_of_false (not_sumInr_le_bot hfy) (not_sumInr_le_bot hy)
    · rw [coalSumCongrFun_sumInr, coalSumCongrFun_sumInl]
      exact iff_of_false (not_sumInr_le_sumInl hfy _) (not_sumInr_le_sumInl hy _)
    · rw [coalSumCongrFun_sumInr, coalSumCongrFun_sumInr, sumInr_le_sumInr_iff hfy,
        sumInr_le_sumInr_iff hy]
      exact f.le_iff_le

/-- **`A ≅ A'` and `B ≅ B'` give `A ⊕ B ≅ A' ⊕ B'`.** The inverse is the
congruence of the inverses; both round trips are the three cases of
`coalescedSum_cases` with `OrderIso.symm_apply_apply`. -/
noncomputable def coalSumCongr (A A' B B' : Cpo.{u})
    (e : A.carrier ≃o A'.carrier) (f : B.carrier ≃o B'.carrier) :
    CoalescedSum A.carrier B.carrier ≃o CoalescedSum A'.carrier B'.carrier where
  toFun := coalSumCongrFun A A' B B' e f
  invFun := coalSumCongrFun A' A B' B e.symm f.symm
  left_inv w := by
    rcases coalescedSum_cases w with rfl | ⟨x, _, rfl⟩ | ⟨y, _, rfl⟩ <;> simp
  right_inv w := by
    rcases coalescedSum_cases w with rfl | ⟨x, _, rfl⟩ | ⟨y, _, rfl⟩ <;> simp
  map_rel_iff' := coalSumCongrFun_le_iff A A' B B' e f _ _

end CoalSumCongr

/-! ## Conjunct 5: `+` is p-representable

Nothing here is a new construction. §4.4's `D + E = D⊥ ⊕ E⊥` makes the
conjugating family for `+` the conjugating family for `⊕` at the lifted maps —
`r + s = r⊥ ⊕ s⊥` — and each of the four obligations is then a composition of a
`⊕` fact with a `(·)⊥` fact already proved:

| # | Obligation | `⊕` half | `(·)⊥` half |
| - | ---------- | -------- | ----------- |
| 1 | projection | `isProjection_coalSumMap` | `PRep.isProjection_liftMap` |
| 2 | monotone in `(r, s)` | `coalSumMap_mono` | `PRep.liftFamily_mono` |
| 3 | `im` a domain | `domain_range_coalSumMap` | `PRep.domain_range_liftMap` |
| 4 | the range isomorphism | `coalSumRangeOrderIso` then `coalSumCongr` | `PRep.liftRangeOrderIso` |
| 5 | index continuity | `scottContinuous_sumInl` | `PRep.isLUB_liftFamily` |

This is the measurement the plan predicted: `+` is the cheapest of the four
because the paper's definition of it *is* a composition, and
`ClosureProperties.lem10_separated` obtained `+` for Lemma 10 the same way. -/

section SepSumConjunct

open ScottHom ClosureProperties

variable {U : Type u} [CompletePartialOrder U]

/-- **`r + s = r⊥ ⊕ s⊥`**, the conjugating family for `+`. -/
noncomputable def sepSumFamily (q : ↥(Fp U) × ↥(Fp U)) :
    ScottHom (SeparatedSum U U) (SeparatedSum U U) :=
  coalSumMap (liftFamily q.1) (liftFamily q.2)
    (isProjection_liftFamily q.1).map_bot (isProjection_liftFamily q.2).map_bot

theorem isProjection_sepSumFamily (q : ↥(Fp U) × ↥(Fp U)) : IsProjection (sepSumFamily q) :=
  isProjection_coalSumMap (isProjection_liftFamily q.1) (isProjection_liftFamily q.2)

theorem sepSumFamily_mono {q q' : ↥(Fp U) × ↥(Fp U)} (h : q ≤ q') :
    sepSumFamily q ≤ sepSumFamily q' :=
  coalSumMap_mono (liftFamily_mono h.1) (liftFamily_mono h.2)

/-- **`im(r + s) ≅ im(r) + im(s)`**: the coalesced-sum range isomorphism at the
lifted maps, followed by the congruence along `im(r⊥) ≅ (im r)⊥`. -/
noncomputable def sepSumRangeOrderIso (q : ↥(Fp U) × ↥(Fp U)) :
    ↥(Set.range ⇑(sepSumFamily q)) ≃o (sepSumOp (FpImage q.1) (FpImage q.2)).carrier :=
  (coalSumRangeOrderIso (isProjection_liftFamily q.1) (isProjection_liftFamily q.2)).trans
    (coalSumCongr (projCpo (isProjection_liftFamily q.1)) (liftOp (FpImage q.1))
      (projCpo (isProjection_liftFamily q.2)) (liftOp (FpImage q.2))
      (liftRangeOrderIso q.1.val) (liftRangeOrderIso q.2.val))

/-- **`im(r + s)` is a domain**: `domain_range_coalSumMap` at the lifted maps,
whose two hypotheses are `PRep.domain_range_liftMap`. -/
theorem domain_range_sepSumFamily (q : ↥(Fp U) × ↥(Fp U)) :
    @Domain _ (IsProjection.rangeCompletePartialOrder (isProjection_sepSumFamily q)) :=
  domain_range_coalSumMap (isProjection_liftFamily q.1) (isProjection_liftFamily q.2)
    (domain_range_liftMap (mem_Fp.mp q.1.2).isProjection (mem_Fp.mp q.1.2).domain)
    (domain_range_liftMap (mem_Fp.mp q.2.2).isProjection (mem_Fp.mp q.2.2).domain)

/-- Pointwise Scott continuity of `r + s` in its `Fp(U) × Fp(U)` index. The
adjoined bottom is constant; each summand is `PRep.isLUB_liftFamily` — which is
where `isFinitaryProjection_sSup` is spent — followed by Scott continuity of the
injection. -/
theorem isLUB_sepSumFamily [Domain U] {d : Set (↥(Fp U) × ↥(Fp U))}
    (hne : d.Nonempty) (hd : DirectedOn (· ≤ ·) d) {a : ↥(Fp U) × ↥(Fp U)}
    (ha : IsLUB d a) (z : SeparatedSum U U) :
    IsLUB ((fun q => sepSumFamily q z) '' d) (sepSumFamily a z) := by
  have hdfst : DirectedOn (· ≤ ·) (Prod.fst '' d) := by
    rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩
    obtain ⟨c, hc, hpc, hqc⟩ := hd p hp q hq
    exact ⟨c.1, ⟨c, hc, rfl⟩, hpc.1, hqc.1⟩
  have hdsnd : DirectedOn (· ≤ ·) (Prod.snd '' d) := by
    rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩
    obtain ⟨c, hc, hpc, hqc⟩ := hd p hp q hq
    exact ⟨c.2, ⟨c, hc, rfl⟩, hpc.2, hqc.2⟩
  rcases coalescedSum_cases z with rfl | ⟨x, _, rfl⟩ | ⟨y, _, rfl⟩
  · refine ⟨?_, fun u _ => ?_⟩
    · rintro _ ⟨q, _, rfl⟩; exact le_rfl
    · exact bot_le
  · have h₁ := isLUB_liftFamily (hne.image _) hdfst (isLUB_prod.mp ha).1 x
    rw [Set.image_image] at h₁
    have hdx : DirectedOn (· ≤ ·)
        ((fun q : ↥(Fp U) × ↥(Fp U) => liftFamily q.1 x) '' d) := by
      rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩
      obtain ⟨c, hc, hpc, hqc⟩ := hd p hp q hq
      exact ⟨liftFamily c.1 x, ⟨c, hc, rfl⟩, liftFamily_mono hpc.1 x, liftFamily_mono hqc.1 x⟩
    have hcont := scottContinuous_sumInl (A := WithBot U) (B := WithBot U)
      (hne.image _) hdx h₁
    rw [Set.image_image] at hcont
    simpa [sepSumFamily] using hcont
  · have h₂ := isLUB_liftFamily (hne.image _) hdsnd (isLUB_prod.mp ha).2 y
    rw [Set.image_image] at h₂
    have hdy : DirectedOn (· ≤ ·)
        ((fun q : ↥(Fp U) × ↥(Fp U) => liftFamily q.2 y) '' d) := by
      rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩
      obtain ⟨c, hc, hpc, hqc⟩ := hd p hp q hq
      exact ⟨liftFamily c.2 y, ⟨c, hc, rfl⟩, liftFamily_mono hpc.2 y, liftFamily_mono hqc.2 y⟩
    have hcont := scottContinuous_sumInr (A := WithBot U) (B := WithBot U)
      (hne.image _) hdy h₂
    rw [Set.image_image] at hcont
    simpa [sepSumFamily] using hcont

/-- **`+` is p-representable over any domain that retracts onto its own separated
square** — conjunct 5 of Lemma 28, at the notion §7.3 uses. -/
theorem rep_sepSum [Domain U] {fn : ScottHom U (SeparatedSum U U)}
    {gr : ScottHom (SeparatedSum U U) U}
    (hfg : ∀ y, fn (gr y) = y) (hgf : ∀ x, gr (fn x) ≤ x) :
    IsPRepresentable₂ U sepSumOp :=
  isPRepresentable₂_of_repFamily hfg
    (fun q => isFinitaryProjection_repOf hfg hgf (isProjection_sepSumFamily q)
      (domain_range_sepSumFamily q))
    sepSumFamily_mono isLUB_sepSumFamily
    fun q => ⟨sepSumRangeOrderIso q⟩

end SepSumConjunct

/-! ## Lemma 28 at `U`, from what remains -/

/-- **`⊕` is p-representable over `U`** — conjunct 6 of Lemma 28, at the paper's
own carrier and with no hypothesis. `U ⊕ U` is a bounded complete domain by
`domain_coalescedSum` and Lemma 10's sixth conjunct, so Theorem 27 supplies the
pair `(Φ⊕, Ψ⊕)`. -/
theorem repCoalSumAtU : IsPRepresentable₂ Dyadic.U coalSumOp := by
  haveI : Domain (CoalescedSum Dyadic.U Dyadic.U) := domain_coalescedSum
  haveI : BoundedComplete (CoalescedSum Dyadic.U Dyadic.U) := lem10_sum
  obtain ⟨_fn, _gr, hfg, hgf⟩ := pairAtU (CoalescedSum Dyadic.U Dyadic.U)
  exact rep_coalSum hfg hgf

/-- **`+` is p-representable over `U`** — conjunct 5 of Lemma 28, at the paper's
own carrier and with no hypothesis. `U + U = U⊥ ⊕ U⊥` is a bounded complete
domain: `ClosureProperties.liftDomain` and `domain_coalescedSum` for the domain
half, Lemma 10's fifth conjunct (`lem10_separated`) for bounded completeness. -/
theorem repSepSumAtU : IsPRepresentable₂ Dyadic.U sepSumOp := by
  haveI : Domain (ClosureProperties.SeparatedSum Dyadic.U Dyadic.U) := domain_coalescedSum
  haveI : BoundedComplete (ClosureProperties.SeparatedSum Dyadic.U Dyadic.U) :=
    ClosureProperties.lem10_separated
  obtain ⟨_fn, _gr, hfg, hgf⟩ := pairAtU (ClosureProperties.SeparatedSum Dyadic.U Dyadic.U)
  exact rep_sepSum hfg hgf

/-- **`Lemma28AtU` from the conjuncts still open.** `PRep.lemma28_of` with the
proved conjuncts substituted at `U`. The arity is the measurement: one hypothesis
per conjunct not yet proved, and the kernel checks that the nine slots of
`PRep.Lemma28` are all filled.

This is the statement the paper asserts — representability over `U`, not over an
abstract carrier assumed to satisfy an interface. -/
theorem lemma_28_atU_of
    (h_arrow : IsPRepresentable₂ Dyadic.U funOp)
    (h_strictArrow : IsPRepresentable₂ Dyadic.U strictFunOp)
    (h_smash : IsPRepresentable₂ Dyadic.U smashOp)
    (h_smyth : IsPRepresentable Dyadic.U smythOp)
    (h_hoare : IsPRepresentable Dyadic.U hoareOp) :
    Lemma28AtU :=
  lemma28_of h_arrow h_strictArrow repProdAtU h_smash repSepSumAtU repCoalSumAtU
    repLiftAtU h_smyth h_hoare

alias lemma28AtU_of := lemma_28_atU_of

end ScottDomains.PRepSum
