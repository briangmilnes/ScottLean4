import ScottDomains.PRep
import ScottDomains.Atomless

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
| 2 | `repProdAtU` | `IsPRepresentable₂ Dyadic.U prodOp` — **no hypothesis** |
| 3 | `repLiftAtU` | `IsPRepresentable Dyadic.U liftOp` — **no hypothesis** |
| 4 | `lemma28AtU_of` | `Lemma28AtU` from the seven conjuncts still open |

`lemma28AtU_of` is the deliverable the conjunct work feeds: its arity is the
count of what remains, and it drops by one each time a conjunct is proved.

## No conjunct is stubbed

There is no `sorry` in this file. A conjunct not proved is a hypothesis of
`lemma28AtU_of` and is named in the table above; it is never a hole in a claimed
proof.
-/

namespace ScottDomains.PRepSum

open ScottDomains ScottDomains.BifiniteUniversal ScottDomains.PRep

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

end CoalescedSumDomain

/-! ## Lemma 28 at `U`, from what remains -/

/-- **`Lemma28AtU` from the conjuncts still open.** `PRep.lemma28_of` with the
proved conjuncts substituted at `U`. The arity is the measurement: one hypothesis
per conjunct not yet proved, and the kernel checks that the nine slots of
`PRep.Lemma28` are all filled.

This is the statement the paper asserts — representability over `U`, not over an
abstract carrier assumed to satisfy an interface. -/
theorem lemma28AtU_of
    (h_arrow : IsPRepresentable₂ Dyadic.U funOp)
    (h_strictArrow : IsPRepresentable₂ Dyadic.U strictFunOp)
    (h_smash : IsPRepresentable₂ Dyadic.U smashOp)
    (h_sepSum : IsPRepresentable₂ Dyadic.U sepSumOp)
    (h_coalSum : IsPRepresentable₂ Dyadic.U coalSumOp)
    (h_smyth : IsPRepresentable Dyadic.U smythOp)
    (h_hoare : IsPRepresentable Dyadic.U hoareOp) :
    Lemma28AtU :=
  lemma28_of h_arrow h_strictArrow repProdAtU h_smash h_sepSum h_coalSum
    repLiftAtU h_smyth h_hoare

end ScottDomains.PRepSum
