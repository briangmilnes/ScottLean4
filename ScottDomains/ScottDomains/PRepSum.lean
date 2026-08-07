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

/-! ## Lemma 28 at `U`, from what remains -/

/-- **`Lemma28AtU` from the conjuncts still open.** `PRep.lemma28_of` with the
two proved conjuncts substituted at `U`. The arity is the measurement: seven
hypotheses, one per conjunct not yet proved, and the kernel checks that the nine
slots of `PRep.Lemma28` are all filled.

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
