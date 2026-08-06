---
round: r0012
from: orchestrator
to: orchestrator
subject: normal-subposets
date: 2026-0806-14:40
status: done
related:
  - reports/r0011-report-from-orchestrator-to-user-countable-basis.md
---

# r0012 — Normal subposets, Lemma 4, and embedding–projection pairs

§3.1's definitions, quoted from the source:

> **Definition:** Let `A` be a poset and suppose `N ⊆ A`. Then `N` is said to be
> **normal** in `A` (and we write `N ◁ A`) if, for every `x ∈ A`, the set
> `N ∩ ↓x` is directed.

> **Lemma 4** Let `C` be a poset with a least element and suppose `A` and `B` are
> subsets of `C`.
> 1. If `A ◁ B ◁ C` then `A ◁ C`.
> 2. If `A ⊆ B ⊆ C` and `A ◁ C` then `A ◁ B`.
> 3. If `A ◁ C`, then `⊥ ∈ A`.
> 4. `⟨P(C), ◁⟩` is a cpo with `{⊥}` as its least element.

> A pair of continuous functions `g : D → E` and `f : E → D` is said to be an
> **embedding–projection pair** if `f ∘ g = id_D` and `g ∘ f ⊑ id_E`.

Deliverables: `ScottDomains/NormalSubposet.lean` (the relation and Lemma 4) and
`ScottDomains/Projection.lean` (embedding–projection pairs and projections).

## Nonemptiness, again

Part 3 is **false** if `directed` is read as Mathlib's `DirectedOn`, which holds
vacuously on `∅`: the empty set would be normal in everything and would not
contain `⊥`. The paper's *directed* requires an upper bound in the set for every
finite subset, including `∅`, hence nonemptiness — the same reading `WayBelow.lean`
fixed in r0003. `IsNormalIn` therefore carries `(N ∩ ↓x).Nonempty` explicitly
alongside `DirectedOn`, and part 3 is exactly what would fail without it.

## Part 4 without a subtype

"`⟨P(C), ◁⟩` is a cpo" is stated here as the three facts that constitute it,
about sets and `◁` directly, rather than by constructing a `CompletePartialOrder`
instance on a subtype of `Set α`:

* `◁` is reflexive on normal subposets, transitive (part 1), and antisymmetric;
* a `◁`-directed family has `⋃` as its `◁`-least upper bound;
* `{⊥}` is `◁`-below every normal subposet.

This is the same content with none of the `SupSet`-totality plumbing that
`ScottHom` needed, and it is what Lemma 5 and Theorem 6 will actually cite.

## Steps

| # | Step | Verify |
| -- | ---- | ------ |
| 1 | `def IsNormalIn (N A : Set α)`, scoped notation `N ◁ A` | elaborates; `◁` is free (Mathlib's is scoped to `CategoryTheory`) |
| 2 | Lemma 4.1 `IsNormalIn.trans` | merge in `B ∩ ↓x`, then in `A ∩ ↓b` |
| 3 | Lemma 4.2 `IsNormalIn.mono_right` | immediate: `x ∈ B ⊆ C` |
| 4 | Lemma 4.3 `IsNormalIn.bot_mem` | `x := ⊥`; nonemptiness gives `y ≤ ⊥`, so `y = ⊥` |
| 5 | `IsNormalIn.refl`, `IsNormalIn.antisymm` | `x` is its own upper bound; double inclusion |
| 6 | Lemma 4.4: `⋃` is normal in `C`, is a `◁`-upper bound, and is `◁`-least | directedness of the family supplies a common member |
| 7 | Lemma 4.4: `{⊥} ◁ N` for every normal `N` | part 3 plus `bot_le` |
| 8 | `def IsEmbeddingProjectionPair`, `def IsProjection`, pointwise | elaborate |
| 9 | The paper's "a projection is a surjection and an embedding is an injection" | two lines each from the two equations |
| 10 | `lake build`, `#print axioms`, docs, PDF, commit | 0 errors, 0 warnings, 0 `sorry` |

## Acceptance criteria

| # | Criterion | Measurement |
| -- | --------- | ----------- |
| 1 | Builds | 0 errors, 0 warnings |
| 2 | Nothing unproved | 0 `sorry`, no `sorryAx` |
| 3 | **Lemma 4 complete** | all four parts, the fourth as the three facts above |
| 4 | Definitions count | normal subposet and embedding–projection pair move `✗ → ✓`; 6 of ≈13 |

## Out of scope

Finitary projections, which require `im(p)` to carry a `Domain` structure — a
sub-cpo construction on a subtype, and a round of its own. Lemma 5 and Theorem 6
depend on it.
