---
round: r0012
from: orchestrator
to: user
subject: normal-subposets
date: 2026-0806-14:45
started: 2026-0806-14:40
finished: 2026-0806-14:45
related:
  - plans/r0012-plan-from-orchestrator-to-orchestrator-normal-subposets.md
  - reports/r0011-report-from-orchestrator-to-user-countable-basis.md
---

# r0012 — Normal subposets, Lemma 4, embedding–projection pairs

**Lemma 4 is proved — the second of the 28 numbered results.** Two new modules,
`ScottDomains/NormalSubposet.lean` and `ScottDomains/Projection.lean`, 0 `sorry`,
0 warnings. Elapsed 5 minutes.

| # | Criterion | Measurement |
| -- | --------- | ----------- |
| 1 | Builds | 0 errors, 0 warnings |
| 2 | Nothing unproved | 0 `sorry`, no `sorryAx` |
| 3 | Lemma 4 complete | all four parts |
| 4 | Definitions | normal subposet and embedding–projection pair move `✗ → ✓`; **6 of ≈13** |

## The nonemptiness reading decides Lemma 4.3

> 3. If `A ◁ C`, then `⊥ ∈ A`.

This is **false** if "directed" is read as Mathlib's `DirectedOn`, which holds
vacuously on `∅`: the empty set would be normal in everything and would not
contain `⊥`. The paper's *directed* asks every finite subset — including `∅` —
for an upper bound *in the set*, hence nonemptiness. `IsNormalIn` carries that
conjunct explicitly, and part 3 then falls out: take `x := ⊥`, get `y ∈ A` with
`y ≤ ⊥`, and `le_bot_iff` makes it `⊥`.

This is the third time this reading has decided a statement — `bot_wayBelow`
(r0003), `compactsBelow_nonempty` (r0004), and now Lemma 4.3. The convention
chosen in r0003 has paid for itself each time.

## Part 4 without a subtype

"`⟨P(C), ◁⟩` is a cpo with `{⊥}` as its least element" is recorded as the four
facts that constitute it, stated about sets and `◁` directly:

| # | Fact | Lean |
| -- | ---- | ---- |
| 1 | `◁` is a partial order on normal subposets | `IsNormalIn.refl`, `.trans` (part 1), `.antisymm` |
| 2 | a `◁`-directed family's union is normal | `isNormalIn_sUnion` |
| 3 | the union is a `◁`-upper bound | `isNormalIn_sUnion_of_mem` |
| 4 | the union is `◁`-least | `isNormalIn_sUnion_le` |
| 5 | `{⊥}` is `◁`-least | `singleton_bot_isNormalIn_of_isNormalIn` |

Building a `CompletePartialOrder` instance on a subtype of `Set α` would have
required the same `SupSet`-totality plumbing `ScottHom` needed, for no gain:
these are the forms Lemma 5 and Theorem 6 will cite.

The linter again sharpened the hypotheses. Facts 2–4 need **no least element at
all** — I had passed `⊥ ∈ C` to the union lemma out of the paper's framing, and
it is unused. They now live in a section with only `[Preorder α]`.

## Embedding–projection pairs

`f ∘ g = id` and `g ∘ f ⊑ id`, stated pointwise since the order on `ScottHom` is
pointwise. Two further paper claims fall out in a line each:

> … a projection is a surjection (i.e. onto) and an embedding is an injection
> (i.e. one-to-one).

`injective_embedding` and `surjective_projection`, both **axiom-free** — `g` has a
left inverse and `f` a right inverse, and that is the whole content.

## What is not yet defined

The **finitary** condition on a projection — "`im(p)` is a domain" — is not
formalized. It needs `Set.range p` to carry a `CompletePartialOrder` and a
`Domain` instance as a subtype. The image of a continuous idempotent is closed
under directed suprema, so the sub-cpo exists; constructing it is a round of its
own, and Lemma 5 and Theorem 6 both quantify over it. The inventory marks the
projection row `~` rather than `✓` for exactly this reason.

## Totals

Ten modules, 1567 lines, 0 `sorry`, 0 warnings. Numbered results **2 of 28**
(Lemma 4, Theorem 7). Definitions **6 of ≈13**.
