---
round: r0013
from: orchestrator
to: orchestrator
subject: projection-image
date: 2026-0806-14:48
status: done
related:
  - reports/r0012-report-from-orchestrator-to-user-normal-subposets.md
---

# r0013 — The image of a projection is a cpo, and finitary projections

The one thing r0012 could not state. From §3.1:

> Let `D` be a cpo. We say that a continuous function `p : D → D` is a
> **finitary projection** if `p ∘ p = p ⊑ id` and `im(p) = {p(x) | x ∈ D}` is a
> domain.

To say "`im(p)` is a domain" in Lean, `↥(Set.range p)` must carry a
`CompletePartialOrder`. This round builds it, then defines
`IsFinitaryProjection`. Lemma 5 and Theorem 6 both quantify over it.

## Why the image is a cpo

`p` is continuous and idempotent, so `Set.range p` is closed under directed
suprema: for directed `s ⊆ im(p)`, continuity gives
`p(⨆s) = ⨆(p '' s) = ⨆s`, the middle step because `p` fixes its own image
(`IsProjection.apply_of_mem_range`, r0012). It is also closed downward at the
bottom: `p ⊥ ≤ ⊥` from `p ⊑ id`, so `p ⊥ = ⊥` and `⊥ ∈ im(p)`.

**No case split is needed in the definition of `sSup`.** Setting
`sSup s := ⟨p (⨆ (val '' s)), _⟩` lands in `Set.range p` *by construction* for
every `s`, directed or not — `p` applied to anything is in its own range. The
`dite` that `ScottHom` needed is avoided entirely, so the instance is
`Classical.choice`-free where `ScottHom`'s was not. On directed `s` the extra `p`
is the identity, which is what `lubOfDirected` proves.

## Stating "is a domain" for a proof-dependent structure

The cpo structure on `↥(Set.range p)` depends on `hp : IsProjection p`, a proof,
so it cannot be an instance. It is a plain definition, and the finitary condition
applies `Domain` to it explicitly:

```
def IsFinitaryProjection (p : ScottHom α α) : Prop :=
  ∃ hp : IsProjection p, @Domain _ hp.rangeCompletePartialOrder
```

Proof irrelevance makes the choice of `hp` immaterial.

## Steps

| # | Step | Verify |
| -- | ---- | ------ |
| 1 | `IsProjection.map_bot : p ⊥ = ⊥` | `le_antisymm (hp.le ⊥) bot_le` |
| 2 | `directedOn_val_image` — a directed set in the subtype has a directed image | `Subtype.val` is monotone |
| 3 | `IsProjection.apply_sSup_of_directed` — `p (⨆ (val '' s)) = ⨆ (val '' s)` | continuity, then `p '' (val '' s) = val '' s`; the empty case via step 1 |
| 4 | `IsProjection.rangeCompletePartialOrder` | fields: `sSup` as above, `bot := ⟨⊥, _⟩`, `lubOfDirected` from step 3 |
| 5 | `def IsFinitaryProjection` | elaborates |
| 6 | `IsFinitaryProjection.isProjection` | projection of the existential |
| 7 | `lake build`, `#print axioms`, docs, PDF, commit | 0 errors, 0 warnings, 0 `sorry` |

## Acceptance criteria

| # | Criterion | Measurement |
| -- | --------- | ----------- |
| 1 | Builds | 0 errors, 0 warnings |
| 2 | Nothing unproved | 0 `sorry`, no `sorryAx` |
| 3 | Definition count | finitary projection moves `~ → ✓`; **7 of ≈13** |
| 4 | The construction is choice-free | `rangeCompletePartialOrder` avoids `Classical.choice`, unlike `ScottHom`'s `SupSet` |

## Out of scope

Lemma 5 (`K(im p) = im(p) ∩ K(D)` and `im(p) ∩ K(D) ◁ K(D)`) and Theorem 6 (the
isomorphism between normal substructures and `Fp(D)`). Both become statable once
this round lands.
