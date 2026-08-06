---
round: r0013
from: orchestrator
to: user
subject: projection-image
date: 2026-0806-14:52
started: 2026-0806-14:48
finished: 2026-0806-14:52
related:
  - plans/r0013-plan-from-orchestrator-to-orchestrator-projection-image.md
  - reports/r0012-report-from-orchestrator-to-user-normal-subposets.md
---

# r0013 — The image of a projection is a cpo; finitary projections

`ScottDomains/Projection.lean` grows to 170 lines. `im(p)` now carries a
`CompletePartialOrder`, so "`im(p)` is a domain" is statable and
`IsFinitaryProjection` exists. 0 `sorry`, 0 warnings. Elapsed 4 minutes.

| # | Criterion | Measurement |
| -- | --------- | ----------- |
| 1 | Builds | 0 errors, 0 warnings |
| 2 | Nothing unproved | 0 `sorry`, no `sorryAx` |
| 3 | Definition count | finitary projection moves `~ → ✓`; **7 of ≈13** |
| 4 | Construction is choice-free | **not met as stated** — see below |

## The definition needs no case split; the proof does

The design claim held: setting `sSup s := ⟨p (⨆ (val '' s)), _⟩` lands in
`Set.range p` **by construction**, since `p` applied to anything is in its own
range. No `dite` on directedness, unlike `ScottHom`'s `SupSet`. On a directed set
the outer `p` is the identity, which is what `lubOfDirected` proves.

But criterion 4 said the *construction* would avoid `Classical.choice`, and
measurement says otherwise: `IsProjection.apply_sSup_of_directed` depends on
`propext`, `Classical.choice`, `Quot.sound`. The choice enters through
`Set.eq_empty_or_nonempty` — `ScottContinuous` quantifies over *nonempty* directed
sets, so the empty case has to be split off and handled by `p ⊥ = ⊥`. That split
is classical.

So the precise statement is: the `SupSet` **definition** is case-split-free, which
was the point; the **proof** that it is a least upper bound is not, and the axiom
profile of the resulting structure is the same as `ScottHom`'s. The criterion was
written too strongly and the report records it rather than the intention.

`IsProjection.map_bot` — `p ⊥ = ⊥`, from `p ⊑ id` and `bot_le` — is axiom-free.

## Stating "is a domain" for a proof-dependent structure

The cpo structure on `↥(Set.range p)` depends on `hp : IsProjection p`, a proof,
so it cannot be an instance. It is a `@[reducible]` definition, and the finitary
condition applies `Domain` to it explicitly:

```
def IsFinitaryProjection (p : ScottHom α α) : Prop :=
  ∃ hp : IsProjection p, @Domain _ (IsProjection.rangeCompletePartialOrder hp)
```

Proof irrelevance makes the choice of `hp` immaterial. Lean required
`@[reducible]` on any definition of class type, which is the right marking here —
instance search must see through it.

## Elaboration failures

Three, all previously seen. `__ :=` parent splicing fails inside `where` and
works in the term-mode `{ … with }` form — identical to r0006. Dot notation on a
local whose type is a `def` unfolding to `And` resolves against `And`, not the
def, so `hp.rangeCompletePartialOrder` had to be written out. And a `Set.image`
membership wanted the equation in the opposite direction.

## Where the §3.1 results stand

Everything Lemma 5 and Theorem 6 quantify over now exists:

| # | Object | Lean |
| -- | ------ | ---- |
| 1 | `N ◁ A` | `IsNormalIn` (r0012) |
| 2 | embedding–projection pair | `IsEmbeddingProjectionPair` (r0012) |
| 3 | projection | `IsProjection` (r0012) |
| 4 | `im(p)` as a cpo | `IsProjection.rangeCompletePartialOrder` (r0013) |
| 5 | finitary projection | `IsFinitaryProjection` (r0013) |

Next is **Lemma 5**: the compact elements of `im(p)` are exactly `im(p) ∩ K(D)`,
and `im(p) ∩ K(D) ◁ K(D)`.

Eleven modules, 1647 lines, 0 `sorry`, 0 warnings. Numbered results **2 of 28**;
definitions **7 of ≈13**.
