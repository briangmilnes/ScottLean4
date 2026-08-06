---
round: r0018
from: orchestrator
to: user
subject: theorem3
date: 2026-0806-15:26
started: 2026-0806-15:22
finished: 2026-0806-15:26
related:
  - plans/r0018-plan-from-orchestrator-to-orchestrator-theorem3.md
  - reports/r0017-report-from-orchestrator-to-user-fixed-point.md
---

# r0018 — Theorem 3 proved; §2 complete

**Sixth of the 29 numbered results, and the last one in §2.**
`ScottDomains/UniformFixedPoint.lean`: 175 lines, 0 `sorry`, 0 warnings. Elapsed
4 minutes.

| # | Criterion | Measurement |
| -- | --------- | ----------- |
| 1 | Builds | 0 errors, 0 warnings |
| 2 | Nothing unproved | 0 `sorry`, no `sorryAx` |
| 3 | Stated for a genuine class of operators | the structure quantifies over every `CompletePartialOrder` in `Type u` |
| 4 | §2 complete | Theorems 1 (r0017), 2 (Mathlib), 3 (here) |

## The formalization decision

"A fixed point operator is a **class** of continuous functions `F_D : (D → D) → D`"
is not a function in Lean — it is a family over a universe of types.
`FixedPointOperator.{u}` is therefore a structure whose field takes a type
`D : Type u` *and* a `CompletePartialOrder D` instance and returns
`ScottHom D D → D`. Uniformity quantifies over two such types at once, with a
strict continuous map between them.

Nothing bumps universes, which was the risk: the subtype `↓fix(f)` that the proof
needs lives in the same `Type u` as `D`.

**One hypothesis was dropped deliberately.** The paper asks each `F_D` to be
continuous. The uniqueness argument never uses it, so it is not part of the
structure — including it would have weakened the theorem by quantifying over
fewer operators.

## The proof, following the paper

Restrict to `D₀ = ↓fix(f)`. It is a cpo: it contains `⊥`, and a directed subset
has its supremum below `fix(f)`. `f` restricts to it, because `x ⊑ fix f` gives
`f x ⊑ f (fix f) = fix f`. The inclusion `i : D₀ → D` is strict and continuous
and satisfies `i ∘ f₀ = f ∘ i` — both by `rfl`, which is the payoff of defining
`D₀` as a subtype with the induced order.

Uniformity then gives `i (F_{D₀}(f₀)) = F_D(f)`. And `f₀` has **exactly one**
fixed point: any fixed point of `f₀` is a fixed point of `f` lying below `fix f`,
and Theorem 1 (r0017) says `fix f` is the least such — so the two are equal.
Hence `F_D(f) = fix f`.

Theorem 1 is used as a black box here, which is why r0017 had to come first: had
the inventory's claim that Theorem 1 was Mathlib reuse gone unchecked, this proof
would have had no least-fixed-point property to appeal to in the paper's setting.

## `↓a` as a cpo

Built as `IicCpo`, with the same `dite`-on-a-condition shape that `ScottHom`
needed and for the same reason: `SupSet` is total, but the supremum of a
non-directed subset of `↓a` need not stay below `a`. On directed sets the first
branch always applies, and `coe_IicSup_of_le` strips the split once.

## Elaboration failures

Two, both familiar. A definition of class type again needed `@[reducible]`. And
`hfa ▸ f.monotone x.2` failed with "failed to compute motive" — `▸` could not
guess where to substitute; `le_of_le_of_eq (f.monotone x.2) hfa` says the same
thing without asking it to.

## Totals

Sixteen modules, 2403 lines, 125 theorems, 0 `sorry`, 0 warnings.
Numbered results **6 of 29** — Theorems 1, 3, 6, 7 and Lemmas 4, 5. Prose claims
**11**. Definitions **7 of ≈13**.

**§2 and §3.1 are complete**, with §3.2's effective presentations the only §3 gap.

## Next

§4: the smash product `D ⊗ E`, sum and lift, and the currying and
product/function-space isomorphism laws (Lemmas 8, 9), then Lemma 10, Theorem 11
(ideal completion of a countable pre-order) and Theorem 14.
