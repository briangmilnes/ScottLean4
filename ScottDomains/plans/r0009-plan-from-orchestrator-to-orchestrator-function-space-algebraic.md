---
round: r0009
from: orchestrator
to: orchestrator
subject: function-space-algebraic
date: 2026-0806-14:17
status: done
related:
  - plans/r0008-plan-from-orchestrator-to-orchestrator-step-functions.md
  - reports/r0008-report-from-orchestrator-to-user-step-functions.md
---

# r0009 — `D → E` is algebraic

The paper's "it is possible to show that they form a basis for `D → E`", which is
all that stands between r0008 and Theorem 7 except countability of the basis.

Deliverable: `IsAlgebraic (ScottHom α β)` for `D` algebraic, `E` algebraic and
bounded complete, plus the one general lemma about compact elements that the
proof needs.

## The two obligations of `IsAlgebraic`, and what each needs

**`compactsBelow f` is directed.** Two compact `g₁, g₂ ≤ f` are bounded above by
`f`, so `sSup {g₁, g₂}` is their least upper bound — this is exactly what r0007's
`BoundedComplete (ScottHom α β)` provides, and it is the reason r0007 had to come
first. The join is below `f` because `f` bounds the pair, and it is compact by a
general fact proved here for the first time:

> If `k₁` and `k₂` are compact and `c` is a least upper bound of `{k₁, k₂}`, then
> `c` is compact.

That belongs in `Domain.lean` next to `isCompactElement_bot`, not in the function
space file: it is a statement about any cpo. Its proof is the directedness of the
approximating set — `k₁ ≤ x₁`, `k₂ ≤ x₂`, merge `x₁, x₂` to `y`, and `c ≤ y`
because `y` bounds the pair.

**`f` is the least upper bound of `compactsBelow f`.** Being an upper bound is
immediate. For leastness, let `u` bound `compactsBelow f` and fix `x`. Since `E`
is algebraic, `f x` is the least upper bound of its compact approximants, so it
suffices to send each compact `e ≤ f x` below `u x`. Since `D` is algebraic and
`f` is continuous, `f x` is the least upper bound of `f '' compactsBelow x`,
which is directed because `f` is monotone; compactness of `e` therefore yields a
compact `k ≤ x` with `e ≤ f k`. Then r0008 finishes it in two moves:
`step_le_iff` gives `step k e ≤ f`, `isCompactElement_step` gives that it is
compact, so it lies in `compactsBelow f` and hence below `u` — and evaluating at
`x`, where `k ≤ x`, gives `e = step k e x ≤ u x`.

Every hypothesis is used exactly once: `E` bounded complete for directedness,
`E` algebraic to reduce to compact `e`, `D` algebraic to produce compact `k`,
and r0008 to turn the pair `(k, e)` into a compact function.

## Steps

| # | Step | Verify |
| -- | ---- | ------ |
| 1 | `Domain.lean`: `isCompactElement_of_isLUB_pair` | the merge argument above |
| 2 | New file `ScottDomains/FunctionSpaceDomain.lean` | — |
| 3 | `directedOn_compactsBelow` for `ScottHom` | step 1 plus r0007's `isLUB_sSup_of_bddAbove` |
| 4 | `directedOn_image` — a monotone image of a directed set is directed | four lines, used in step 5 |
| 5 | `isLUB_compactsBelow` for `ScottHom` | the argument above |
| 6 | `instance : IsAlgebraic (ScottHom α β)` | steps 3 and 5 |
| 7 | `lake build`; `#print axioms` | 0 errors, 0 warnings, 0 `sorry` |
| 8 | `docs/PaperInventory.md`, `INDEX.md`, PDF | recorded |

## Acceptance criteria

| # | Criterion | Measurement |
| -- | --------- | ----------- |
| 1 | Builds | 0 errors, 0 warnings |
| 2 | Nothing unproved | 0 `sorry`, no `sorryAx` |
| 3 | The instance resolves | `IsAlgebraic (ScottHom (Set ℕ) (Set ℕ))` by `inferInstance`, composing r0005 |
| 4 | Step 1 is general | stated for any `[CompletePartialOrder α]`, not for `ScottHom` |

## Out of scope

Countability of `K(D → E)`, and therefore `Domain (ScottHom α β)` and Theorem 7
itself. Countability needs every compact function to be a *finite* join of step
functions, which is a further argument; that is r0010.
