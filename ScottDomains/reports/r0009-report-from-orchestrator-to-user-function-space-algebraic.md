---
round: r0009
from: orchestrator
to: user
subject: function-space-algebraic
date: 2026-0806-14:20
started: 2026-0806-14:17
finished: 2026-0806-14:20
related:
  - plans/r0009-plan-from-orchestrator-to-orchestrator-function-space-algebraic.md
  - reports/r0008-report-from-orchestrator-to-user-step-functions.md
---

# r0009 — `D → E` is algebraic: result

`ScottDomains/FunctionSpaceDomain.lean` (118 lines) plus one general theorem
added to `Domain.lean`. The mathematics **built on the first attempt** — the only
edits after that were to sharpen hypotheses the linter reported as unused.
0 `sorry`, 0 warnings. Elapsed 3 minutes.

| # | Criterion | Measurement |
| -- | --------- | ----------- |
| 1 | Builds | `lake build` exits 0, 0 errors, 0 warnings |
| 2 | Nothing unproved | `grep -c sorry` = 0; no `sorryAx` |
| 3 | The instance resolves | `IsAlgebraic (ScottHom (Set ℕ) (Set ℕ))` by `inferInstance`, composing r0005 with this round |
| 4 | The general lemma is general | `isCompactElement_of_isLUB_pair` is stated at `[PartialOrder α]` with the least upper bound as a hypothesis, and **depends on no axioms at all** |

## The result

`IsAlgebraic (ScottHom α β)` for `D` algebraic and `E` algebraic and bounded
complete: every continuous function is the directed least upper bound of the
compact functions below it. This is the paper's "it is possible to show that they
form a basis for `D → E`", which Theorem 7's proof asserts without argument.

The proof of the second half, in one paragraph: let `u` bound `compactsBelow f`
and fix `x`. `E` algebraic reduces `f x ≤ u x` to sending each compact `e ≤ f x`
below `u x`. `D` algebraic plus continuity of `f` makes `f x` the least upper
bound of `f '' compactsBelow x`, which is directed because `f` is monotone, so
compactness of `e` yields a compact `k ≤ x` with `e ≤ f k`. Then r0008 finishes
in two moves: `step_le_iff` puts `step k e` below `f`, `isCompactElement_step`
makes it compact, so it lies in `compactsBelow f` and hence below `u`; evaluating
at `x`, where `k ≤ x`, gives `e = step k e x ≤ u x`.

## The linter found a sharper statement than the plan had

The paper states its hypotheses as one block — "`D` and `E` bounded complete
domains" — and the plan inherited that framing. Lean's `unusedSectionVars` linter
reported three declarations carrying hypotheses they never used, and restructuring
the file around those reports produced a strictly more precise result:

| # | Result | Actually needs |
| -- | ------ | -------------- |
| 1 | `directedOn_image` | nothing but monotonicity |
| 2 | `directedOn_compactsBelow_scottHom` | `E` **bounded complete** only — not algebraicity of either |
| 3 | `isLUB_compactsBelow_scottHom` | `D` and `E` **algebraic** only — not bounded completeness |
| 4 | the `IsAlgebraic` instance | all of the above |

The two halves of `IsAlgebraic` use *disjoint* parts of the hypothesis block.
That is not visible in the paper's prose and would not have been visible here
either, had the warnings been silenced instead of acted on. The file's section
boundaries now record it, so the attribution is maintained by the build.

`isCompactElement_of_isLUB_pair` — a least upper bound of two compact elements is
compact — went into `Domain.lean` rather than the function space file, because it
is a statement about any partial order with no completeness in sight. It depends
on no axioms whatever.

## Axioms

The two function-space theorems carry `propext`, `Classical.choice` and
`Quot.sound`, inherited from `ScottHom`'s `SupSet` and from the step function's
classical `if`. The new general lemma is axiom-free.

## Where Theorem 7 stands

Theorem 7 says: `D`, `E` bounded complete domains ⟹ `D → E` is a bounded complete
domain. Of the three conjuncts in the conclusion:

| # | Conjunct | Status |
| -- | -------- | ------ |
| 1 | `D → E` is a cpo | done, r0006 |
| 2 | `D → E` is bounded complete | done, r0007 |
| 3 | `D → E` is algebraic | **done, this round** |
| 4 | `K(D → E)` is countable | remaining |

`Domain` carries the countability condition (the one r0004 recovered from the
paper and the inventory had dropped), so conjunct 4 is genuinely required. It
needs every compact function to be a *finite* join of step functions — the
paper's `step(s)` for finite `N ⊆ K(D)` — which then injects `K(D → E)` into the
finite subsets of `K(D) × K(E)`. That is r0010, and it is the last step to the
first of the 28 numbered results.

Six modules, 985 lines, 0 `sorry`. Counts unchanged at **9 definitions and 28
results remaining** until Theorem 7 closes.
