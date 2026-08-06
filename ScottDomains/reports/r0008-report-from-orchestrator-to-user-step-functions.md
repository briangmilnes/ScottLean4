---
round: r0008
from: orchestrator
to: user
subject: step-functions
date: 2026-0806-14:16
started: 2026-0806-14:12
finished: 2026-0806-14:16
related:
  - plans/r0008-plan-from-orchestrator-to-orchestrator-step-functions.md
  - reports/r0007-report-from-orchestrator-to-user-function-space-bounded-complete.md
---

# r0008 — Step functions: result

`ScottDomains/StepFunction.lean`: 148 lines, 2 definitions, 8 theorems,
0 `sorry`, 0 warnings. Elapsed 4 minutes.

| # | Criterion | Measurement |
| -- | --------- | ----------- |
| 1 | Builds | `lake build` exits 0, 0 errors, 0 warnings, 0.6 s |
| 2 | Nothing unproved | `grep -c sorry` = 0; no `sorryAx` |
| 3 | The adjunction is the workhorse | `isCompactElement_step` and `step_mono` are proved through `step_le_iff`; neither unfolds `stepFun` |
| 4 | Compactness attributed correctly | `isCompactElement_step` requires `IsCompactElement e`; `IsCompactElement k` enters only through `step`'s continuity |

## The three results and where each hypothesis is spent

`step k e x = if k ≤ x then e else ⊥`, and the file is careful about which
compactness does what — the paper states the two together and it is easy to
assume both are needed everywhere.

| # | Result | Needs | Does not need |
| -- | ------ | ----- | ------------- |
| 1 | `scottContinuous_stepFun` | `IsCompactElement k` | anything about `e` |
| 2 | `step_le_iff : step hk e ≤ f ↔ e ≤ f k` | nothing | compactness of either |
| 3 | `isCompactElement_step` | `IsCompactElement e` | compactness of `k`, beyond what `step` already carries |

Result 1 is the only use of `k`'s compactness in the file. If `k ⊑ ⨆M` for
directed `M`, compactness produces `y ∈ M` with `k ⊑ y`, so the value `e` is
already attained in the image; otherwise `k` is below no member of `M`, the image
is `{⊥}`, and the value at the supremum is `⊥` too.

Result 2 costs nothing at all, and is the reason the file is short. It converts
every statement about a step function into a statement about a single value of
`f`. Result 3 then runs entirely through it: the adjunction turns
`step k e ≤ F` into `e ≤ F k`; `F k` is the least upper bound of the evaluation
image at `k` (r0006's `coe_sSup_of_directed` with `directedOn_eval_image`);
compactness of `e` yields `f ∈ d` with `e ≤ f k`; the adjunction converts that
back. No induction, no unfolding of the `if`.

## One elaboration failure, and it is the same one as last time

`step_le_iff` failed both directions with `rw` unable to find `⇑(step ?hk ?e)`,
because `PartialOrder.lift` leaves the goal as
`(fun f => ⇑f) (step hk e) k ≤ (fun f => ⇑f) f k`. `dsimp only` beta-reduces and
the rewrite fires. This is the fourth round in a row whose only failure was about
the form a term has after elaboration rather than about the mathematics, and the
second time this specific redex has appeared. It is a consequence of defining the
order by `PartialOrder.lift`; a `le_def` simp lemma exists in `ScottHom.lean` and
would serve as well.

## Axioms

All four principal results depend on `propext`, `Classical.choice`, and
`Quot.sound`. Choice enters through the `if k ≤ x` — the order on a general
domain is not decidable — and was already a dependency of `ScottHom`'s `SupSet`
instance, so the axiom profile of the development is unchanged.

## Where Theorem 7 stands

The paper's `step(s)` for finite `N ⊆ K(D)` and monotone `s : N → K(E)` is the
join of the single step functions `step y (s y)` over `y ∈ N`. That join needs
`E` bounded complete, which r0007 supplies, and needs a join of compacts to be
compact, which is a separate argument. With `step(s)` in hand, the basis property
gives algebraicity of `D → E` and completes Theorem 7 — the first of the 28
numbered results.

Counts unchanged: **9 definitions and 28 results remaining**. Five modules,
837 lines, 0 `sorry`.
