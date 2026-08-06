---
round: r0008
from: orchestrator
to: orchestrator
subject: step-functions
date: 2026-0806-14:12
status: done
related:
  - plans/r0007-plan-from-orchestrator-to-orchestrator-function-space-bounded-complete.md
  - reports/r0007-report-from-orchestrator-to-user-function-space-bounded-complete.md
---

# r0008 — Single step functions

The paper, continuing Theorem 7's proof past where r0007 stopped:

> To prove that `D → E` is a domain we must demonstrate its basis. Suppose
> `N ⊆ K(D)` is finite and `s : N → K(E)` is monotone. Then the function
> `step(s) : D → E` given by `step(s)(x) = ⨆{s(y) | y ∈ N ∩ ↓x}` is continuous
> and compact in the ordering on `D → E`. These are called step functions and it
> is possible to show that they form a basis for `D → E`.

Deliverable: `ScottDomains/StepFunction.lean` — the **single** step function
`step k e`, the case `N = {k}`, with its continuity, its compactness, and the
adjunction that characterizes it.

## Why the single step function first, and not `step(s)` directly

`step(s)` for finite `N` is the join of the single step functions `step y (s y)`
for `y ∈ N`. That join needs `E` bounded complete (to have the finite suprema)
and needs the join of compacts to be compact, which is a separate argument. The
single case needs neither, and every property of the general case is proved from
it. Doing the general case first would entangle three independent obligations in
one proof.

## The three results, and what each costs

Write `step k e x = if k ≤ x then e else ⊥`.

**Continuity needs `k` compact.** For directed nonempty `s` with `IsLUB s a`:
if `k ≤ a` then compactness of `k` gives `y ∈ s` with `k ≤ y`, so `e` is attained
in the image and is its greatest element; if `k ≰ a` then `k ≰ x` for every
`x ∈ s` (else `k ≤ x ≤ a`), so the image is `{⊥}` and `step k e a = ⊥`. This is
the *only* place compactness of `k` is used.

**The adjunction needs nothing.** `step k e ≤ f ↔ e ≤ f k` for any continuous
`f`: forward by evaluating at `k`, where `k ≤ k`; backward by cases on `k ≤ x`,
using monotonicity of `f` in the true branch and `bot_le` in the false one. This
is the workhorse — it converts every statement about a step function into a
statement about one value of `f`.

**Compactness needs `e` compact, not `k`.** Given directed `d` with
`IsLUB d F` and `step k e ≤ F`: the adjunction gives `e ≤ F k`; `F k` is the
least upper bound of the evaluation image at `k` (r0006's
`coe_sSup_of_directed` and `directedOn_eval_image`); compactness of `e` yields
`f ∈ d` with `e ≤ f k`; the adjunction converts that back to `step k e ≤ f`.
The compactness of `k` is carried only because the definition needs it for
continuity.

## Steps, each with its verification

| # | Step | Verify |
| -- | ---- | ------ |
| 1 | `def stepFun (k : α) (e : β) : α → β` — `if k ≤ x then e else ⊥`, classical | elaborates |
| 2 | `theorem stepFun_apply_of_le` / `_of_not_le` | `if_pos` / `if_neg` |
| 3 | `theorem monotone_stepFun` | two cases; `bot_le` in the false branch |
| 4 | `theorem scottContinuous_stepFun (hk : IsCompactElement k)` | the two-case argument above |
| 5 | `def step (hk : IsCompactElement k) (e : β) : ScottHom α β` | bundles 1 and 4 |
| 6 | `@[simp] theorem coe_step`, `step_apply_self : step hk e k = e` | `rfl` / `if_pos le_rfl` |
| 7 | `theorem step_le_iff {f : ScottHom α β} : step hk e ≤ f ↔ e ≤ f k` | the adjunction |
| 8 | `theorem isCompactElement_step (he : IsCompactElement e) : IsCompactElement (step hk e)` | via 7 and the evaluation image |
| 9 | `theorem step_mono` — monotone in `e` | via 7 |
| 10 | `lake build`; `#print axioms` | 0 errors, 0 warnings, 0 `sorry` |
| 11 | `docs/PaperInventory.md`, `INDEX.md`, PDF | step functions recorded |

Dependencies: 1→{2,3}, {2,3}→4, {1,4}→5, 5→{6,7}, 7→{8,9}. Span is 5.

## Design decisions

1. **`k`'s compactness is a parameter of `step`, not a typeclass.** `IsCompactElement k`
   is a proposition about a particular element, not a structure on the type. Lean's
   definitional proof irrelevance makes `step hk e` and `step hk' e` the same term,
   so carrying the proof costs nothing at use sites.

2. **`stepFun` is a plain function, `step` is the bundled `ScottHom`.** Statements
   that do not need the order (steps 2, 3) are about `stepFun`; the rest are about
   `step`. This keeps the continuity proof out of every rewrite.

3. **Classical `if`.** `k ≤ x` is not decidable in general. `Classical.dec` is
   already a dependency of the `ScottHom` `SupSet` instance, so this adds nothing
   new to the axiom profile.

## Acceptance criteria

| # | Criterion | Measurement |
| -- | --------- | ----------- |
| 1 | Builds | `lake build` exits 0, 0 errors, 0 warnings |
| 2 | Nothing unproved | `grep -c sorry` = 0; no `sorryAx` |
| 3 | The adjunction is the workhorse | steps 8 and 9 are proved *through* step 7, not by unfolding `stepFun` |
| 4 | Compactness is attributed correctly | `isCompactElement_step` requires `IsCompactElement e`; `IsCompactElement k` enters only through `step`'s continuity |

## Out of scope

`step(s)` for a finite `N` with monotone `s`, the basis property, algebraicity of
`D → E`, and Theorem 7. Those need finite joins of step functions and therefore
`E` bounded complete; they are r0009.
