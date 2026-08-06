---
round: r0018
from: orchestrator
to: orchestrator
subject: theorem3
date: 2026-0806-15:22
status: done
related:
  - reports/r0018-report-from-orchestrator-to-user-theorem3.md
---

# r0018 — Theorem 3: `fix` is the unique uniform fixed point operator

> **Definition:** A fixed point operator `F` is a class of continuous functions
> `F_D : (D → D) → D` such that, for each cpo `D` and continuous `f : D → D`, we
> have `F_D(f) = f(F_D(f))`.
>
> `F` is **uniform** if, for any continuous `f : D → D`, `g : E → E` and strict
> continuous `h : D → E` making the square commute, `h(F_D(f)) = F_E(g)`.
>
> **Theorem 3** `fix` is the unique uniform fixed point operator.

## The formalization decision, settled

"A class indexed by all cpos" is not a function in Lean but a family over a
universe. `FixedPointOperator.{u}` is a structure whose field takes a type
`D : Type u` **and** a `CompletePartialOrder D` instance and returns
`ScottHom D D → D`; uniformity quantifies over two such types at once. No
universe bump is needed: the subtype `↓fix(f)` the proof requires lives in the
same `Type u` as `D`.

The paper additionally asks each `F_D` to be continuous. That hypothesis is
**not used** by the uniqueness argument, so it is omitted from the structure —
including it would weaken the theorem.

## Steps

| # | Step | Verify |
| -- | ---- | ------ |
| 1 | `directedOn_val_image_subtype`, `sSup_val_image_le` | a directed set below `a` has its supremum below `a` |
| 2 | `IicSup`, `coe_IicSup_of_le`, `IicCpo` | `↓a` is a cpo; the `dite` is forced by `SupSet` totality, as in `ScottHom` |
| 3 | `FixedPointOperator`, `IsUniform`, `kleeneOperator` | elaborate |
| 4 | `key` — least upper bounds in `↓a` are least upper bounds in `D` | uniqueness against `lubOfDirected` |
| 5 | `f₀`, the restriction of `f` to `↓fix(f)` | `x ⊑ fix f ⟹ f x ⊑ f (fix f) = fix f` |
| 6 | `i`, the inclusion: continuous and strict | step 4; `i ⊥ = ⊥` by `rfl` |
| 7 | `theorem3` | uniformity along `i`, then uniqueness of `f₀`'s fixed point via Theorem 1 |

## Acceptance criteria

| # | Criterion | Measurement |
| -- | --------- | ----------- |
| 1 | Builds | 0 errors, 0 warnings |
| 2 | Nothing unproved | 0 `sorry`, no `sorryAx` |
| 3 | Theorem 3 stated for a genuine class of operators | the structure quantifies over every `CompletePartialOrder` in `Type u` |
| 4 | §2 complete | Theorems 1, 2, 3 all accounted for |
