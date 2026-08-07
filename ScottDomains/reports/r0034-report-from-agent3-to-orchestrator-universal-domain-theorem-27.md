---
round: r0034
from: agent3
to: orchestrator
subject: universal-domain-theorem-27
date: 2026-0806-23:14
started: 2026-0806-22:40
finished: 2026-0806-23:14
related:
  - plans/r0034-plan-from-orchestrator-to-agent3-universal-domain-theorem-27.md
---

# r0034 agent3 — §7.3's universal domain `U`, and Theorem 27

**Status at this revision: Part 1 is complete and compiles (0 errors, 0 warnings,
0 `sorry`). Part 2 is in progress.** This file is written early and committed
early because agent4's Lemma 28 and agent5's Lemma 30 instantiate at `U`; the
interface below is final and will not change.

## Interface note for agent4 and agent5 — `U` as built

Module: `ScottDomains/ScottDomains/Dyadic.lean`, namespace
`ScottDomains.Dyadic`. Import it as `import ScottDomains.Dyadic`.

### The points

    def S : Set ℚ := {q | ∃ n m : ℕ, 0 < m ∧ n < 2 ^ m ∧ q = (n : ℚ) / 2 ^ m}

the paper's `S`, the dyadic rationals of `[0, 1)`. `mem_Ico_of_mem_S` proves
`q ∈ S → 0 ≤ q ∧ q < 1`.

    def E : Set ℚ := {q | ∃ n m : ℕ, 0 < m ∧ n ≤ 2 ^ m ∧ q = (n : ℚ) / 2 ^ m}

the admissible interval endpoints — the dyadic rationals of the *closed*
`[0, 1]`, i.e. `S` together with `1`. `max_mem_E`, `min_mem_E`, `zero_mem_E`,
`one_mem_E`.

    def Ivl (r t : ℚ) : Set ℚ := {s | s ∈ S ∧ r ≤ s ∧ s < t}   -- the paper's `[r, t)`

with `Ivl_zero_one : Ivl 0 1 = S` and
`Ivl_inter : Ivl r t ∩ Ivl r' t' = Ivl (max r r') (min t t')`.

### The basis `U₀` — carrier and pre-order

    def unionOf (F : Finset (ℚ × ℚ)) : Set ℚ := ⋃ p ∈ F, Ivl p.1 p.2

    def IsBasic (X : Set ℚ) : Prop :=
      X.Nonempty ∧ ∃ F : Finset (ℚ × ℚ), (∀ p ∈ F, p.1 ∈ E ∧ p.2 ∈ E) ∧ X = unionOf F

    def U₀ : Type := {X : Set ℚ // IsBasic X}

`U₀` is the paper's basis: the finite **non-empty** unions of dyadic half-open
intervals of `[0, 1)`. Access the underlying set with `U₀.toSet X : Set ℚ`
(`U₀.mk`, `U₀.ext`, `U₀.toSet_mk` round it out); it is a plain `def`, not an
`abbrev`, so that Mathlib's `Subtype.partialOrder` — which orders by `⊆`, the
*wrong* direction — is not found.

**The pre-order is superset**, in Mathlib's orientation:

    theorem U₀.le_iff {X Y : U₀} : X ≤ Y ↔ toSet Y ⊆ toSet X

More information is a *narrower* set of dyadic points. Instances on `U₀`:
`PartialOrder` (the display above), `OrderBot` with `⊥ = [0, 1) = S`
(`U₀.toSet_bot : toSet ⊥ = S`), and `Countable` (`U₀.countable_isBasic` is the
underlying `Set.Countable`).

### `U` and `K(U)`

    abbrev U : Type := IdealCompletion U₀

An `abbrev`, so Theorem 11's instances on `IdealCompletion U₀` —
`CompletePartialOrder`, `IsAlgebraic`, `Domain` — are found by instance search at
`U`. Two further facts are proved here:

| # | Statement | Name |
| - | --------- | ---- |
| 1 | `U` is a domain | `Domain U` by `inferInstance`; `thm11_at_U` states it with the `K(U)` conjunct |
| 2 | `K(U) = {↓X | X ∈ U₀}` | `compacts_U : compacts U = Set.range (IdealCompletion.principal : U₀ → U)` |
| 3 | compact ⇔ principal | `isCompactElement_iff : IsCompactElement I ↔ ∃ X : U₀, I = IdealCompletion.principal X` |
| 4 | membership in a compact | `mem_principal_iff : Y ∈ (principal X : U) ↔ toSet X ⊆ toSet Y` |
| 5 | `U` is bounded complete | `instance : BoundedComplete U` |

Read row 4 as: the compact element `↓X` of `U` is the set of basis elements
**containing** `X` — a superset is a coarser approximation. Row 5 is not in the
plan but is the property §7.3 exists for: the least upper bound of a bounded pair
`X, Y` of `U₀` is the *intersection* `toSet X ∩ toSet Y`
(`U₀.exists_isLUB_pair`), and `IdealCompletion.boundedComplete` lifts that to
`U`. §7.4 opens by observing that the convex powerdomain cannot be represented
over `U` precisely because a projection of `U` inherits bounded completeness.

Nothing about ideals, cpos, algebraicity or compactness is re-proved in this
module. Part 1 is exactly three instances on `U₀` — the superset order, the
least element `[0, 1)`, and countability — after which Theorem 11
(`IdealCompletion.instDomain`, `IdealCompletion.thm11`) supplies the rest.

## Measured counts

| # | Metric | Value |
| - | ------ | ----- |
| 1 | New module | `ScottDomains/ScottDomains/Dyadic.lean` |
| 2 | Lines in the new module | 351 |
| 3 | `theorem`/`lemma` declarations in the new module | 32 |
| 4 | `sorry` in the new module | 0 |
| 5 | Development totals after Part 1 | 46 modules, 14399 lines, 691 theorems |
| 6 | Pre-existing `sorry` elsewhere | 8, in `Skeleton/Recovered.lean` (7) and `Skeleton/Section6.lean` (1) — untouched |
| 7 | `scripts/compile.sh -r r0034 ScottDomains.Dyadic` | exit 0, 0 errors, 0 warnings, 0 `sorry`, wall 1.41 s |

## Part 2 — Theorem 27

In progress; this section is rewritten when Part 2 lands or when its obstruction
is stated.
