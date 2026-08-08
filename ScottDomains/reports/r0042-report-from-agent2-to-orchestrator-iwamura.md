---
round: r0042
from: agent2
to: orchestrator
subject: iwamura
date: 2026-0808-14:35
started: 2026-0808-14:05
finished: 2026-0808-14:35
related:
  - ScottDomains/plans/r0042-plan-from-orchestrator-to-orchestrator-clear-the-sorry.md
  - ScottDomains/ScottDomains/Iwamura.lean
  - ScottDomains/ScottDomains/JungNets.lean
---

# r0042 agent2 — Iwamura's lemma and Markowsky's theorem, formally verified

## Result

**Chain-complete implies directed-complete is now available**, and from a
hypothesis strictly weaker than the plan asked for: suprema of **well-ordered**
chains suffice. `ScottDomains/ScottDomains/Iwamura.lean`, 635 lines, 39
declarations, built with zero errors, zero warnings and zero `sorry`. Every
headline result is kernel-checked on `[propext, Classical.choice, Quot.sound]`.

Acceptance item (1) of the brief is met; items (2) and (3) are met as byproducts;
item (4), the negative verdict, does not apply.

## The declarations that matter

| # | Declaration | Statement |
| -- | ---------- | --------- |
| 1 | `exists_chain_directed_cover` | **Iwamura's lemma.** A directed `t` with `ℵ₀ ≤ #t` is `⋃₀ 𝒞` for a `⊆`-chain `𝒞`, well-ordered by `⊆`, of nonempty directed subsets each of cardinality `< #t` |
| 2 | `hasDirectedSuprema_of_hasWellOrderedSuprema` | **Markowsky's theorem**, from well-ordered chains only |
| 3 | `hasChainSuprema_of_hasWellOrderedSuprema` | suprema of well-ordered chains give suprema of all chains |
| 4 | `hasChainInfima_of_hasWellOrderedInfima` | **Jung's Corollary 1.3 as he uses it**, dually: infima for monotone injective nets indexed by an ordinal give `JungNets.HasChainInfima` |
| 5 | `isBicomplete_of_hasChainInfima` | Jung's Theorem 1.2, dual form: `HasChainInfima D → IsBicomplete D` |
| 6 | `thm137Chains_of_wellOrderedInfima` | `(IsAlgebraic (ScottHom D D) → HasWellOrderedInfima D) → JungNets.Thm137Chains D` |
| 7 | `thm137Chains_iff_thm137` | `JungNets.Thm137Chains D ↔ JungNets.Thm137 D` |
| 8 | `hasChainInfima_iff_isBicomplete` | the same equivalence at the predicate level |

Row 6 is the one the round should carry forward. Combined with agent5's
`Thm18.thm18_of_thm137Chains_and_cor136`, the remaining obligation for Theorem 18
is now: **find infima for monotone injective nets indexed by an ordinal**, plus
Corollary 1.36. Nothing weaker than that is required and nothing stronger.

## Which escape route held

**Neither, in the form the brief posed them, and route 1 inverted.**

* **Route 2 (`BourbakiWitt`) does not hold.** Mathlib's
  `ChainCompletePartialOrder` (`Mathlib/Order/BourbakiWitt.lean:53`) carries an
  instance to `OmegaCompletePartialOrder` and none to `CompletePartialOrder`, and
  the file proves the Bourbaki–Witt fixed-point theorem, not a completeness
  transfer. Re-measured this round: `grep -rn "Iwamura\|Markowsky" Mathlib/` → **0
  hits**, confirming r0037. The theorem had to be built.
* **Route 1 held, but backwards from how the brief framed it.** The brief asked
  whether the *specific instance* Theorem 1.37 needs is weaker than "all directed
  sets". It is — the coordinator's mid-round correction from agent5 fixed that
  precisely: only `Thm137Chains` is ever spent. But the weakening runs the other
  way from Iwamura's lemma: what Jung's proof *produces* is infima of
  ordinal-indexed nets, and what the development *consumes* is infima of arbitrary
  chains, so a reduction is still needed — just the reduction
  `well-ordered chains ⟹ chains` rather than `chains ⟹ directed sets`.

  That reduction came out of the general theorem **free of charge**: an arbitrary
  chain is a directed set, so proving directed-completeness from
  well-ordered-chain-completeness already covers it. The direct argument (every
  linear order has a coinitial well-ordered subset, by Zorn over initial segments)
  was therefore never needed. One transfinite induction, not two.

## Proof structure, and its cost

Strong induction on `#t` along `Cardinal.lt_wf`, in two cases:

1. **`t` countable** — settled outright, no induction hypothesis used. Enumerate
   `t` as `f : ℕ → D` (`Set.Countable.exists_eq_range`), build `v : ℕ → t` by
   `v 0 = f 0`, `v (n+1) = ub (v n) (f (n+1))`. `range v` is a well-ordered chain
   (`isWellOrderedSet_range`) whose supremum is the supremum of `t`.
2. **`ℵ₀ < #t`** — the **directed closure** `close ub E`: adjoin a chosen upper
   bound `ub x y` for every pair and iterate `ω` times. It is directed, monotone
   in `E`, and `#(close ub E) ≤ c` for any infinite `c ≥ #E`
   (`Cardinal.mk_iUnion_le`, `mul_eq_self`, `add_eq_self`, `aleph0_mul_eq`).
   Well-order `t` in order type `(#t).ord` and take
   `F a = close ub (e '' Iic a)`; `Cardinal.mk_Iio_lt` gives `#(F a) < #t`. The
   induction hypothesis supplies a supremum `g a` of each; `g` is monotone, so
   `range g` is a chain, and well-ordered because the index is.

The `ℵ₀` and `> ℵ₀` cases are genuinely different constructions and Iwamura's
lemma is stated with both: the `ω`-iterated closure of a finite set is in general
infinite, so it cannot produce the *finite* stages that `κ = ℵ₀` demands. Those
come from `f '' Iic n ∪ v '' Iic n`, directed because `v n` is a greatest element.

## Mathlib survey, measured this round

| # | Item | Present? | Measurement |
| -- | ---- | -------- | ----------- |
| 1 | Iwamura / Markowsky | **no** | `grep -rn "Iwamura\|Markowsky" Mathlib/` → 0 hits |
| 2 | `ChainCompletePartialOrder → CompletePartialOrder` | **no** | `Mathlib/Order/BourbakiWitt.lean:53`, instance to `OmegaCompletePartialOrder` only |
| 3 | Well-founded order on `Cardinal` | yes | `Cardinal.lt_wf`, `SetTheory/Cardinal/Order.lean:360` |
| 4 | Well-ordering of a type at its own cardinality | yes | `Ordinal.ToType`, `Cardinal.mk_ord_toType`, `Ordinal.type_toType` |
| 5 | `#(Iio a) < #ι` for `ι = c.ord.ToType` | yes | `Cardinal.mk_Iio_lt`, `SetTheory/Ordinal/Basic.lean:1210` |
| 6 | Infinite cardinal arithmetic | yes | `mul_eq_self`, `add_eq_self`, `aleph0_mul_eq`, `add_lt_of_lt` |
| 7 | Countable union bound | yes | `Cardinal.mk_iUnion_le` — same-universe only, so the closure indexes over `ULift.{u} ℕ` |
| 8 | Chain from a monotone map | yes | `Monotone.isChain_range` |
| 9 | Well-ordered range of a monotone map | **no** | proved here as `isWellOrderedSet_range` (11 lines) |
| 10 | Cofinal well-ordered subset of a linear order | **no** | not proved here either — the directed-set route makes it unnecessary |

## Measured build

| # | Metric | Value |
| -- | ----- | ----- |
| 1 | `ScottDomains.Iwamura` alone | 1.9 s, 985 jobs, 0 errors, 0 warnings, 0 `sorry` |
| 2 | Whole library after the change | 3.6 s wall, 1334 jobs, 0 errors, 0 non-`sorry` warnings |
| 3 | `sorry` count, before and after | **1 → 1** (`Skeleton/Section6.lean:197`, `thm18`) |
| 4 | Modules / lines / theorems | 95 / 34886 / 1686 |
| 5 | Axioms of every headline result | `[propext, Classical.choice, Quot.sound]` |

Peak resident set size for the whole-library build: 2784 MiB process-group PSS.

## Corrections to the plan

1. The plan's row 2 says `JungNets.Thm137` is "blocked on Iwamura's lemma, which
   Mathlib does not have". Mathlib still does not have it; it is no longer a
   blocker. What blocks Theorem 1.37 now is items 2–5 of the `JungNets`
   obstruction list (the retraction onto `A ∪ αᵒᵖ`, Proposition 1.22,
   interpolation, the `g_β` family) — item 1 is discharged.
2. The plan's "Expected outcome" table calls case 4 (streams 2 and 3) the least
   likely. Stream 2 landed in full. Whether case 4 is reached now depends only on
   stream 3, and stream 3's job got easier: it may assume a well-ordered index
   throughout and stop at `HasWellOrderedInfima`, never touching arbitrary chains
   or filtered sets.
3. The equivalence `Thm137Chains ↔ Thm137` means the round no longer has to
   choose between the two remainders. Both `JungNets.Thm137Chains` and
   `JungNets.Thm137` remain unproved, but they are the same proposition, so any
   proof of either discharges every theorem in `JungNets.lean` and, with
   Corollary 1.36, `thm18`.

## What a merge should check

* `ScottDomains/ScottDomains/Iwamura.lean` is a new module; nothing existing was
  edited, so no other module can regress. `JungNets.lean` is untouched — the new
  file imports it and adds to it from outside.
* `JungNets.lean`'s module docstring still says Iwamura's lemma "is not available
  here" (its Mathlib survey row, and the `HasChainInfima` docstring). That text is
  now stale. It is a comment, not a proof, so I left it alone rather than edit a
  file another stream may be holding; it should be corrected at merge.
* Commits on `agent2`: `3c434ca` (first landing) and `23d143d` (retarget at
  `Thm137Chains`). Not pushed, per the agent rule.
