---
round: r0036
from: agent1
to: orchestrator
subject: theorem-14
date: 2026-0807-08:51
started: 2026-0807-08:37
finished: 2026-0807-08:51
related:
  - plans/r0036-plan-from-orchestrator-to-agent1-theorem-14.md
  - plans/r0036-plan-from-orchestrator-to-orchestrator-five-way-open-results.md
---

# r0036 stream 1 — Theorem 14, proved

Acceptance level **1** of the plan's ranked list: `thm14` is proved in both
directions and its `sorry` is removed. No new `sorry` was introduced.

## Measurements

| # | Quantity | Before | After | Measured by |
| -- | -------- | ------ | ----- | ----------- |
| 1 | `sorry` in the development | 2 | **1** (`Skeleton/Section6.lean:197`, `thm18` — agent2's stream) | `scripts/counts.sh` |
| 2 | Build jobs | 1137 | **1138** | `scripts/compile.sh -r r0036` |
| 3 | Lean diagnostics (errors) | 0 | **0** | same |
| 4 | Lake errors | 0 | **0** | same |
| 5 | Non-`sorry` warnings | 0 | **0** | same |
| 6 | Modules / lines / theorems | 61 / 19497 / 906 | **62 / 19995 / 928** | `scripts/counts.sh` |
| 7 | Wall / peak RSS (replay) | — | 1.30 s, 810 MiB single-process | `compile-20260807-085119.agent1.log` |
| 8 | Axioms of `thm14` | — | `propext, Classical.choice, Quot.sound` — **no `sorryAx`** | `scripts/axioms.sh` |

Full-build log: `ScottDomains/logs/compile-20260807-085119.agent1.log`.
Axioms were also printed for `SFP.thm14_forward`, `SFP.thm14_converse`,
`SFP.range_normalHom_of_finite`, `SFP.exists_greatest_of_finite`,
`SFP.isFinitaryProjection_const_bot` and `SFP.range_toFp_eq`; all six carry the
same three axioms and none carries `sorryAx`.

## Where the code went

One new module, `ScottDomains/ScottDomains/SFP.lean` (487 lines, namespace
`ScottDomains.SFP`, 21 theorems). `Skeleton/Recovered.lean` gains one
`import` line and a six-line proof of `thm14`; its `thm14` docstring is rewritten
from the four-gap obstruction into the four-gap outcome. No other Lean file is
touched. `INDEX.md` and `docs/PaperInventory.md` row 4.5 are updated.

`Recovered.lean` continues to read as statements rather than proofs: the proof
lives in `SFP.lean`, matching the arrangement r0034 used for Lemma 9 under
`ScottDomains.Isomorphism`.

## The four gaps: two real, two false constraints

| # | Gap (r0034's wording) | Outcome | Declaration |
| -- | -------------------- | ------- | ----------- |
| 1 | the `FpLattice` section is stated at `[Domain α]`, which the forward direction must conclude | **false constraint** | — |
| 2 | `Set.range ⇑(toFp hN) = N` for finite normal `N` | **real, proved** | `SFP.range_normalHom_of_finite`, `SFP.range_toFp_eq` |
| 3 | `IsLUB` in `↥(Fp α)` is weaker than `IsLUB … ScottHom.id` | **false constraint** | — |
| 4 | two finite-combinatorial lemmas | **real, proved** | `SFP.exists_upperBound_of_finite_subset`, `SFP.exists_greatest_of_finite` |

### Gap 2 — proved, and finiteness is exactly what it needs

`p_N(x) = ⨆(N ∩ ↓x)`. For finite `N` the set `N ∩ ↓x` is finite, nonempty
(`⊥ ∈ N` by Lemma 4.3) and directed (`IsNormalIn.directedOn_inter_Iic`), so by
gap 4(a) it contains its own greatest element, which is therefore its supremum
and lies in `N`. Hence `im(p_N) ⊆ N`; the reverse is `normalFun_of_mem`.

For infinite `N` the statement is **false** — the supremum of an infinite
directed subset of `N` escapes `N` — and only `im(p_N) ∩ K(D) = N` survives,
which is the existing `range_normalHom_inter_compacts`. The bridge is stated at
`[CompletePartialOrder α] [IsAlgebraic α]`; the `toFp` form additionally needs
`[Domain α]` only because `toFp` does.

### Gap 4 — proved as one lemma with a corollary

4(b) is the general statement: a finite subset of a nonempty directed set has an
upper bound *inside the set* (`exists_upperBound_of_finite_subset`, induction on
the finite subset). 4(a) is that lemma applied to `t := s`
(`exists_greatest_of_finite`). A third form, `exists_mem_isLUB_of_finite`,
packages the greatest element as an `IsLUB`, which is what both call sites use.

### Gap 1 — the constraint does not bind

The forward direction never touches `toFp`, `fpBasis` or
`Fp.le_iff_fpBasis_subset`. Every one of those speaks about the basis coordinate
`im(p) ∩ K(D)`, and on a **finite** image `im(p) ∩ K(D) = im(p)` — because a
projection of finite image has `im(p) ⊆ K(D)`
(`SFP.isCompactElement_of_mem_range_of_finite`, which is the paper's own
sentence). So the whole forward argument runs on `im(p)` inside `D` with no
basis coordinate at all, and the `[Domain α]` binder is never reached.

The measurement the plan asked for — whether the four `FpLattice` declarations
survive at `[CompletePartialOrder α]` — is therefore moot for Theorem 14, and the
answer is **no** independently: `toFp hN` is `⟨normalHom hN, isFinitaryProjection_normalHom hN⟩`,
and `isFinitaryProjection_normalHom` spends `Domain.countable_compacts` on
`countable_compacts_range_normalHom`, the basis of `im(p_N)`. Weakening it would
require weakening `IsFinitaryProjection` itself, which asserts `im(p)` is a
*domain*. `fpBasis_isNormalIn`, `fpMeetFamily_isNormalIn` and `fpMeet_isNormalIn`
already carry `omit [Domain α]`, so the section's `variable` is not uniformly
load-bearing — but the four declarations gap 1 named are.

### Gap 3 — the constraint does not arise

Leastness of `ScottHom.id` above `M` is not transferred from `↥(Fp α)`; it is
proved in `ScottHom α α` directly (`SFP.isLUB_id_of_normalHom_mem`). Given an
upper bound `b` of `M` and `x : D`, for each compact `k ⊑ x` let `⟨k⟩` be the
least normal subposet of `K(D)` containing `k`, finite by `normalClosure_finite`
(this is the one place the Plotkin condition is spent). Then `p_⟨k⟩ ∈ M`,
`k ⊑ p_⟨k⟩(x)` by `le_normalFun`, and `p_⟨k⟩ ⊑ b`, so `k ⊑ b x`. Algebraicity
lifts this to `x = ⨆(K(D) ∩ ↓x) ⊑ b x`. Nothing in the argument mentions
`↥(Fp α)`.

## Where the plan and the r0034 docstring were incomplete

**One hypothesis neither names: `M` must be nonempty.** `IsCompactElement`
quantifies over *nonempty* directed sets, and the forward direction applies it to
`{p x | p ∈ M}`. Mathlib's `DirectedOn` holds vacuously on `∅`, so the paper's
"directed" — which asks every finite subset, including `∅`, for an upper bound
*in the set* — is not recovered from `IsBifiniteViaProjections`'s second
conjunct. Without nonemptiness the forward direction is not provable as stated
from the three conjuncts alone; one must either add it or case-split on `M = ∅`
(which forces `D` to be a one-point cpo).

The fix is a positive lemma rather than a case split:
`SFP.isFinitaryProjection_const_bot` proves that the constant-`⊥` map is a
finitary projection — its image is the one-point cpo `{⊥}`, whose single element
is compact and whose basis is countable — and `SFP.range_const_bot_finite` that
its image is finite. So `ScottHom.const ⊥ ∈ M` always, and `M` is the paper's
directed set in the paper's sense.

**Everything else in the plan checked out against the source.** I read
PDF pages 30–31 of `papers/Gunter Scott 1990.pdf` directly
(`scripts/extract-thm14-pages.sh`, which is committed). The definition of
bifinite and the statement of Theorem 14 are exactly as
`docs/StatementRecovery.md` recovered them. The paper additionally supplies its
own sketch of the forward direction three sentences above the theorem —

> … whenever `p : D → D` is a finitary projection and `im(p)` is finite, then
> `im(p) ⊆ K(D)`. From this, together with the fact that the set `M` is directed
> and `⨆M = id`, it is possible to show `D` is a domain with `⋃{im(p) | p ∈ M}`
> as its basis.

— and `SFP.thm14_forward` follows it step for step. The plan's claim that the
forward direction is "the cheap half" is confirmed by the more useful measure:
the forward direction spends **no** hypothesis it does not conclude, whereas the
converse spends `[Domain α]` and the Plotkin condition at four separate points
(`normalClosure_isNormalIn`, `normalClosure_finite` twice, and
`Domain.countable_compacts`). By source lines the two are comparable —
`SFP.lean:259–326` (68 lines) forward against `SFP.lean:401–483` (83 lines)
converse.

Two smaller corrections. `docs/PaperInventory.md` row 4.5 described Theorem 14 as
"equivalent characterizations of an (algebraic/BC) domain"; the theorem is two
items about *bifiniteness*, and `docs/StatementRecovery.md` §3.2 had already said
so. The row is rewritten. And the plan's gap-2 statement
`Set.range ⇑(toFp hN) = N` is proved, but the load-bearing form is the one a step
below it, `Set.range ⇑(normalHom hN) = N`, which needs only `[IsAlgebraic α]`.

## Declaration inventory of `ScottDomains.SFP`

| # | Declaration | Hypotheses | What it is |
| -- | ----------- | ---------- | ---------- |
| 1 | `exists_upperBound_of_finite_subset` | `[Preorder α]` | gap 4(b) |
| 2 | `exists_greatest_of_finite` | `[Preorder α]` | gap 4(a) |
| 3 | `exists_mem_isLUB_of_finite` | `[Preorder α]` | 4(a) as an `IsLUB` |
| 4 | `isCompactElement_of_mem_range_of_finite` | `[CompletePartialOrder α]` | the paper's `im(p)` finite ⟹ `im(p) ⊆ K(D)` |
| 5 | `range_subset_compacts_of_finite` | `[CompletePartialOrder α]` | 4 as a set inclusion |
| 6 | `range_inter_compacts_of_finite` | `[CompletePartialOrder α]` | `im(p) ∩ K(D) = im(p)` on a finite image — why gap 1 dissolves |
| 7 | `eq_of_range_eq` | `[CompletePartialOrder α]` | a projection is determined by its image |
| 8 | `isProjection_const_bot` | `[CompletePartialOrder α]` | |
| 9 | `eq_bot_of_mem_range_const_bot` | `[CompletePartialOrder α]` | |
| 10 | `range_const_bot_finite` | `[CompletePartialOrder α]` | |
| 11 | `isFinitaryProjection_const_bot` | `[CompletePartialOrder α]` | `M.Nonempty`'s witness |
| 12 | `thm14_forward` | `[CompletePartialOrder α]` | Theorem 14, `1 → 2` |
| 13 | `range_normalHom_of_finite` | `[CompletePartialOrder α] [IsAlgebraic α]` | **gap 2** |
| 14 | `le_normalHom_of_range_subset` | `[CompletePartialOrder α] [IsAlgebraic α]` | `⊑` in the function space — why gap 3 dissolves |
| 15 | `range_toFp_eq` | `[CompletePartialOrder α] [Domain α]` | gap 2 in `Fp(D)` coordinates |
| 16 | `range_eq_fpBasis_of_finite` | `[CompletePartialOrder α] [Domain α]` | the two finiteness conditions coincide |
| 17 | `isFinitaryProjection_and_finite_normalHom` | `[CompletePartialOrder α] [Domain α]` | membership supply for the converse |
| 18 | `countable_of_subset_finiteImage` | `[CompletePartialOrder α] [Domain α]` | `M` countable |
| 19 | `directedOn_of_normalHom_mem` | `[CompletePartialOrder α] [Domain α]` | `M` directed |
| 20 | `isLUB_id_of_normalHom_mem` | `[CompletePartialOrder α] [Domain α]` | `⨆M = id`, **gap 3** |
| 21 | `thm14_converse` | `[CompletePartialOrder α] [Domain α]` | Theorem 14, `2 → 1` |

`thm14_forward` and `thm14_converse` are stated against a *characterization* of
the paper's `M` (`hM : ∀ p, p ∈ M ↔ IsFinitaryProjection p ∧ (Set.range ⇑p).Finite`)
rather than against `finiteImageProjections`, so `SFP.lean` does not import
`Skeleton/Recovered.lean`, which imports it. `Recovered.thm14` discharges `hM`
with `fun _ => Iff.rfl`.

## Namespace check

Every new declaration is under `ScottDomains.SFP`. Grepped against the round
plan's list of existing namespaces (`Isomorphism`, `ClosureProperties`, `Dyadic`,
`Combinator`, `CombinatorRep`, `BifiniteUniversal`, `PRepresentable`,
`Section62`, `Universality`, `Recursive`, `Hoare`, `Smyth`, `Plotkin`,
`IdealCompletion`, `ContinuousAlgebra`, `PowerdomainBC`): no collision. The
orchestrator's composition check (`scripts/axioms.sh -i` over every new module
together) is still worth running against agents 2–5.

## Commits on `agent1`

| # | Commit | Contents |
| -- | ------ | -------- |
| 1 | `4b8f4a6` | `ScottDomains/SFP.lean`, `scripts/extract-thm14-pages.sh` |
| 2 | `9c5da4f` | `Skeleton/Recovered.lean` with `thm14` proved, build logs |
| 3 | this one | `INDEX.md`, `docs/PaperInventory.md` row 4.5, this report |

Not pushed — "no tracking information" is the expected outcome for an agent.

## What this leaves for the round

`docs/PaperInventory.md` row 6 still reads "**2**, in 2 files: `thm14` … and
`thm18`". I did not edit it, to avoid a merge conflict with agent2's stream,
which owns the other half of that sentence. Rows 2, 2c, 2d, 5 and 6 are the
orchestrator's per the round plan; the measured input for them is the table at
the top of this report. If agent2's stream also lands, `sorry` reaches **0** and
numbered results complete reaches **24 of 29**.
