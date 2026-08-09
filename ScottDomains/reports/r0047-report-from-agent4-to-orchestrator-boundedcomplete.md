---
round: r0047
from: agent4
to: orchestrator
subject: boundedcomplete
date: 2026-0809-12:25
started: 2026-0809-12:05
finished: 2026-0809-12:25
related:
  - plans/r0047-plan-from-orchestrator-to-orchestrator-close-the-seven.md
---

# r0047 agent4 — `[BoundedComplete β]` removed from `lem17_fun`

## Outcome

**Outcome 1 — removed.** `[BoundedComplete β]` is gone from Lemma 17's
function-space conjunct, from its strict twin, and from the two declarations
underneath them (`IsAlgebraic (ScottHom α β)`, `Domain (ScottHom α β)`) that
carry the same binder for the same reason. Every removal is kernel-checked, and
each is paired with a theorem showing the binder-free statement implies the one
the development already has, so the bar was not lowered.

`Lemma30AtV`'s conjuncts 1–2 are **not** reachable from this alone. The plan's
reduction is incomplete; the correction is section 3.

## What was removed, and how

`ClosureProperties.lean:54` attributes the binder to Theorem 7's step-function
decomposition. Measured: `lem17_fun`'s only consumer of `[BoundedComplete β]` is
`ScottHom.exists_finite_isLUB_of_isCompactElement`, whose only consumer of it is
`directedOn_finiteJoinsBelow` — one lemma, one use, in `CompactFunction.lean:89`.

The replacement is Gunter & Scott's own §6.2 argument, which names the finitary
projections `(q, p)(f) = q ∘ f ∘ p` and never decomposes a compact function.
`ScottDomains/A4Lemma17Fun.lean` builds, for each `f : D → E`, the set

    approx f = { (p_{N₂}, p_{N₁})(f) | N₁ ◁ K(D), N₂ ◁ K(E) finite }

and proves it nonempty, directed and `IsLUB (approx f) f`. The least-upper-bound
step (`isLUB_approx`) is the whole content and it spends **algebraicity of `D`
and of `E`** — nothing else. A compact `f` is therefore fixed by some finite
normal pair, and the fixing is inherited by every larger pair, which is what lets
one pair serve a whole finite set of compacts.

Nothing in the new proof mentions `stepFun`, `IsStepPair` or `stepsBelow`.

| # | declaration | old binders | new binders |
| - | ----------- | ----------- | ----------- |
| 1 | `ClosureProperties.lem17_fun` | `[Domain α] [Domain β] [BoundedComplete β]` | `[Domain α] [Domain β]` |
| 2 | `ClosureProperties.lem17_strictFun` | same | `[Domain α] [Domain β]` |
| 3 | `ClosureProperties.exists_finite_projection_fixing` | same | `[Domain α] [Domain β]` |
| 4 | `IsAlgebraic (ScottHom α β)` (`FunctionSpaceDomain.lean:121`) | same | `[Domain α] [Domain β]` |
| 5 | `Domain (ScottHom α β)` (`FunctionSpaceCountable.lean:122`) | same | `[Domain α] [Domain β]` |
| 6 | `PRepFun.strictHomDomain` | same | `[Domain α] [Domain β]` |

Rows 1–3 are `A4Lemma17Fun.lean`; rows 4–6 are `A4FunctionSpaceBifinite.lean`.
In every row the removed instance binder is replaced by *nothing* — the two
`IsBifinite` hypotheses were already present in rows 1–3, and rows 4–6 gain them
as explicit hypotheses, which is strictly weaker than `[BoundedComplete β]` for
the carriers at issue (`V` is bifinite and, under `Thm29SecondAtDomains`, not
bounded complete). Rows 4–6 are theorems, not instances, so no diamond is
created: `Domain` is `Prop`-valued and the existing instances are untouched.

Row 4's proof is `approx f ⊆ compactsBelow f` plus `isLUB_approx`; row 5's is
that every compact is `(p_{N₂}, p_{N₁})(f)` for a finite normal pair, so
`K(D → E)` is a countable union of finite projection images indexed by the finite
subsets of the countable `K(D)` and `K(E)`.

**No existing declaration was edited.** All 27 new declarations are in
`ScottDomains.R47.Agent4`.

## 3. Correcting the plan: conjuncts 1–2 have a second, different obstruction

The plan states that conjuncts 1–2 "reduce to removing `[BoundedComplete β]` from
`lem17_fun`". Re-derived from the tree, that is **wrong**: there are two
independent bounded-completeness obligations on conjunct 1 and Lemma 17 supplies
only one.

| # | obligation | source | status after this round |
| - | ---------- | ------ | ----------------------- |
| 1 | `Retracts (ScottHom V V)` | `LemThirty.retracts_fun_of_boundedComplete`, `[BoundedComplete V]` from `lem17_fun` | **removed** — `A4RepArrow.retracts_fun_V` |
| 2 | `IsPRepresentable₂ V funOp` from that pair | `PRepFun.rep_arrow`, `[BoundedComplete U]` | **reduced**, not removed |

Obligation 2 is not Lemma 17's, and `PRepFun.lean:269` says where it lives: the
`[BoundedComplete U]` of `rep_arrow` is spent in exactly one place,
`PRepFun.domain_range_compHom`, which needs `Domain (im p → im q)` for the two
finitary projections indexing the conjugating family and gets it from
`PRep.boundedComplete_range`.

`A4RepArrow.lean` replaces that route with row 5 above and carries the
replacement through both conjuncts. What is left is exactly one proposition:

    FpImagesBifinite U : ∀ p : Fp U, IsBifinite (FpImage p).carrier

— every finitary-projection image of `U` is bifinite. This is Plotkin's closure
of the bifinite domains under projections. Measured over every module, **no
declaration in this development concludes `IsBifinite` of a projection image**,
and the general statement is not a formality: the argument does not go through by
transporting a finite normal subposet along `p`, because `p a ≤ x` does not give
`a ≤ x`, and the "directed family of finite-image maps below the identity"
argument needs those maps idempotent, which `q ∘ p_i ∘ q` is not.

The trade is nonetheless a strict improvement, and the reason is agent5's:
`{Thm29SecondAtDomains, BoundedComplete V}` is contradictory
(`not_thm29SecondAtDomains_and_boundedComplete_V`), so conjuncts 1–2 could not be
*repaired* the way `⊗`, `+` and `⊕` were in r0045 — repairing lands on the
contradictory pair. They needed the route replaced, which is what
`retracts_fun_V` and `retracts_strictFun_V` do: they take `Thm29SecondAtDomains`
and carry **no bounded-completeness binder at all**. Whether `V` is bounded
complete no longer bears on conjuncts 1–2 in either direction, which is why the
`Ainf` stage-3 minimal-upper-bound witness, valuable as it is for agent5's
unconditional `¬ BoundedComplete V`, is no longer on the critical path for this
item.

**Answer to the round's question: conjuncts 1–2 are reachable from
`Thm29SecondAtDomains` + `FpImagesBifinite V`, and from nothing weaker that this
round found.** Before this round they were reachable only from a hypothesis set
now known to be contradictory.

## 4. Declarations added, with axiom footprints

All 27 depend on `[propext, Classical.choice, Quot.sound]` and on no other axiom.
No `sorryAx` anywhere; the package is at `sorry 0`.

`ScottDomains/A4Lemma17Fun.lean` (12): `compHom_mono`, `approx`,
`approx_nonempty`, `directedOn_approx`, `isLUB_approx`, `exists_fixing`,
`exists_normal_fixing`, `approx_subset_compactsBelow`,
`exists_finite_projection_fixing`, `lem17_fun`, `lem17_strictFun`,
`lem17_fun_imp_old`, `lem17_strictFun_imp_old`.

`ScottDomains/A4FunctionSpaceBifinite.lean` (8): `isAlgebraic_scottHom`,
`fixedBy`, `finite_fixedBy`, `countable_compacts_scottHom`, `domain_scottHom`,
`domain_strictHom`, `isAlgebraic_scottHom_imp_old`, `domain_scottHom_imp_old`.

`ScottDomains/A4RepArrow.lean` (9): `FpImagesBifinite`,
`domain_range_compHom_of_bifinite`, `rep_arrow_of_fpImagesBifinite`,
`domain_range_strictArrowFamily_of_bifinite`,
`rep_strictArrow_of_fpImagesBifinite`, `retracts_fun_V`, `retracts_strictFun_V`,
`rep_fun_V`, `rep_strictFun_V`.

None of these is a discharge-at: the four `*_imp_old` theorems are the only ones
carrying an added instance binder, and their purpose is precisely to record that
the binder-free statements imply the old ones.

## 5. Build

`scripts/compile.sh -r r0047` over the whole package: **1359 jobs, exit 0, zero
errors, zero warnings, `sorry 0`** (`logs/compile-20260809-122157.agent4.log`).

## 6. For the next round

1. `FpImagesBifinite V` — bifiniteness of finitary-projection images of a
   bifinite domain. One proposition, and it is the *only* thing between
   `Thm29SecondAtDomains` and conjuncts 1–2 of `Lemma30AtV`.
2. `PaperInventory.md` row 569 records Lemma 17 as over-hypothesized on five
   conjuncts; two of those five (`→`, `⇸`) are now measured, not conjectured.
3. `LemThirty.retracts_fun_of_boundedComplete` and
   `retracts_strictFun_of_boundedComplete` are now superseded by
   `retracts_fun_V` / `retracts_strictFun_V`. They are left in place — only
   agent3 was authorized to change a `def` this round, and these are theorems the
   orchestrator may want to retire deliberately.
