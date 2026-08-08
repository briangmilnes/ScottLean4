---
round: r0042
from: agent3
to: orchestrator
subject: bicomplete
date: 2026-0808-14:15
started: 2026-0808-13:58
finished: 2026-0808-14:15
related:
  - ScottDomains/plans/r0042-plan-from-orchestrator-to-orchestrator-clear-the-sorry.md
  - ScottDomains/ScottDomains/JungBicomplete.lean
  - ScottDomains/ScottDomains/JungNets.lean
---

# r0042, stream 3 — Jung's Theorem 1.37, taking Corollary 1.3 as a hypothesis

One new module, `ScottDomains/ScottDomains/JungBicomplete.lean`, namespace
`ScottDomains.JungBicomplete`: 600 lines, 28 declarations, no `sorry`, no
`axiom`, no edit to any existing file.

## Which ingredients landed

The plan's four absent ingredients, measured against what the module proves.

| # | Ingredient | Status | Declaration |
| -- | ---------- | ------ | ----------- |
| 1 | Corollary 1.3 (agent2's) | not attempted, per the assignment | — |
| 2 | the retraction onto `A ∪ αᵒᵖ`, with its continuity | **half** — `A ∪ αᵒᵖ` proved closed under least upper bounds, so it is a sub-dcpo; the map `r : D → D′` not built | `isLUB_mem_union` |
| 3 | **Proposition 1.22** | **proved** | `prop122`, over `IsContinuousDcpo.of_retractPair` and `IsRetractPair.sandwichHom` |
| 4 | interpolation (Proposition 1.8) | **proved** | `IsContinuousDcpo.exists_wayBelow_wayBelow` |
| 5 | the `g_β` family | not proved; it is the sole remaining hypothesis of the endgame theorem | — |

Beyond the four, one result the plan did not ask for and did not anticipate:

| # | Result | Declaration |
| -- | ------ | ----------- |
| 6 | **the entire second paragraph of Jung's proof** — from "Assume now that the infimum of `αᵒᵖ` does not exist" to "so by construction `αᵒᵖ` is mapped into itself under `f`" | `exists_isGLB_of_forall_not_mapsTo` |

`exists_isGLB_of_forall_not_mapsTo` is stated over an abstract dcpo `D′` covered
by `lowerBounds C ∪ C`, and its hypotheses are exactly (a) `D′` continuous, (b)
`[D′ → D′]` continuous — which `prop122` delivers from the retraction — and (c)
no `f ≪ id_{D′}` maps `C` into itself, which is ingredient 5. So the whole of
Theorem 1.37 now factors as **Corollary 1.3 + the retraction + the `g_β` family**,
with nothing else missing between them.

Supporting results, all new to the development:

* `IsContinuousDcpo` — the predicate for a continuous dcpo. `JungNets.lean`
  records its absence as the reason `Thm137` is stated with the stronger
  `IsAlgebraic (ScottHom D D)` in place of Jung's "continuous function space".
* `isContinuousDcpo_of_isAlgebraic`, and `isContinuousDcpo_scottHom_of_isAlgebraic`
  — the bridge showing `Thm137`'s antecedent discharges the `hFS` hypothesis of
  `prop122` and of the endgame theorem exactly, with no further deviation.
* `IsContinuousDcpo.of_retractPair` — a retract of a continuous dcpo is
  continuous, in the retraction–embedding-pair form Proposition 1.22 needs.
* `sandwich`, `sandwichHom` — `f ↦ r ∘ f ∘ i` as an element of
  `[[D → D] → [E → E]]`. `Skeleton/Lemma17.lean`'s `compFun` is the endomorphic
  special case and cannot be reused: Proposition 1.22 needs the sandwich to
  change the type.
* `IsOrdinalCodirected` — "`αᵒᵖ`" as a property of a *set*: every nonempty subset
  has a greatest element. `.isChain` confirms it forces a chain.
* `exists_isGLB_of_directedOn_wayBelowLower` — Jung's "Then the set `↡A` cannot
  be directed", contraposed.
* `mapsTo_of_forall_not_upperBound` — his "so by construction `αᵒᵖ` is mapped
  into itself under `f`". Needs only monotonicity; no completeness, no `f ≪ id`.

## Four corrections to `JungNets.lean`'s obstruction list, from the source

Read off pp. 18, 31 and 50–51 of the Jung PDF, not from the plan.

1. **Jung's retraction `r` is not total as written, for a reason r0037 did not
   record.** `JungNets.lean` item 2 says `⋀{γ ∈ αᵒᵖ | γ ≥ x}` needs a transfinite
   induction to exist. There is a second, independent defect: **that set is empty**
   whenever `x` is not below the chain's largest element. `αᵒᵖ`'s largest element
   is `s(0)` — the ordinal `0` is `αᵒᵖ`-greatest and `s` is monotone — so any
   `x ≰ s(0)` has `{γ ∈ αᵒᵖ | γ ≥ x} = ∅`, and a dcpo has no `⋀∅` without a top.
   Such an `x` is also not in `A`, so it falls in Jung's second case. His
   two-case formula needs a third. The obvious repair (send those `x` to `s(0)`)
   keeps `r` monotone but has to be checked for continuity separately.

2. **What interpolation buys is specific, and the plan does not say it.**
   `JungNets.lean` item 4 records interpolation as "applied twice". Its actual
   and only role is to convert *no upper bound of `{x″, y″}` in `↡A`* — which is
   what non-directedness of `↡A` yields — into *no upper bound of `{x′, y′}` in
   `A`*, which is what the final step consumes. Nothing else in the proof needs
   it. That conversion is step 5 inside `exists_isGLB_of_forall_not_mapsTo`.

3. **Proposition 1.22's "hence a continuous dcpo" is not Proposition 1.16.**
   Prop 1.16 is about `im(r)` for a retraction `r : D → D` on one dcpo; Prop 1.22
   needs it for a retract `E` given by a retraction–embedding pair between two.
   `IsContinuousDcpo.of_retractPair` proves the pair form directly rather than
   transporting 1.16 across an isomorphism, which would have cost more.

4. **Jung's "If `A` is empty this is trivially the case" branch is vacuous in
   this development.** `A = lowerBounds C` and `CompletePartialOrder` extends
   `OrderBot`, so `⊥ ∈ A` always. The orchestrator's brief repeated Jung's
   "possibly empty"; here it never is. The branch is kept in the quoted proof for
   fidelity and is never taken.

The plan's paraphrase was otherwise accurate. One wording point: it says the
`x″, y″` pair has "no upper bound"; Jung says no upper bound **in `↡A`**, and the
restriction is load-bearing — without it correction 2 has nothing to convert.

## Measured build counts

`scripts/compile.sh -r r0042` (whole library),
log `ScottDomains/logs/compile-20260808-141444.agent3.log`:

| # | Metric | Value |
| -- | ------ | ----- |
| 1 | jobs | 1299 |
| 2 | lean diagnostics | 0 |
| 3 | lake errors | 0 |
| 4 | `sorry` declarations | 1 (`Skeleton/Section6.lean:196`, pre-existing, untouched) |
| 5 | other warnings | 0 |
| 6 | wall clock | 0:01.54 (incremental; the module itself elaborates in 757 ms) |
| 7 | peak PSS, process group | 986 MiB |

`scripts/axioms.sh` over all twelve substantive results: every one is on a subset
of `[propext, Classical.choice, Quot.sound]`. `mapsTo_of_forall_not_upperBound`
and `IsOrdinalCodirected.isChain` depend on **no axioms at all**;
`isContinuousDcpo_of_isAlgebraic`, `IsContinuousDcpo.exists_wayBelow_wayBelow`
and `exists_isGLB_of_directedOn_wayBelowLower` on `propext` alone.
`Classical.choice` enters only through `ScottHom`'s `SupSet` instance, which
`ScottHom.lean` documents as the price of a total `sSup`.

## What remains between this and Theorem 1.37

Three items, in the order a later round would take them.

1. **Corollary 1.3** (agent2). Reduces bicompleteness to infima of sets that are
   well-ordered by `≥` — that is, to `IsOrdinalCodirected` sets. Until it lands,
   nothing here applies to an arbitrary filtered set.
2. **The retraction `r : D → D′`**, with correction 1's third case, and its
   continuity. `isLUB_mem_union` gives the sub-dcpo; what is missing is the map,
   and the map is where the transfinite induction lives — the infimum `r` takes
   at a limit stage *is* the infimum the theorem is trying to produce, so the
   construction is a least-counterexample argument over `α`, not a definition.
   This is the largest of the three and I judge it a round of its own.
3. **The `g_β` family**: `∀ f ≪ id_{D′}, ¬∀ γ ∈ C, f γ ∈ C`. It needs the
   successor `τ(γ) = γ + 1`, so it needs `C` indexed by the ordinal and not
   merely `IsOrdinalCodirected`. It is a proof script over machinery items 1 and
   2 supply, exactly as `JungNets.lean` item 5 predicted.

Item 2 remains the plan's correct judgement of where the cost is. Nothing in this
round changes the plan's expected outcome for `sorry`: it stays at 1 unless
stream 4's bypass or the other streams land.

## Deviation from the assignment

The brief ranked acceptance as (1) Theorem 1.37 from Corollary 1.3, (2) the
retraction and Proposition 1.22, (3) the retraction alone, (4) a written
obstruction. What landed is Proposition 1.22 and interpolation in full, half the
retraction, the entire endgame paragraph, and a written obstruction on the
retraction's remaining half — that is above (3) and below (2), plus item 6, which
the ranking did not contemplate and which is the larger part of the proof body.
Ordering the ranking by the retraction turned out to mis-rank the work: the
retraction is the most expensive ingredient, not the cheapest, because it is not
a definition.
