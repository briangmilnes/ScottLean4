---
round: r0042
from: agent3
to: orchestrator
subject: bicomplete
date: 2026-0808-14:25
started: 2026-0808-13:58
finished: 2026-0808-14:25
related:
  - ScottDomains/plans/r0042-plan-from-orchestrator-to-orchestrator-clear-the-sorry.md
  - ScottDomains/ScottDomains/JungBicomplete.lean
  - ScottDomains/ScottDomains/JungNets.lean
---

# r0042, stream 3 — Jung's Theorem 1.37

One new module, `ScottDomains/ScottDomains/JungBicomplete.lean`, namespace
`ScottDomains.JungBicomplete`: 728 lines, 32 declarations, no `sorry`, no
`axiom`, no edit to any existing file.

## Headline: Corollary 1.3 is not needed, and is now proved for the chain case

The orchestrator's continuation asked whether the chain case can be reached
without Corollary 1.3, given stream 5's measurement that only
`JungNets.HasChainInfima` is ever spent. **It can, and the reduction is now
proved.** `exists_coinitial_isOrdinalCodirected`: every nonempty chain has a
*coinitial* subset that is well-ordered by `≥`. With
`lowerBounds_eq_of_coinitial` (coinitial subsets have the same lower bounds,
hence the same infima) this gives
`hasChainInfima_of_forall_isOrdinalCodirected` — `HasChainInfima D` follows from
the ordinal-codirected case alone.

The proof is elementary and uses no transfinite recursion. Well-order `D` by
`WellOrderingRel` (call it `≺`) and take
`C' = {b ∈ C | b is ≺-minimal in {d ∈ C | d ≤ c}, for some c ∈ C}`. Coinitiality
is immediate. For the well-ordering: given nonempty `S ⊆ C'`, its `≺`-minimal
element is its `≤`-greatest, by trichotomy of `≺` against minimality on both
sides.

**Totality of the chain is used exactly once** — to turn `s ≰ s₀` into `s₀ ≤ s` —
and that is precisely why the argument does not extend to filtered sets. It
cannot: the finite subsets of `ℝ` under `⊆` form a directed set with no cofinal
well-ordered subset, because a well-ordered chain of finite sets has length at
most `ω` and countable union. **That is what Iwamura's lemma is for.** Full
bicompleteness needs it; the chain case does not; and Theorem 18 asks only for
the chain case.

So agent2's stream is not on the critical path to `thm18`. It is still needed for
Jung's Theorem 1.37 *as stated* (bicomplete), which is a strictly stronger
conclusion than Theorem 18 consumes.

**The orchestrator's further inference does not hold.** The message suggested
that if the reduction is free then "the retraction onto `A ∪ αᵒᵖ`, Proposition
1.22 and the interpolation step may all be unnecessary". They are not. Those
three act *after* the reduction, on the ordinal-indexed net, which is still what
one has. What drops is Corollary 1.3 and nothing else. Concretely: a function
`f ≪ id_D` need not map the chain into itself, because `f γ` may land outside
`A ∪ αᵒᵖ`; forcing it back is the entire purpose of `D′`, and `g_β`'s
monotonicity at a point of `A` below a point of `αᵒᵖ` fails in `D` for the same
reason.

## Which ingredients landed

The plan's four absent ingredients, measured against what the module proves.

| # | Ingredient | Status | Declaration |
| -- | ---------- | ------ | ----------- |
| 1 | Corollary 1.3 | **proved for the chain case**, which is the only case Theorem 18 needs; Iwamura not used | `exists_coinitial_isOrdinalCodirected`, `hasChainInfima_of_forall_isOrdinalCodirected` |
| 2 | the retraction onto `A ∪ αᵒᵖ`, with its continuity | **partial** — `A ∪ αᵒᵖ` proved closed under least upper bounds, and the infimum proved to transfer back along `r`; the map `r : D → D′` not built | `isLUB_mem_union`, `isGLB_image_of_isGLB` |
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
no `f ≪ id_{D′}` maps `C` into itself, which is ingredient 5. Hypothesis (c) is
stated under `¬∃ i, IsGLB C i`, which the contradiction has in hand; that
weakening is not cosmetic, since Jung's successor `τ(γ) = γ + 1` is total only
because `αᵒᵖ` has no least element, and "no infimum" is what supplies that.

**`Thm137Chains` now factors as the retraction plus the `g_β` family, and
nothing else.**

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

## Five corrections to `JungNets.lean`'s obstruction list, from the source

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

5. **Jung's `r` is a closure, not a projection, and he never says so.**
   `JungNets.lean` item 2 calls it "the retraction onto `A ∪ αᵒᵖ`". His own
   formula gives more: off `A`, `r(x) = ⋀{γ ∈ αᵒᵖ | γ ≥ x}` is an infimum of
   *upper bounds of `x`*, so `r(x) ≥ x`; on `A` it is `x`. Hence
   `id_D ≤ i ∘ r` — the order dual of `Projection.lean`'s
   `IsEmbeddingProjectionPair`. This is not optional: without it a greatest lower
   bound computed in `D′` need not be one in `D`, and the whole proof would
   establish nothing about `D`. `isGLB_image_of_isGLB` proves the transfer from
   it in three lines. Any construction of `r` must deliver it.

The plan's paraphrase was otherwise accurate. One wording point: it says the
`x″, y″` pair has "no upper bound"; Jung says no upper bound **in `↡A`**, and the
restriction is load-bearing — without it correction 2 has nothing to convert.

## Measured build counts

`scripts/compile.sh -r r0042` (whole library),
log `ScottDomains/logs/compile-20260808-142244.agent3.log`:

| # | Metric | Value |
| -- | ------ | ----- |
| 1 | jobs | 1306 (up from 1299: the module now imports `Mathlib.SetTheory.Cardinal.Order` for `WellOrderingRel`) |
| 2 | lean diagnostics | 0 |
| 3 | lake errors | 0 |
| 4 | `sorry` declarations | 1 (`Skeleton/Section6.lean:196`, pre-existing, untouched) |
| 5 | other warnings | 0 |
| 6 | wall clock | 0:01.62 (incremental; the module itself elaborates in 829 ms) |
| 7 | peak PSS, process group | 1047 MiB |

`scripts/axioms.sh` over all seventeen substantive results: every one is on a
subset of `[propext, Classical.choice, Quot.sound]`.
`mapsTo_of_forall_not_upperBound` and `IsOrdinalCodirected.isChain` depend on
**no axioms at all**; `isContinuousDcpo_of_isAlgebraic`,
`IsContinuousDcpo.exists_wayBelow_wayBelow` and
`exists_isGLB_of_directedOn_wayBelowLower` on `propext` alone. `Classical.choice`
enters through `ScottHom`'s `SupSet` instance — which `ScottHom.lean` documents
as the price of a total `sSup` — and, in
`exists_coinitial_isOrdinalCodirected`, through the well-ordering theorem. The
second use is faithful to the source: Jung says of Theorem 1.2 that "the proof …
uses the Axiom of Choice".

## What remains between this and `Thm137Chains`

Two items, and no more.

1. **The retraction `r : D → D′`**, where `D′` carries `lowerBounds C ∪ C`. It
   must satisfy `r ∘ i = id_{D′}`, `id_D ≤ i ∘ r` (correction 5), correction 1's
   third case, and Scott continuity. What is already proved around it:
   `isLUB_mem_union` (`D′` is closed under least upper bounds, so it is a dcpo),
   `isGLB_image_of_isGLB` (the infimum transfers back), and `prop122`
   (`[D′ → D′]` is continuous once `r` exists). What is missing is the map, and
   the map is where the transfinite induction lives — the infimum `r` takes at a
   limit stage *is* the infimum the theorem is trying to produce, so the
   construction is a least-counterexample argument over `α`, not a definition.
   This is the expensive one and I judge it a round of its own.
2. **The `g_β` family**:
   `(¬∃ i, IsGLB C i) → ∀ f ≪ id_{D′}, ¬∀ γ ∈ C, f γ ∈ C`. It needs the successor
   `τ(γ) = γ + 1` along `C`, which is total exactly because `C` has no least
   element — which the `¬∃ glb` hypothesis supplies. It is a proof script over
   machinery item 1 builds, as `JungNets.lean` item 5 predicted.

Nothing in this round changes the plan's expected outcome for `sorry`: it stays
at 1 unless stream 4's bypass lands, or a later round builds item 1 and item 2.

## Recommendation for the next round

Both remaining items live over `D′ = A ∪ αᵒᵖ` and neither is separable from the
construction of that type. **They are one stream, not two**, and the stream's
first task is the type `D′` with its `CompletePartialOrder` instance, on which
`isLUB_mem_union` is already the mathematical content. Agent2's Iwamura stream
should be re-scoped or stood down for `thm18`'s sake: it is needed only for
Jung's Theorem 1.37 as stated, and stream 5 has measured that Theorem 18 does not
consume that statement.

## Deviation from the assignment

The brief ranked acceptance as (1) Theorem 1.37 from Corollary 1.3, (2) the
retraction and Proposition 1.22, (3) the retraction alone, (4) a written
obstruction. That ranking assumed Corollary 1.3 was someone else's and the
retraction was the cheap first target; both turned out to be wrong. Corollary 1.3
is free for the case that matters and is proved here; the retraction is the most
expensive ingredient, not the cheapest, because it is not a definition. What
landed is Corollary 1.3 for chains, Proposition 1.22 and interpolation in full,
two of the retraction's three obligations, the entire endgame paragraph, and a
written obstruction on what is left.
