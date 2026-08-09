---
round: r0045
from: agent5
to: orchestrator
subject: discharge-jung137
date: 2026-0808-21:30
started: 2026-0808-21:20
finished: 2026-0808-21:30
related:
  - plans/r0045-plan-from-orchestrator-to-orchestrator-discharge-nineteen.md
  - reports/r0044-report-from-agent6-to-orchestrator-undischarged-defs.md
---

# r0045 agent5 — Jung's Theorem 1.37: 3 of 3 discharged

All three claims in this stream are now proved by theorems whose conclusion is the
claim and which carry **zero proof hypotheses beyond instance binders** — agent6's
own detection rule, re-run below and confirming it. New module:
`ScottDomains/ScottDomains/A5Thm137.lean`, namespace `ScottDomains.R45.Agent5`,
305 lines, no `sorry`, footprint `[propext, Classical.choice, Quot.sound]`
throughout.

| # | claim | status | theorem | instance binders | footprint |
| -- | ----- | ------ | ------- | ---------------- | --------- |
| 1 | `JungNets.Thm137` | **discharged** | `R45.Agent5.thm137` | `[CompletePartialOrder D] [Domain D]` | `[propext, Classical.choice, Quot.sound]` |
| 2 | `JungNets.Thm137Chains` | **discharged** | `R45.Agent5.thm137Chains` | `[CompletePartialOrder D] [Domain D]` | `[propext, Classical.choice, Quot.sound]` |
| 3 | `PropertyM.Thm137Omega` | **discharged** | `R45.Agent5.thm137Omega` | `[CompletePartialOrder D] [IsAlgebraic D]` | `[propext, Classical.choice, Quot.sound]` |

## The plan's first instruction: the Iwamura composition does **not** close

The plan told me to check, before anything else, whether
`Iwamura.thm137Chains_of_wellOrderedInfima` composed with an existing
well-ordered-infima result discharges `Thm137Chains`. **It does not, and no such
composition is possible from the current tree.** Measured, not inferred:

    grep -rn "HasWellOrderedInfima" ScottDomains/ScottDomains/

returns five source occurrences, all in `Iwamura.lean`: the `def` and four
*consumers* (`hasChainInfima_of_hasWellOrderedInfima`,
`isBicomplete_of_hasWellOrderedInfima`, `thm137Chains_of_wellOrderedInfima`, and
one docstring). **There is no producer** — nothing in the package proves
`Iwamura.HasWellOrderedInfima D` for any `D`, nor
`IsAlgebraic (ScottHom D D) → Iwamura.HasWellOrderedInfima D`. Iwamura's lemma
`exists_chain_directed_cover` and Markowsky's theorem
`hasChainSuprema_iff_hasDirectedSuprema` are both proved, but they convert
*between* completeness hypotheses; neither manufactures one. The `Iwamura.lean`
cluster is a complete reduction chain with an empty left end.

The plan's line numbers are also stale — `HasWellOrderedInfima` is at `:563` not
`:558`, `hasChainInfima_of_hasWellOrderedInfima` at `:576`, and
`thm137_of_thm137Chains` at `:614`; the built `.ilean` disagrees with the plan by
about ten lines in each case. Names checked against the built `.olean` by
`#print axioms`, which is what the discharges below actually use.

**So the round's cheapest win was not where the plan said it was.** It was one file
away, in `PropertyM.lean`.

## What actually discharges the three claims

The route does not go through Iwamura's lemma, `HasWellOrderedInfima`, Jung's
transfinite retraction onto `A ∪ αᵒᵖ`, or his Proposition 1.22. It goes through
`PropertyM.hasOmegaOpBoundsAbove_pair` — **Spreen 2005's Lemma 5.8**, already
proved in the tree, carrying no hypothesis on `D` beyond `IsAlgebraic (ScottHom D D)`.

### The observation

For `c ⊆ D` write `compactLowerBounds c = {k | IsCompactElement k ∧ k ∈ lowerBounds c}`.
In an algebraic dcpo, `sSup (compactLowerBounds c)` is the infimum of `c` **as
soon as that set is directed**, and both halves are one line of algebraicity
(`isGLB_sSup_compactLowerBounds`, which depends on *no axioms at all*):

* it is a lower bound, because every `w ∈ c` is an upper bound of
  `compactLowerBounds c`;
* it is the greatest, because a lower bound `w` has
  `compactsBelow w ⊆ compactLowerBounds c` and `IsAlgebraic.isLUB_compactsBelow`
  makes `w` the least upper bound of the smaller set.

Directedness is therefore the entire content, and Spreen's lemma **is** a
directedness statement: given compact `k₁, k₂` below every term of a descending
sequence, it produces `z` above both and still below every term;
`exists_mem_upperBounds_of_directedOn` on `compactsBelow z` — the step
`PropertyM.hasCompleteMub_of_countable` already uses at `:349` — converts `z` into
a *compact* `q`. That is `exists_compact_upperBound_le`.

### Claim 3, with no countability at all

`PropertyM.Thm137Omega D` quantifies over sequences already indexed by `ℕ`, so
Spreen's lemma applies directly:

    theorem thm137Omega (D : Type*) [CompletePartialOrder D] [IsAlgebraic D] :
        PropertyM.Thm137Omega D

Note what this says about `PropertyM.lean`'s own module docstring, line 133: it
claims "the `ωᵒᵖ` condition is a theorem here and not a hypothesis," but what was
proved there is `HasOmegaOpBoundsAbove {a₁, a₂}` — *some* lower bound of the
sequence, relative to one pair. `HasOmegaOpInfima D` — an actual greatest lower
bound of an arbitrary antitone sequence — was **not** proved, and `Thm137Omega`
sat undischarged as a result. The gap between the two is closed by the directed
supremum above; the docstring was one implication ahead of the file.

### Claims 2 and 1: countability replaces Iwamura

For a chain of arbitrary order type the descending sequence has to be
manufactured. Jung does this by well-ordering the chain in order type `|D|`,
which is why the cluster was thought to need Iwamura's lemma. Over a countable
basis it is done by **counting the constraints instead**
(`exists_countable_subset_compactLowerBounds`):

for each compact `k` that is *not* a lower bound of `c`, keep one witness `w ∈ c`
with `¬ k ≤ w`. There are at most `|K(D)|` such `k`, so the resulting `c₀ ⊆ c` is
countable — and a compact element below every member of `c₀` is below every member
of `c`, since otherwise its own witness would be in `c₀` and refute it. So `c₀` has
**the same compact lower bounds as `c`**, and `compactLowerBounds c` is directed as
soon as `compactLowerBounds c₀` is. `PropertyM.minPrefix` of an enumeration of `c₀`
is a descending `ω`-sequence coinitial in it (`PropertyM.minPrefix_le`, the only
step that uses the chain hypothesis), and Spreen's lemma applies to that. Hence

    theorem thm137Chains (D : Type*) [CompletePartialOrder D] [Domain D] :
        JungNets.Thm137Chains D
    theorem thm137      (D : Type*) [CompletePartialOrder D] [Domain D] :
        JungNets.Thm137 D

`thm137` is `thm137Chains` followed by `Iwamura.thm137_of_thm137Chains`, the order
dual of Markowsky's theorem — so the `Iwamura.lean` machinery *is* used, but for
the upgrade from chains to filtered sets, not for the part the plan expected.

## The honest caveat: what is **not** proved

The instance binders are a real strengthening over the claims' own signatures,
which carry only `[CompletePartialOrder D]`. Stated plainly:

| # | setting | status |
| -- | ------- | ------ |
| 1 | `[Domain D]` — `ω`-algebraic cpo, countable basis | Theorem 1.37 **proved** |
| 2 | `[IsAlgebraic D]`, uncountable basis | only the `ωᵒᵖ` form (`thm137Omega`) proved |
| 3 | `D` merely continuous — **Jung's own hypothesis** | open |

**Jung's Theorem 1.37 in full generality is still open.** An algebraic dcpo with an
uncountable basis gets claim 3 and not claims 1–2; a continuous, non-algebraic
dcpo gets none of the three, because every argument here runs on `K(D)`.
`Iwamura.thm137Chains_of_wellOrderedInfima` remains the exact statement of what a
general proof still owes, and it should not be deleted.

This is not a weakening of any claim's statement (plan shape 3): the `def`s are
untouched and the theorems conclude them verbatim. It is the instance-binder
allowance in agent6's rule being used, and the orchestrator should record *which*
instances, because `[Domain D]` is strictly more than `[CompletePartialOrder D]`.
In mitigation: `[Domain D]` and `[Domain (ScottHom D D)]` are exactly the
hypotheses of Gunter & Scott's Theorem 18 and of `ScottDomains.Thm18`'s own
`variable` line, so every consumer in the development is covered.

## Correction to the plan: `Thm137Omega` is not a by-product of Theorem 18

The plan says `PropertyM.Thm137Omega` is "one of the two weakenings the route to
Theorem 18 spends," and instructs me to check whether the closed Theorem 18
discharges it as a by-product. **Both halves are wrong, measured against
`PropertyM.lean`.** The live route is
`PropertyM.thm18_of_cor136` → `forall_hasCompleteMub` → `hasCompleteMub_pair` →
`hasCompleteMub_pair_of_countable` + `hasOmegaOpBoundsAbove_pair`. It spends
`HasOmegaOpBoundsAbove` at a pair, never `HasOmegaOpInfima`, and therefore spends
**neither** `Thm137Omega` nor `Thm137Chains` — the section is titled "Property m at
pairs, unconditionally" and its docstring says so at `:797`. `lemma217_of_omega`,
`propertyM_pairs_of_omega` and `forall_hasCompleteMub_of_omega` are the theorems
that consume `Thm137Omega`, and all three were superseded by their unconditional
counterparts in the same file. Theorem 18 closing was consequently no evidence
about this claim either way.

## Cross-check that the discharge is strong enough for the assembly

`Thm18.thm18_of_thm137Chains_and_cor136` was written against `Thm137Chains α` as an
open hypothesis. Feeding it `thm137Chains` gives

    theorem thm18_of_cor136_via_thm137Chains {α} [CompletePartialOrder α]
        [Domain α] [Domain (ScottHom α α)]
        (hcor : JungFinite.FixedPointOfCompactDeflationIsCompact α) : IsBifinite α

which reproduces `PropertyM.thm18_of_cor136` by the *other* route. This is a
consistency check, not a new result: it makes the kernel confirm that the
`Thm137Chains` discharged here is strong enough to drive the Theorem 18 assembly
five rounds built around it, and not merely strong enough for its own statement.

## Axioms

`docs/AxiomFootprint.md` records that this cluster genuinely needs choice because
Iwamura well-orders a directed set in order type `|D|`. **That justification no
longer applies to these three theorems** — nothing here well-orders anything. The
footprint is nonetheless `[propext, Classical.choice, Quot.sound]`, from three
smaller uses: the decidability branch in `PropertyM.minPrefix`, the witness
selection (`choose!`) in `exists_countable_subset_compactLowerBounds`, and
`Classical.choice` inside Spreen's lemma. Choice is not avoidable here and was not
fought; only the *reason* recorded in `AxiomFootprint.md` is now narrower, and the
orchestrator may want to amend that note.

| # | declaration | footprint |
| -- | ----------- | --------- |
| 1 | `R45.Agent5.thm137` | `[propext, Classical.choice, Quot.sound]` |
| 2 | `R45.Agent5.thm137Chains` | `[propext, Classical.choice, Quot.sound]` |
| 3 | `R45.Agent5.thm137Omega` | `[propext, Classical.choice, Quot.sound]` |
| 4 | `R45.Agent5.isBicomplete` | `[propext, Classical.choice, Quot.sound]` |
| 5 | `R45.Agent5.thm18_of_cor136_via_thm137Chains` | `[propext, Classical.choice, Quot.sound]` |
| 6 | `R45.Agent5.hasChainInfima` | `[propext, Classical.choice, Quot.sound]` |
| 7 | `R45.Agent5.hasOmegaOpInfima` | `[propext, Classical.choice, Quot.sound]` |
| 8 | `R45.Agent5.directedOn_compactLowerBounds_of_isChain` | `[propext, Classical.choice, Quot.sound]` |
| 9 | `R45.Agent5.directedOn_compactLowerBounds_range` | `[propext, Classical.choice, Quot.sound]` |
| 10 | `R45.Agent5.exists_countable_subset_compactLowerBounds` | `[propext, Classical.choice, Quot.sound]` |
| 11 | `R45.Agent5.exists_compact_upperBound_le` | `[propext, Classical.choice, Quot.sound]` |
| 12 | `R45.Agent5.isGLB_sSup_compactLowerBounds` | **no axioms** |
| 13 | `R45.Agent5.compactLowerBounds_nonempty` | **no axioms** |

No `sorryAx` anywhere; agent6's `SORRYUSER` stream is empty (0 lines) and its
`AXIOM` stream is empty.

## Measurements

| # | measurement | value |
| -- | ----------- | ----: |
| 1 | `scripts/compile.sh -r r0045`, full package | 1340 jobs, exit 0 |
| 2 | errors | 0 |
| 3 | warnings | 0 |
| 4 | `sorry` | 0 |
| 5 | new module lines | 305 |
| 6 | new declarations (1 `def`, 13 theorems) | 14 |
| 7 | build wall clock, incremental (this module only) | 0.71 s |
| 8 | claims discharged of 3 assigned | 3 |

Agent6's detector re-run on the built environment
(`scripts/a6-env-scan.sh`) reports, in its `PROPDEF` `uncond` column, `1` for each
of the three, with these `PROVEDBY` records at hypothesis count 0:

    PROVEDBY  ScottDomains.JungNets.Thm137Chains    ScottDomains.R45.Agent5.thm137Chains  0
    PROVEDBY  ScottDomains.PropertyM.Thm137Omega    ScottDomains.R45.Agent5.thm137Omega   0
    PROVEDBY  ScottDomains.JungNets.Thm137          ScottDomains.R45.Agent5.thm137        0

`TOTALS 3704 2652 731 1881 88 194`.

## For the orchestrator

1. Nothing in this stream touches a file outside `A5Thm137.lean`, so a merge
   conflict is possible only on a name clash. Every new name is under
   `ScottDomains.R45.Agent5`; the only common word is `compactLowerBounds`, which
   does not occur elsewhere in the package.
2. `PropertyM.lean:133`'s claim that "the `ωᵒᵖ` condition is a theorem here" was
   an overstatement by one implication (see claim 3 above). It is now true. The
   docstring is not mine to edit.
3. `docs/AxiomFootprint.md`'s justification for choice in this cluster now names a
   mechanism these theorems do not use. The footprint is unchanged; the reason
   should be narrowed.
4. `Iwamura.thm137Chains_of_wellOrderedInfima` should stay: it is now the precise
   statement of the uncountable-basis and continuous-dcpo cases, which remain open.
