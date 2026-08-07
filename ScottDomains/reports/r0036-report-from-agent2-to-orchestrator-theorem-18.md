---
round: r0036
from: agent2
to: orchestrator
subject: theorem-18
date: 2026-0807-09:20
started: 2026-0807-08:43
finished: 2026-0807-09:20
related:
  - plans/r0036-plan-from-orchestrator-to-agent2-theorem-18.md
  - plans/r0036-plan-from-orchestrator-to-orchestrator-five-way-open-results.md
---

# r0036 stream 2 — Theorem 18 — steps 2 and 3 landed

Branch `agent2`, two commits: `70f708e` (step 2) and `ccecaa5` (step 3). One new
module, `ScottDomains/ScottDomains/JungSFP.lean`, 888 lines, 29 top-level
declarations (22 theorems, 6 definitions, 1 structure), all under namespace
`ScottDomains.JungSFP`. No existing file was modified except `INDEX.md`.

## Measurement

| # | Quantity | Before | After |
| -- | -------- | ------ | ----- |
| 1 | `sorry` in `ScottDomains/` | 2 — `Skeleton/Recovered.lean:257`, `Skeleton/Section6.lean:196` | **2 — the same two** |
| 2 | `sorry` introduced by this stream | — | **0** |
| 3 | Build jobs | 1137 | **1138** |
| 4 | Build errors | 0 | **0** |
| 5 | Non-`sorry` warnings | 0 | **0** |
| 6 | Diagnostics | 0 | **0** |
| 7 | Wall / peak RSS, full replay build | — | 1.82 s / 1714 MiB single, 2517 MiB tree |

Measured by `scripts/compile.sh -r r0036`, log
`ScottDomains/logs/compile-20260807-091314.agent2.log`. `thm18` at
`Skeleton/Section6.lean:196` is **not** discharged; nothing in `Skeleton/` was
touched.

Axiom audit, `scripts/axioms.sh -i ScottDomains.JungSFP` over `lemma213`,
`thm214`, `lemma217`, `isCompactElement_of_minimal_upperBounds`,
`minimal_upperBounds_of_mem_minimalUpperBounds`,
`exists_mem_minimalUpperBounds_le`, `minimal_upperBounds_jungHom`: every one
depends on `[propext, Classical.choice, Quot.sound]` and on nothing else. No
`sorryAx`. These are formally verified in the kernel sense.

## Which of the five steps closed

| # | Step | Jung's number | Status after this stream |
| -- | ---- | ------------- | ------------------------ |
| 1 | `[D → D]` continuous ⟹ `K(D)` has property m | Theorem 1.37 | absent — now an **explicit hypothesis** of `lemma217`, not a `sorry` |
| 2 | `[D → D]` algebraic ⟹ bifinite **or** algebraic L-domain | Lemma 2.13, Theorem 2.14 | **closed** — `lemma213`, `thm214` |
| 3 | `[D → D]` ω-algebraic ⟹ `K(D)` has property M | Lemma 2.17 | **closed** — `lemma217` |
| 4 | property M ⟹ `U^∞(A)` finite | Lemma 2.2 | unchanged: middle and last parts in `Section62.lean`; Rado's Selection Theorem and Corollary 1.36 still missing |
| 5 | property m + `U^∞` finite ⟹ bifinite | Theorem 1.32 | already proved — `isBifinite_iff_mubClosure` |

The plan's ranked acceptance list asked for item 3 (step 2 alone) as the
fallback. Steps 2 **and** 3 landed, which is item 2's first two thirds; step 4
was not attempted and step 1 is out of reach for the reason given below, so item
2 is not fully met and item 1 (`thm18` proved) is not met.

## What the proof needed that the development did not have

Not a new tactic — a missing lemma about the *relativized* minimal upper bounds
the development already had. `minimalUpperBounds A u` is minimality inside `A`,
because that is what §6 needs (`A = K(D)`). Every one of Jung's minimality
arguments applies the minimality of some `b ∈ mub(A)` to a bound that is **not**
known to be compact — a value `h d` of an arbitrary continuous function, an
arbitrary member of a directed set, an arbitrary `d` in the top region of `f_A`.
Three theorems close that gap, and they are the file's foundation:

* `isCompactElement_of_minimal_upperBounds` — Jung's Proposition 1.9, for
  `IsAlgebraic` rather than for continuous dcpos;
* `minimal_upperBounds_of_mem_minimalUpperBounds` — minimal in `K(D)` implies
  minimal in `D`, for a finite set of compacts;
* `mem_minimalUpperBounds_of_minimal` — the converse.

Monotonicity of Jung's `f_A` is false without the second of these. That is the
mechanical reason the earlier rounds could not get past step 2's construction.

The other reusable piece is `jungFun x₁ x₂ a₁ a₂ t` with the predicate
`IsJungPatch`. Jung's `g`, `f_A` and `f_S` are the *same* function on three of
their four regions; abstracting the fourth region as `t` means the monotonicity
and Scott-continuity case analysis is written once and instantiated four times
(`g`, `f_A`, the constant-`c` least upper bound, and `f_S`). `IsJungPatch`'s
fourth field, `attained`, is where each instance does its own work.

## Which uncountable family, and why

Jung's `2 ^ mub{a₁,a₂}`-indexed `f_S`, not Spreen's `ω ^ ω`-indexed variant and
not Smyth's (of which only the conclusion is attested). `Section62.lean` is right
that no family is canonical, so the choice is an engineering one and it was made
on cost: `f_S` is `jungFun` with `t_S d = if ∃ s ∈ S, s ≤ d then b₁ else b₂`, so
its continuity proof is *already paid for* by step 2 — the only new obligations
are the four `IsJungPatch` fields, and three of the four are two lines. Its
injectivity is a single evaluation at a point of `S`. Spreen's `ω ^ ω` indexing
would need a chain construction and its own continuity argument for no gain: the
cardinality contradiction is the same either way. The contradiction itself is
`Function.cantor_surjective` against `Domain.countable_compacts`, routed through
`Set.Infinite.natEmbedding` and `Function.invFun_surjective`; no `Cardinal`
arithmetic was needed.

Countability is spent exactly once, in `lemma217`, as the plan required. Neither
`lemma213` nor `thm214` mentions it, and neither should — Theorem 2.14 is the
purely algebraic bifurcation and holds with no cardinality hypothesis. r0031's
(★) was not reintroduced; nothing in the file quantifies over deflations.

## Where the source contradicted the plan, and where it did not

The plan is accurate on the mathematics. Three points where reading the PDF
changed what got written, none of which contradicts the plan's conclusions:

1. **Jung's Theorem 2.10 is not needed at all, in either direction.** The plan
   says step 2 "needs `IsLDomain` defined, which the development does not have".
   Reading Jung's proof of Lemma 2.17 shows the *only* consequence of "algebraic
   L-domain" he ever uses is his condition (vii) — "any element above both `a₁`
   and `a₂` is above exactly one element of `mub(A)`". So the file defines
   `HasTwoMubBelow` (the failure of (vii)) and `HasAtMostOneMubBelow` (its
   negation) and never introduces `IsLDomain` or the principal-ideal-lattice
   definition. This is what lets steps 2 and 3 be `sorry`-free: formalizing
   `IsLDomain` would have forced Theorem 2.10's six equivalences, none of which
   the route to Theorem 18 passes through. The cost is a naming one, recorded in
   the module docstring: `thm214`'s second disjunct is (vii)-minus-existence, not
   the literature's "algebraic L-domain", and it says so.
2. **`lemma213` concludes "not algebraic", where Jung concludes "not
   continuous".** Algebraic implies continuous, so the formalized statement is
   the weaker one — and it is the one `thm214` and Theorem 18 consume. The
   weakening costs nothing: continuity enters Jung's proof at exactly one place,
   Proposition 1.9, and that is proved here for `IsAlgebraic` directly.
3. **Step 3 genuinely needs step 1, and the plan's step table understates the
   coupling.** Jung's Lemma 2.17 does not assume property m; he cites
   Theorem 1.37. Property m is what makes `f_S` monotone — uniqueness alone gives
   "at most one" minimal upper bound below `d`, and monotonicity needs "exactly
   one", i.e. existence too. So `lemma217` carries
   `HasCompleteMub (compacts D) {a₁, a₂}` as an explicit hypothesis. Per the
   plan's rule 9 this is an obstruction in the statement and the docstring, not a
   `sorry`.

## What now stands between this and `thm18`

Four named items, in the order they would be attacked:

1. **Step 1, Jung's Theorem 1.37** — "a dcpo with continuous function space is
   bicomplete". This is not a proof script over the present API and should not be
   scheduled as one. Jung's proof runs over ordinal-indexed codirected nets
   (his Corollary 1.3), uses interpolation in a continuous dcpo, and builds a
   retraction onto `A ∪ αᵒᵖ` (his Proposition 1.22). Nothing in `ScottDomains/`
   quantifies over any of that. It is the largest single remaining item.
2. **Jung's Lemma 1.29** — property M for pairs and for `∅` implies property M
   for every finite set, by the inductive construction
   `M_{i+1} = ⋃_{x ∈ M_i} mub{x, a_{i+1}}`. `lemma217` produces the pair case;
   this converts it to the form `isBifinite_iff_mubClosure` consumes. Estimated
   at one finite-set induction plus a minimality argument — the cheapest of the
   four, and the natural next task for this stream.
3. **Step 4, Jung's Lemma 2.2** — needs Rado's Selection Theorem (his
   Theorem 2.1, proved by Tychonoff on `∏ A_i`) and his Corollary 1.36. The
   middle and last parts are already in `Section62.lean`.
4. **The assembly**, which is then three lines through
   `isBifinite_iff_mubClosure`.

Recommendation for the merge: `JungSFP.lean` is standalone — it imports only
`MinimalUpperBounds` and `StepFunction` and nothing imports it, so it cannot
break another stream. The composition check the round plan calls for
(`scripts/axioms.sh -i` over every new module at once) should still be run; the
only names this file introduces at top level are inside
`ScottDomains.JungSFP`, and the four generic ones (`jungFun`, `fVal`, `sVal`,
`IsJungPatch`) do not occur anywhere else in the development.
