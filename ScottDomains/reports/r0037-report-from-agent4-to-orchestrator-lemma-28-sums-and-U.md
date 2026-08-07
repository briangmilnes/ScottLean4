---
round: r0037
from: agent4
to: orchestrator
subject: lemma-28-sums-and-U
date: 2026-0807-11:43
started: 2026-0807-11:14
finished: 2026-0807-11:43
related:
  - plans/r0037-plan-from-orchestrator-to-agent4-lemma-28-sums-and-U.md
  - plans/r0037-plan-from-orchestrator-to-orchestrator-last-four.md
---

# r0037 stream 4 — Lemma 28 at §7.3's `U`, and the two sum conjuncts

Branch `agent4`, four commits, all in `ScottDomains/ScottDomains/PRepSum.lean`
(1076 lines, namespace `ScottDomains.PRepSum`) plus a two-paragraph docstring
correction in `PRep.lean`.

## Result against the ranked acceptance list

**Acceptance level 2 reached** — `Lemma28AtU` derived, plus `+` and `⊕`. Level 1
was not reached: `()♯` and `()♭` were not attempted, for the reason in section 5.

| # | Item | Status |
| - | ---- | ------ |
| 1 | `PRepSum.pairAtU` — Theorem 27 in `PRep`'s `(fn, gr)` shape | proved |
| 2 | `PRepSum.repProdAtU` — conjunct 3, `×`, at `Dyadic.U`, no hypothesis | proved |
| 3 | `PRepSum.repSepSumAtU` — conjunct 5, `+`, at `Dyadic.U`, no hypothesis | proved |
| 4 | `PRepSum.repCoalSumAtU` — conjunct 6, `⊕`, at `Dyadic.U`, no hypothesis | proved |
| 5 | `PRepSum.repLiftAtU` — conjunct 7, `(·)⊥`, at `Dyadic.U`, no hypothesis | proved |
| 6 | `PRepSum.lemma28AtU_of` — `Lemma28AtU` from what remains | proved, arity 5 |
| 7 | `PRep.lean:114–119` stale obstruction | corrected |

Lemma 28 over the paper's own carrier stands at **4 of 9 conjuncts with no
hypothesis**, up from 0. `lemma28AtU_of`'s arity fell from 9 to 5; the five
still open are `→`, `⇸`, `⊗`, `(·)♯`, `(·)♭`.

## 1. Build, measured

| # | Quantity | Value |
| - | -------- | ----- |
| 1 | Build | `Build completed successfully (1218 jobs).` |
| 2 | Lake errors | 0 |
| 3 | Diagnostics | 0 |
| 4 | Non-`sorry` warnings | 0 |
| 5 | `sorry` | 1 — `Skeleton/Section6.lean:197` (`thm18`), pre-existing, unchanged |
| 6 | Modules / lines / theorems | 67 / 24682 / 1181 (from 66 / 23596 / 1119) |
| 7 | Axioms on every new headline result | `[propext, Classical.choice, Quot.sound]` — no `sorryAx` |

Axioms checked with `scripts/axioms.sh` on `pairAtU`, `repProdAtU`, `repLiftAtU`,
`repCoalSumAtU`, `repSepSumAtU`, `rep_coalSum`, `rep_sepSum`, `coalSumCongr`,
`isAlgebraic_coalescedSum`, `domain_coalescedSum` and `lemma28AtU_of`.

Builds were run only through `scripts/compile.sh -r r0037`; nine runs, logs in
`ScottDomains/logs/compile-20260807-11*.agent4.log`.

## 2. The headline: did `Lemma28AtU` go through as expected?

**Yes, and it was cheaper than the plan implied — the whole instantiation is one
transposition plus one instance per operator, and it compiled on the first
attempt.**

`Atomless.thm27 V` produces `∃ e p, ScottHom.IsEmbeddingProjectionPair e p` with
`e : V → U` and `p : U → V`, which unfolds to `∀ x, p (e x) = x` and
`∀ y, e (p y) ≤ y`. `PRep`'s scheme wants `fn : U → V`, `gr : V → U` with
`fn ∘ gr = id` and `gr ∘ fn ⊑ id`. Setting `fn := p`, `gr := e` matches the two
conditions **in order, with no adjustment**; `pairAtU` is that four-line proof.

The only real content per conjunct is meeting Theorem 27's condition: the
operator's *result* must be a bounded complete domain. That is exactly Lemma 10,
already proved in this development, so **Lemma 10 and Lemma 28 compose** — Lemma
10 puts the operator's value inside the class Theorem 27 quantifies over,
Theorem 27 returns the retraction pair, and `PRep`'s scheme turns the pair into a
representation. Each `AtU` theorem is four lines:

| # | Operator | `Domain` of the result | `BoundedComplete` of the result |
| - | -------- | ---------------------- | ------------------------------- |
| 1 | `×` | `PowerdomainRep.domain_prod` | `lem10_prod` |
| 2 | `+` | `domain_coalescedSum` (new, section 4) | `ClosureProperties.lem10_separated` |
| 3 | `⊕` | `domain_coalescedSum` (new, section 4) | `lem10_sum` |
| 4 | `(·)⊥` | `ClosureProperties.liftDomain` | `lem10_lift` |

`PRep.lean`'s two stale passages are corrected: the module docstring now carries
a dated correction naming `Atomless.thm27` and `Atomless.isNormallyRepresented_compacts`
and pointing at `PRepSum`, and `rep_lift`'s docstring no longer claims the
instantiation is unavailable. No other line of `PRep.lean` was touched, so the
diff against agent3's `PRepFun` work is two docstring hunks.

## 3. The source, read directly

Page 42 of `Gunter Scott 1990.pdf` rendered at 600 dpi and read as an image
(`scripts/pdf-render.sh`, `scripts/pdf-crop.sh` — both reused from r0036; no new
script was written, per the r0036 collision rule). Lemma 28's operator line reads

> `→, ∘→, ×, ⊗, +, ⊕, (·)⊥, (·)♯, (·)♭`

— nine operators, `♯` and `♭` and **no `♮`**, and `∘→` (the strict function space)
present. This is an independent re-measurement and it **agrees** with r0036's
reading and with `PRep.Lemma28`'s nine conjuncts. `pdftotext` on the same page
returns `!, !, , ; +, ; ()?, ()], ()[` — both function-space arrows collapse to
`!`, `×` `⊗` `⊕` vanish, and `⊥ ♯ ♭` become `? ] [`.

The same page also states the representation scheme, written out for `+`:

> To get a representation for `+`, take a pair of continuous functions
> `Φ₊ : U → (U + U)`, `Ψ₊ : (U + U) → U` such that `Φ₊ ∘ Ψ₊ = id` and
> `Ψ₊ ∘ Φ₊ ⊑ id`. Then take `R₊(r, s) = Ψ₊ ∘ (r + s) ∘ Φ₊`.

`PRep.isPRepresentable₂_of_repFamily` is that displayed formula with `(Φ₊, Ψ₊)`
abstracted to `(fn, gr)`, so `rep_sepSum` is the paper's own construction with
the pair supplied rather than assumed. **The source confirmed the plan on every
point this stream touched**; unlike r0034 and r0036, I have no correction to
report.

## 4. The closure property the library was missing

`agent5`'s cross-stream message arrived mid-task and is **confirmed**:
`IsAlgebraic (CoalescedSum A B)` is proved nowhere in the development. The
coalesced sum carries Lemma 10 (`lem10_sum`, bounded completeness) and Lemma 17
(`lem17_sum`, bifiniteness) and nothing else, because §4.5 and §6.2 are the only
closure properties the paper states for it.

This is a real gap and it is on the critical path: `IsPRepresentable` routes
through `IsFinitaryProjection`, whose second component is a `Domain` on the
operator's image, and `Domain` is `IsAlgebraic` plus a countable basis.

**I closed it rather than assuming it.** `PRepSum.isAlgebraic_coalescedSum` and
`PRepSum.domain_coalescedSum` are new. The argument is a case split on `WithBot`
and on the side of the injection, resting on `Skeleton/Sum.lean`'s
`isCompactElement_coe_inl_iff` — `↑(inl x)` is compact in `A ⊕ B` exactly when
`x` is compact in `A` — so the compact approximants of `↑(inl x)` are the
injections of the non-`⊥` compact approximants of `x`, plus the adjoined bottom.
The one delicate step is the bottom the injections do not carry, handled by
`Skeleton/Sum.lean`'s `isLUB_diff_bot`. Countability is an inclusion into
`{⊥} ∪ inl(K A) ∪ inr(K B)`.

`+` inherits it rather than routing around it, exactly as agent5 predicted:
`ClosureProperties.SeparatedSum A B` **is** `CoalescedSum (WithBot A) (WithBot B)`,
so `domain_coalescedSum` composed with the `liftDomain` instance is what makes
`repSepSumAtU` go through. No algebraicity obligation is carried as a hypothesis
anywhere in this file, and no `sorry` was introduced.

`Smash` was not touched; if it is likewise never proved algebraic, that blocks
`⊗` for agent3 the same way, and the fix is the same shape as
`isAlgebraic_coalescedSum`.

## 5. Conjunct by conjunct

| # | Operator | Conjunct | Status | Where |
| - | -------- | -------- | ------ | ----- |
| 1 | `+` | `IsPRepresentable₂ U sepSumOp` | **proved**, abstract and at `U` | `rep_sepSum`, `repSepSumAtU` |
| 2 | `⊕` | `IsPRepresentable₂ U coalSumOp` | **proved**, abstract and at `U` | `rep_coalSum`, `repCoalSumAtU` |
| 3 | `(·)♯` | `IsPRepresentable U smythOp` | **not attempted** — see below | — |
| 4 | `(·)♭` | `IsPRepresentable U hoareOp` | **not attempted** — see below | — |

### `⊕` — the r0034 refutation does not transfer, and that is now checked

r0034's three-chain counterexample refutes `⊕` at the **closure** notion, where
the operator satisfies `id ⊑ r` and nothing forces `r ⊥ = ⊥`, so the two
summands' bottoms get glued to different points. A projection satisfies
`r ⊥ ⊑ ⊥`, hence `r ⊥ = ⊥` (`isStrict_of_isProjection`, one line). That makes
`r ⊕ s` the copairing `[inl ∘ r, inr ∘ s]`, whose continuity
`Isomorphism.copair` already supplies — the file exists for exactly this
universal property and had no other customer. **The notion was the obstruction,
not the operator.**

The five obligations and what discharged each:

| # | Obligation | Discharged by |
| - | ---------- | ------------- |
| 1 | `r ⊕ s` continuous | `Isomorphism.copair` (reused unchanged) |
| 2 | `r ⊕ s` a projection | `isProjection_coalSumMap` — three cases, 12 lines |
| 3 | `im(r ⊕ s) ≅ im(r) ⊕ im(s)` | `coalSumRangeOrderIso` — new, ~90 lines |
| 4 | `im(r ⊕ s)` a domain | `domain_range_coalSumMap` through `domain_coalescedSum` |
| 5 | continuity in the `Fp(U)` index | `isLUB_coalSumFamily`, spending `PRep.isFinitaryProjection_sSup` |

### `+` — cheapest of the four, as the plan predicted, and for the plan's reason

Nothing in the `+` conjunct is a new construction. §4.4 *defines*
`D + E = D⊥ ⊕ E⊥`, and `SeparatedSum` is an `abbrev` recording that as an
equation between cpos, so `sepSumFamily q` is literally
`coalSumMap (liftFamily q.1) (liftFamily q.2)` — the `⊕` family at the lifted
maps — and each obligation composes a `⊕` fact with a `(·)⊥` fact already in
`PRep`:

| # | Obligation | `⊕` half | `(·)⊥` half |
| - | ---------- | -------- | ----------- |
| 1 | projection | `isProjection_coalSumMap` | `PRep.isProjection_liftMap` |
| 2 | monotone in `(r, s)` | `coalSumMap_mono` | `PRep.liftFamily_mono` |
| 3 | `im` a domain | `domain_range_coalSumMap` | `PRep.domain_range_liftMap` |
| 4 | range isomorphism | `coalSumRangeOrderIso` then `coalSumCongr` | `PRep.liftRangeOrderIso` |
| 5 | index continuity | `scottContinuous_sumInl` | `PRep.isLUB_liftFamily` |

The one piece row 4 needed and nothing supplied is `coalSumCongr`: the coalesced
sum carries an order isomorphism of each summand, because an order isomorphism
preserves the least element and therefore carries the punctured copy to the
punctured copy. This is what lets `im(r⊥) ≅ (im r)⊥` compose with the coalesced
range isomorphism. `rep_sepSum` compiled on the first attempt.

`ClosureProperties.lem10_separated` obtains `+` for Lemma 10 by the same
composition, so this is the second time the paper's definition of `+` has paid
for itself in this development.

### `()♯` and `()♭` — the obstruction, stated precisely

Not attempted, and the reason is **not** the one `CombinatorRep.lean` records
and not the one my own r0036 finding cleared.

r0036 established that `smythOp` and `hoareOp` are functions `Cpo → Cpo` — the
`[Domain D]` in `Powerdomain/Hoare.lean` is spent on `IdealCompletion.instDomain`
and not on the type — so both conjuncts are *statable*. That is still correct,
and agent5 is right that the `Domain` on the result is free from Theorem 11.
Neither fact touches what representability needs.

Measured: **the development defines no action of a map on either powerdomain.**
`grep` over `ScottDomains/` for `smythMap`, `hoareMap`, `Powerdomain.map`,
`powerdomainMap`, `Smyth.map`, `Hoare.map` returns nothing, and
`ClosureProperties/Powerdomain.lean` contains only `lem17_hoare`, `lem17_smyth`
and `lem17_plotkin` — three statements about a single `D`. The representation
scheme needs a conjugating family `C : Fp(U) → ScottHom (D♯) (D♯)`, and there is
no `r ↦ r♯` to build it from.

Constructing one runs into a question this development has not settled. The
powerdomain is `IdealCompletion (Pf ↥(compacts D))`, so the natural induced map
acts on finite sets of **compacts**, which needs `p(K(D)) ⊆ K(D)`.
`IsFinitaryProjection` does not obviously supply that: `IsProjection.isCompactElement_iff`
says the compacts of `im(p)` are the image points compact in `D`, which is a
statement about points already in the image and says nothing about where `p`
sends a compact of `D`. I did not establish either that it holds or that it
fails, and I am not asserting either — I am recording that this is the step to
settle first, and that it is the real content of the two conjuncts rather than
anything about `Cpo` or `Domain`. An alternative route through
`IdealCompletion.thm11_converse` (`D ≃o IdealCompletion K(D)`) exists and was not
explored.

This is well beyond the plan's 120–180 line estimate for these two, and starting
it would have produced an uncommittable half-build rather than a fifth conjunct.

## 6. Files touched

| # | File | Change |
| - | ---- | ------ |
| 1 | `ScottDomains/ScottDomains/PRepSum.lean` | new, 1076 lines, namespace `ScottDomains.PRepSum` |
| 2 | `ScottDomains/ScottDomains/PRep.lean` | two docstring hunks; no declaration changed |
| 3 | `ScottDomains/logs/compile-20260807-11*.agent4.log` | nine build logs |

One import was added to reach `Isomorphism.copair`
(`import ScottDomains.Isomorphism.Copair`); it imports only `StrictHom` and
`CoalescedSum`, so no cycle.

No script was written. `scripts/pdf-render.sh` and `scripts/pdf-crop.sh` were
reused as they stand.

## 7. Commits

| # | SHA | Content |
| - | --- | ------- |
| 1 | `61413d5` | `Lemma28AtU` unblocked: `pairAtU`, `repProdAtU`, `repLiftAtU`, `lemma28AtU_of`; `PRep.lean` docstring corrected |
| 2 | `6268643` | `isAlgebraic_coalescedSum`, `domain_coalescedSum` |
| 3 | `206bb36` | the `⊕` conjunct, abstract and at `U` |
| 4 | `2043391` | the `+` conjunct, abstract and at `U` |

Not pushed; `gitcp.sh` reports "no tracking information for the current branch"
at the push step on each, which is the expected outcome for an agent.

## 8. Merge notes for the orchestrator

1. Streams 3 and 4 both import `PRep`. My edits to it are **two docstring hunks
   and nothing else**, so a conflict with agent3 is possible only if agent3 also
   rewrote lines 114–119 or `rep_lift`'s docstring.
2. `PRepSum.projCpo` is deliberately **not** reducible. `Cpo.str` is an instance,
   so instance search resolves `CompletePartialOrder (projCpo hp).carrier` by
   matching the head `Cpo.carrier ?D`; making it an `abbrev` unfolds it to the
   bare subtype before the match and breaks nine declarations. I tried both.
3. If agent3's `⊗` conjunct stalls on `Domain (Smash A B)`, the fix is the same
   shape as `isAlgebraic_coalescedSum`, and `Skeleton/Sum.lean`'s
   `isCompactElement_coe_smash_iff` is the criterion to build it on.
4. `docs/PaperInventory.md`'s Lemma 28 row should read **4 of 9 conjuncts at
   `Dyadic.U` with no hypothesis** after this branch merges — the numbered-result
   count for Lemma 28 itself is unchanged, since five conjuncts remain.
