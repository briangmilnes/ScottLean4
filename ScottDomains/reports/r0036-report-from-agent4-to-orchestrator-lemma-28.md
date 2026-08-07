---
round: r0036
from: agent4
to: orchestrator
subject: lemma-28
date: 2026-0807-09:06
started: 2026-0807-08:36
finished: 2026-0807-09:06
related:
  - plans/r0036-plan-from-orchestrator-to-agent4-lemma-28.md
  - plans/r0036-plan-from-orchestrator-to-orchestrator-five-way-open-results.md
---

# r0036 stream 4 — Lemma 28 at `Fp(U)`

One new module, `ScottDomains/PRep.lean`, namespace `ScottDomains.PRep`, 1002
lines, 55 top-level declarations. No declaration was added to `PRepresentable`,
`Dyadic`, `CombinatorRep`, or any other existing module; all four are imported.

## Measured build state

| # | Quantity | Value |
| -- | -------- | ----- |
| 1 | Build | `Build completed successfully (1138 jobs).` |
| 2 | Errors | 0 |
| 3 | Non-`sorry` warnings | 0 |
| 4 | Diagnostics | 0 |
| 5 | `sorry` | **2**, both pre-existing on `main` (`Skeleton/Section6.lean:196`, `Skeleton/Recovered.lean:257`); **0 introduced** |
| 6 | Wall / peak RSS | 1.72 s replay, 1768 MiB single |
| 7 | Axioms of every new declaration | `[propext, Classical.choice, Quot.sound]`, or none; no `sorryAx` |

Log: `ScottDomains/logs/compile-20260807-090537.agent4.log`.
Commits on `agent4`: `6187378`, `abbb9ac`, `819579e`, `be8741d`, `684ca7d`. Not pushed.

## The plan's operator list is wrong; the source wins

Process rule 7 says the plan is not evidence. It is not. The plan gives Lemma 28
as `→, ×, ⊗, ⊕, +, ()⊥, ()♮, ()♯, ()♭`. Physical page 42 of
`ScottDomains/papers/Gunter Scott 1990.pdf` was rendered at 600 dpi and read as
an image — the file's Type 3 bitmap fonts have no usable `ToUnicode` map, so
`pdftotext` emits `!, !, , ; +, ; ()?, ()], ()[` for the whole list. The rendered
line reads:

> **Lemma 28** *The following operators are representable over* U: →, ⇸, ×, ⊗, +, ⊕, (·)⊥, (·)♯, (·)♭.

and page 43, likewise rendered:

> **Lemma 30** *The following operators are p-representable over* V: →, ⇸, ×, ⊗, +, ⊕, (·)⊥, (·)♯, (·)♭, (·)♮.

Two corrections to the plan, each a change to what may be claimed:

1. **`(·)♮` is not in Lemma 28.** It is in Lemma 30 only, and §7.4's opening
   sentence says why: "The convex powerdomain `(·)♮` cannot be representable over
   `U` because it does not preserve bounded completeness." A nine-conjunct Lemma
   28 including `(·)♮` would state something the paper explicitly denies.
2. **`⇸` is in Lemma 28** and the plan drops it. The glyph is drawn `∘→`; it is
   §4.2's strict continuous function space, `StrictHom`.

The count nine is right; two of the nine members are not. `Combinator`'s r0034
docstring already had the correct nine — the plan drifted from the file, not the
file from the paper.

A second source reading corrects a file rather than the plan.
`PRepresentable.lean`'s docstring (r0034) asserts "Lemma 28 … is the `Fc`
notion." §7.3 redefines *representable* to mean *p-representable* four
paragraphs before Lemma 28 and inside the same subsection — "let us just use the
term 'representable' for 'p-representable' for the remainder of this section" —
so Lemma 28 is the `Fp` notion. `CombinatorRep.lean`'s docstring says this
correctly; the two modules on `main` contradict each other, and `CombinatorRep`
is right. Recommend the orchestrator correct `PRepresentable.lean`'s docstring.

## Conjunct-by-conjunct

`Lemma28 U` is one nine-fold conjunction (`PRep.lean`), so the count is
kernel-checked: `lemma28_of` takes nine named hypotheses and its anonymous
constructor must supply exactly nine components.

| # | Operator | Conjunct | Notion | Status |
| -- | -------- | -------- | ------ | ------ |
| 1 | `→` | `IsPRepresentable₂ U funOp` | `Fp(U)` | open |
| 2 | `⇸` | `IsPRepresentable₂ U strictFunOp` | `Fp(U)` | open |
| 3 | `×` | `IsPRepresentable₂ U prodOp` | `Fp(U)` | **proved** — `PRep.rep_prod` |
| 4 | `⊗` | `IsPRepresentable₂ U smashOp` | `Fp(U)` | open |
| 5 | `+` | `IsPRepresentable₂ U sepSumOp` | `Fp(U)` | open |
| 6 | `⊕` | `IsPRepresentable₂ U coalSumOp` | `Fp(U)` | open |
| 7 | `(·)⊥` | `IsPRepresentable U liftOp` | `Fp(U)` | **proved** — `PRep.rep_lift` |
| 8 | `(·)♯` | `IsPRepresentable U smythOp` | `Fp(U)` | open; **statable**, see below |
| 9 | `(·)♭` | `IsPRepresentable U hoareOp` | `Fp(U)` | open; **statable**, see below |

Both proved conjuncts carry `[Domain U]` and the operator's own retraction pair
(`fn ∘ gr = id`, `gr ∘ fn ⊑ id`) as hypotheses — exactly the shape
`Combinator.rep_arrow`/`rep_prod`/`rep_lift` have at the closure notion. At
§7.3's `U` the pair is what **Theorem 27** supplies, and `Dyadic.thm27` is still
conditional on `IsNormallyRepresented`, so `Lemma28AtU` is not derivable from
them yet. That blockage is one level below this stream and is agent3's.

Position moved from 3 of 9 at a notion known to be wrong, to 2 of 9 at the
paper's notion plus the machinery that unblocks the other seven.

## Re-examination of the three r0034 proofs

The plan asked whether `rep_arrow`, `rep_prod`, `rep_lift` transfer unchanged,
transfer with a changed hypothesis, or fail. **None transfers unchanged, and the
hypothesis change is not cosmetic.** Measured against `rep_lift`, ingredient by
ingredient:

| # | Ingredient | r0034 | At `Fp` |
| -- | ---------- | ----- | ------- |
| 1 | conjugating family `r⊥` | `Combinator.liftMap` | reused verbatim |
| 2 | its Scott continuity | `scottContinuous_liftFun` | reused verbatim |
| 3 | monotonicity in the index | `liftMap_mono` | reused verbatim |
| 4 | the two equations | `isClosure_liftMap` | re-proved (`isProjection_liftMap`); the inequality reverses |
| 5 | `im(r⊥) ≅ (im r)⊥` | `liftRangeOrderIso`, indexed by `Fc(U)` | re-derived at a bare `ScottHom` |
| 6 | `im(R(r⊥))` a **domain** | not required | **new work** (`domain_range_liftMap`) |
| 7 | index least upper bound | `isLUB_val_image_of_isLUB` (free) | `isLUB_val_image_of_isLUB_fp'`, which costs the keystone below |
| 8 | pair hypothesis | `Retracts U V`, i.e. `id ⊑ gr ∘ fn` | `gr ∘ fn ⊑ id` — **incompatible** |

Row 6 is the structural difference. `ClosurePoset U` is `{r // IsClosure r}`,
two equations. `↥(Fp U)` is `{p // IsFinitaryProjection p}`, and
`IsFinitaryProjection p ↔ ∃ hp : IsProjection p, Domain ↥(Set.range p)` — a
second component demanding the image be algebraic with a countable basis. Every
r0034 proof produces `⟨repOf fn gr (C r), isClosure_repOf …⟩`; the projection
analogue must produce a `Domain` that nothing on `main` supplied.

Row 8 is now kernel-checked rather than argued: `PRep.gr_fn_eq_of_both` shows
that `id ⊑ gr ∘ fn` and `gr ∘ fn ⊑ id` together force `gr ∘ fn = id`, and
`PRep.orderIsoOfBothPairs` builds the resulting `U ≃o V`. So r0034's hypothesis
and the projection scheme's are simultaneously satisfiable only when `U ≅ V` —
at `V = WithBot U`, only when `U ≅ U⊥`, false whenever `U` has a compact bottom.
The three proofs are not at a weaker notion of the same hypothesis; they are at a
different one.

## `(·)♯` and `(·)♭` are definable on `Cpo` — `CombinatorRep`'s docstring is wrong

`CombinatorRep.lean` records conjuncts 8 and 9 as blocked because "the operator
is not defined on `Cpo`", the powerdomains being `IdealCompletion (Pf K(D))`
which the file reads as needing `[Domain D]`. Measured, `[Domain D]` is spent in
exactly one place. The *type* `IdealCompletion (Pf ↥(compacts D))` and its
`CompletePartialOrder` instance need only `[Preorder A]` and `[OrderBot A]` of
the base preorder (`IdealCompletion.lean:232, 324`), both of which
`[CompletePartialOrder D]` already gives. `Countable A` — the only consumer of
`[Domain D]` — is needed solely by `IdealCompletion.instDomain` (line 443), to
make the *result* a domain.

`PRep.smythOp` and `PRep.hoareOp` are therefore honest functions `Cpo → Cpo`,
and `smythOp_eq`/`hoareOp_eq` check by `rfl` that they agree with
`Smyth.Powerdomain` and `Hoare.Powerdomain` wherever the latter are defined. Both
conjuncts are statable; the obstruction `CombinatorRep` names does not exist. The
remaining work on them is a representing map, not a definition. Recommend the
orchestrator correct that docstring too.

## What was built, and what it unblocks

| # | Result | What it is |
| -- | ------ | ---------- |
| 1 | `Lemma28`, `lemma28_of`, `Lemma28AtU` | the nine-fold conjunction, its constructor, and the instantiation at `Dyadic.U` |
| 2 | nine operators on `Cpo` | `funOp`, `strictFunOp`, `prodOp`, `smashOp`, `sepSumOp`, `coalSumOp`, `liftOp`, `smythOp`, `hoareOp` |
| 3 | `isProjection_sSup` | directed supremum of projections is a projection — free, no hypothesis on the carrier |
| 4 | `isFinitaryProjection_sSup` | **the keystone.** Over a domain, the directed supremum of *finitary* projections is finitary |
| 5 | `isLUB_val_image_of_isLUB_fp'` | least upper bounds in `Fp(D)` are pointwise — the projection counterpart of `isLUB_val_image_of_isLUB` |
| 6 | `domain_orderIso`, `isAlgebraic_orderIso`, `isCompactElement_orderIso` | `Domain` transports along `≃o` |
| 7 | `isFinitaryProjection_repOf` | reduces `Fp`'s new obligation to a `Domain` on the conjugating family's image |
| 8 | `boundedComplete_range`, `countable_compacts_range` | structural facts about a projection's image |
| 9 | `isPRepresentable_of_repFamily`, `isPRepresentable₂_of_repFamily` | the scheme `R(C) = gr ∘ C ∘ fn` at the projection notion |
| 10 | `gr_fn_eq_of_both`, `orderIsoOfBothPairs` | the incompatibility of the two pair hypotheses |

Item 4 is the load-bearing one. Every conjunct needs continuity of its
representing map; continuity needs least upper bounds in `Fp(U)` to be pointwise;
that needs the directed supremum of finitary projections to be finitary. Its
proof runs on two facts about a directed family `d` with pointwise supremum `P`:
`im(p) ⊆ im(P)` for each `p ∈ d`, and conversely every *compact* point of `im(P)`
already lies in some `im(p)` — because `k = P k = ⨆_{p ∈ d} p k` is directed and
compactness pushes `k` below a single `p k`, which `p ⊑ id` forces to equal `k`.
So `K(im P) = ⋃_{p ∈ d} K(im p)`, and each `K(im p)` is a domain basis by
finitarity of `p`.

With items 4–9 in place the remaining seven conjuncts are scheduled work rather
than research. Each needs three things and nothing else: the projection version
of its two equations, a `Domain` on `im(C)` (via `domain_orderIso` and the
`ClosureProperties` instance for that carrier — `lem10_*`/`lem17_*` supply the
bounded-complete and bifinite halves), and the index least upper bound, which is
now item 5.

Estimated remaining cost, measured against the two that landed (`(·)⊥` cost
about 130 lines, `×` about 100):

| # | Conjunct | Estimate | Note |
| -- | -------- | -------- | ---- |
| 1 | `→` | ~180 lines | needs `evidentOrderIso` re-derived at a projection pair, plus `[BoundedComplete U]` for `Domain (D → E)`; `boundedComplete_range` is already proved |
| 2 | `⇸` | ~150 lines | after `→`; `ClosureProperties.StrictFunction` has the closure-property half |
| 3 | `⊗` | ~150 lines | the r0034 counterexample does *not* apply here — a projection has `p ⊥ = ⊥`, so `im(p)`'s bottom is the ambient one and nothing is collapsed |
| 4 | `⊕` | ~150 lines | same remark |
| 5 | `+` | ~120 lines | `SeparatedSum = D⊥ ⊕ E⊥`; reuses `(·)⊥` |
| 6 | `(·)♯` | ~150 lines | statable now; needs the functorial action on `IdealCompletion (Basis D)` |
| 7 | `(·)♭` | ~150 lines | same |

## Compliance with the process rules

| # | Rule | Status |
| -- | ---- | ------ |
| 1 | Namespace `ScottDomains.PRep` | held; nothing added to `PRepresentable`, `Dyadic`, `CombinatorRep` |
| 2 | `Edit`/`Write` only, no heredoc, no `sed -i` | held |
| 3 | One command per `Bash` call, never `cd` | held |
| 4 | Multi-step work becomes a script | four new scripts: `pdf-section.sh`, `pdf-find-page.sh`, `pdf-render.sh`, `pdf-crop.sh` |
| 5 | Build only via `scripts/compile.sh -r r0036` | held; six runs, all logged |
| 6 | Errors and non-`sorry` warnings to zero | held: 0 and 0 |
| 7 | Read §7.3 of the PDF | done, by rendering pages 42 and 43 as images; two corrections to the plan resulted |
| 8 | Commit at every stopping point, do not push | five commits on `agent4`; push reports "no tracking information", the expected outcome |
| 9 | No new `sorry` | held: 0 introduced, total unchanged at 2 |

## Recommendations to the orchestrator

1. Merge `agent4`. Composition check: `scripts/axioms.sh -i ScottDomains.PRep -i <other new modules>` — `PRep` declares nothing that any other stream's namespace could collide with, but the r0028 clash survived a green build, so run it.
2. Correct `PRepresentable.lean`'s docstring: Lemma 28 is the `Fp` notion, not `Fc`. The sentence is refuted by §7.3's own "for the remainder of this section".
3. Correct `CombinatorRep.lean`'s docstring: `(·)♯` and `(·)♭` *are* definable on `Cpo`; the `[Domain D]` it cites is spent on `IdealCompletion.instDomain`, not on the type.
4. Update `docs/PaperInventory.md` for Lemma 28 as **2 of 9 at `IsPRepresentable` over `Fp(U)`**, replacing 3 of 9 at `IsRepresentable` over `Fc(U)`. The row should say the nine operators are `→ ⇸ × ⊗ + ⊕ (·)⊥ (·)♯ (·)♭` and that `(·)♮` belongs to Lemma 30.
5. `Lemma28AtU` remains underivable until `Dyadic.thm27` is unconditional — that is agent3's `IsNormallyRepresented`. Sequencing note, not a defect in this stream.
