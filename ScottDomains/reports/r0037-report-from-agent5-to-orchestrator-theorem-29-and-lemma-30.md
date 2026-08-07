---
round: r0037
from: agent5
to: orchestrator
subject: theorem-29-and-lemma-30
date: 2026-0807-11:39
started: 2026-0807-11:15
finished: 2026-0807-11:39
related:
  - plans/r0037-plan-from-orchestrator-to-agent5-theorem-29-and-lemma-30.md
  - plans/r0037-plan-from-orchestrator-to-orchestrator-last-four.md
---

# r0037 stream 5 — Lemma 30 at ten, and Theorem 29's second sentence reduced to one proposition

Branch `agent5`, three commits: `3ce0ac6`, `758b802`, `dd47f92`. One new module,
`ScottDomains/ScottDomains/LemThirty.lean`, 722 lines, namespace
`ScottDomains.LemThirty`. `Colimit.lean`'s stale docstring corrected in place.

## Measurements

| # | Quantity | Value | Measured by |
| -- | -------- | ----- | ----------- |
| 1 | Build | `Build completed successfully (1218 jobs).` — 0 errors, 0 diagnostics, 0 non-`sorry` warnings | `scripts/compile.sh -r r0037`, log `compile-20260807-113727.agent5.log` |
| 2 | `sorry` | **1**, unchanged — `Skeleton/Section6.lean:197` (`thm18`), not mine | `scripts/counts.sh` |
| 3 | Modules / lines / theorems | 67 / 24338 / 1156, from 66 / 23596 / 1119 at the round's baseline | `scripts/counts.sh` |
| 4 | Axioms of every headline declaration | `[propext, Classical.choice, Quot.sound]` — no `sorryAx` | `scripts/axioms.sh -i ScottDomains.LemThirty` |
| 5 | Build attempts that failed | 1 of 6, on one instance-synthesis line (`Domain (plotkinOp D).carrier`) | build logs |

## What the source says, read from the image

`scripts/pdf-render.sh` at 600 dpi on page 43, then `scripts/pdf-crop.sh`. The
line reads

> **Lemma 30** *The following operators are p-representable over* **V**: `→`,
> `⇸`, `×`, `⊗`, `+`, `⊕`, `(·)⊥`, `(·)♯`, `(·)♭`, `(·)♮`. ∎

**Ten**, confirmed at the glyph level. `pdftotext` gives the same line as
`!, !, , ; +, ; ()?, ()], ()[, ()\`. Two further facts are visible in the print
and were not recorded before:

1. Lemma 30 spells out "**p**-representable", where Lemma 28 says
   "representable" and relies on the redefinition four paragraphs earlier. Both
   lemmas are therefore statements about `Fp`, which removes the last doubt about
   Lemma 28's notion that earlier rounds recorded.
2. The carrier is printed **V** in bold, the same letter this development uses.

Three printed defects in the surrounding §7.4 text, all previously recorded in
`BifiniteUniversal.lean`: "define `M(A)` to be **the** of pairs" (missing "set");
`D⁺` defined as ideals over `⟨M(A), ⊢⟩` with `A` unbound where `K(D)` is meant;
and the pre-order printed without its reflexive part. No new printed defect this
round.

## The transfer measurement — the item the plan ranked above any single conjunct

**The §7.3 proofs transfer to `V` completely, at zero proof cost.**
`PRep.rep_lift` and `PRep.rep_prod` are stated over an arbitrary
`{U : Type u} [CompletePartialOrder U]` with `[Domain U]` and the paper's
retraction pair as explicit hypotheses. Neither statement nor proof mentions
`Dyadic.U`, bounded completeness, atomless Boolean algebras, or any other §7.3
fact; the whole content is the `Fp` interface. Instantiating at `U := V` is one
`obtain` and one `exact` each — `rep_lift_V` and `rep_prod_V` are three lines
together, and they compiled first time.

So **Lemma 30 is not ten fresh proofs.** It is `PRep`'s ten generic schemes
(two exist, seven are streams 3 and 4, one is `(·)♮` and nobody's) plus ten
retraction pairs over `V`. The pairs are where the work is, and every one of them
is Theorem 29's second sentence at `E := F(V)` with `IsBifinite F(V)` supplied by
Lemma 17 — whose ten conjuncts (`ClosureProperties.lemma17`) are exactly Lemma
30's ten operators.

## Conjunct-by-conjunct

| # | Operator | Lemma 30 conjunct | Retraction pair over `V` | Generic scheme | Conjunct |
| -- | -------- | ----------------- | ------------------------ | -------------- | -------- |
| 1 | `→` | `IsPRepresentable₂ V PRep.funOp` | `retracts_fun_of_boundedComplete` — needs `[BoundedComplete V]` | none | open |
| 2 | `⇸` | `IsPRepresentable₂ V PRep.strictFunOp` | `retracts_strictFun_of_boundedComplete` — same | none | open |
| 3 | `×` | `IsPRepresentable₂ V PRep.prodOp` | `retracts_prod`, from `Thm29Normal` | `PRep.rep_prod` | **`rep_prod_V_of_thm29Normal`** |
| 4 | `⊗` | `IsPRepresentable₂ V PRep.smashOp` | `retracts_smash`, from `Colimit.Thm29Second` only | none | open |
| 5 | `+` | `IsPRepresentable₂ V PRep.sepSumOp` | `retracts_sepSum`, same | none | open |
| 6 | `⊕` | `IsPRepresentable₂ V PRep.coalSumOp` | `retracts_coalSum`, same | none | open |
| 7 | `(·)⊥` | `IsPRepresentable V PRep.liftOp` | `retracts_lift`, from `Thm29Normal` | `PRep.rep_lift` | **`rep_lift_V_of_thm29Normal`** |
| 8 | `(·)♯` | `IsPRepresentable V PRep.smythOp` | `retracts_smyth`, from `Thm29Normal` | none | open |
| 9 | `(·)♭` | `IsPRepresentable V PRep.hoareOp` | `retracts_hoare`, from `Thm29Normal` | none | open |
| 10 | `(·)♮` | `IsPRepresentable V plotkinOp` | `retracts_plotkin`, from `Thm29Normal` | none | open |

`Lemma30` is one ten-fold conjunction and `lemma30_of` takes ten named
hypotheses, so the count is checked by the kernel and cannot drift again.
`lemma30_iff_lemma28_and_plotkin` proves that Lemma 30's list *is* Lemma 28's
plus `(·)♮`, at whatever carrier both are read over — the sentence "the same nine
plus one" is now a theorem, not prose. `Lemma30AtV := Lemma30 Colimit.V` fixes
the carrier.

`plotkinOp D = ⟨Plotkin.Powerdomain D.carrier, inferInstance⟩`. Its `[Domain D]`
is spent in exactly one place, `Plotkin.FinCompacts.instCountable`, which feeds
Theorem 11's third hypothesis; the type and its cpo structure need only
`[CompletePartialOrder D]`. `domain_plotkinOp` records that, and it is
`inferInstance` behind a `show`.

## Theorem 29's second sentence — reduced, not proved

Not proved. It is now **one proposition** away rather than a paragraph away, and
the reduction is kernel-checked.

`Thm29Normal` : for every bifinite domain `E` there is an order-reflecting
`f : K(E) → A∞` whose range is normal in `A∞`.
`exists_embeddingProjectionPair_of_thm29Normal` derives the entire sentence from
it. The construction is elementary ideal manipulation:

| # | map | definition |
| -- | --- | ---------- |
| 1 | `E → V` | `x ↦ ↓(f '' {k ∈ K(E) | k ⊑ x})` |
| 2 | `V → E` | `J ↦ ⨆ f⁻¹(J)` |

and each hypothesis of `Thm29Normal` is spent once, in a different place:
order-reflection gives `p ∘ g = id`; **normality of `range f` gives directedness
of `f⁻¹(J)`**, which is what makes the projection well defined at all. Compact
approximation is never used — the argument is about ideals — and the composite
with `IdealCompletion.orderIsoIdealCompletionCompacts` finishes it. About sixty
lines; compiled first time.

Two corrections came out of writing it, both now in signatures rather than
comments.

1. **`Colimit.Thm29Second` as recorded in r0036 is stronger than the printed
   sentence, and the difference is not cosmetic.** The paper says "`E` is any
   bifinite **domain**"; `IsBifinite` alone is the Plotkin condition on `K(E)`.
   `countable_compacts_of_reflects` proves that an order-reflecting map into
   `A∞` has a countable source, because `A∞` is countable
   (`Colimit.instCountableAinf`). An uncountable flat cpo is bifinite with an
   uncountable basis, so the version of `Thm29Normal` quantifying over every
   bifinite cpo is **refutable**, not open. `Thm29SecondAtDomains` restores the
   paper's word; `thm29SecondAtDomains_of_thm29Second` records that the r0036
   form implies it. Inside the reduction proper only the algebraicity half of
   "domain" is spent.

2. **The round plan located the missing step in the wrong place.**
   `Colimit.lean` and both plans said the gap was "extending a normal embedding
   of a finite normal subposet of `K(E)` into `Stg n` to the next one into
   `Stg (n+1)`". `exists_stage_ge_of_finite` proves that statement, for arbitrary
   finite subsets of `A∞` and at arbitrarily late stages: the stages are already
   cofinal, and `isNormalIn_range_incl` already makes each normal in `A∞`. The
   gap is one level earlier — getting `K(E)` into `A∞` at all. The plan is not
   evidence; this is the source-and-kernel answer.

## A gap next to Lemma 17, found while doing this

Three of the ten retraction pairs — `⊗`, `+`, `⊕` — take the stronger
`Colimit.Thm29Second` and do not follow from `Thm29Normal`, because **this
development never proves `Smash`, `CoalescedSum` or `SeparatedSum` algebraic.**
Measured over the whole library: `IsAlgebraic` instances exist for `ScottHom`,
`Set X`, `IdealCompletion` and `WithBot`, and `PowerdomainRep.domain_prod`
supplies the product. The three sum-and-smash constructions have Lemma 10's
bounded completeness and Lemma 17's bifiniteness and nothing else. This is
independent of Theorem 29 and of §7.4, and no round has recorded it.

Separately, conjuncts 1 and 2 are blocked by `[BoundedComplete β]` in
`lem17_fun` and `lem17_strictFun`. `V` cannot be bounded complete if
`Thm29Second` holds, since `PRep.boundedComplete_range` would then force every
bifinite domain to be bounded complete. `ClosureProperties.lean`'s own docstring
already calls that instance "a real open item, not a formality"; this round
turns it into a hypothesis in two signatures.

## Against the ranked acceptance list

| # | Level | Status |
| -- | ----- | ------ |
| 1 | `Thm29Second` proved, Lemma 30 stated at ten with several proved | not reached |
| 2 | `Thm29Second` proved, Lemma 30 stated at ten | not reached — it needs `Thm29Normal`, which is [Gun87]'s content |
| 3 | Lemma 30 at ten with `plotkinOp`, plus the transfer measurement | **reached**, and exceeded: the transfer is kernel-checked at two conjuncts, and `Thm29Second` is reduced to one proposition |
| 4 | The ten-fold statement alone | reached |

Theorem 29's second sentence stays open, so the numbered count is unchanged by
this stream at 24 of 29 plus whatever streams 1–4 land. What changed is that the
remainder of Theorem 29 is `Thm29Normal` and nothing else, and that eight of
Lemma 30's ten conjuncts are now blocked only on per-operator schemes rather than
on anything about `V`.

## Merge notes

- One new file, `ScottDomains/ScottDomains/LemThirty.lean`; the `lakefile.toml`
  glob `ScottDomains.+` picks it up with no edit.
- `Colimit.lean` edited in three docstring places only — no declaration changed
  except `Lem30Arrow`'s docstring. No other stream touches that file.
- No new script written, so no repeat of r0036's `pdf-section.sh` collision;
  `pdf-render.sh`, `pdf-crop.sh`, `pdf-find-page.sh` and `pdf-section.sh` were
  reused as they stand.
- Streams 3 and 4's new schemes will instantiate at `V` exactly as `rep_lift` and
  `rep_prod` did, provided they are stated over a generic `[CompletePartialOrder U]`
  with the retraction pair as a hypothesis — which is the shape `PRep` already
  fixed. The paired retraction lemma for each is already in `LemThirty.lean`.
