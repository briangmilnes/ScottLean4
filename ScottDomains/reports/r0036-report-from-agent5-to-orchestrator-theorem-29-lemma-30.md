---
round: r0036
from: agent5
to: orchestrator
subject: theorem-29-lemma-30
date: 2026-0807-09:14
started: 2026-0807-08:38
finished: 2026-0807-09:14
related:
  - plans/r0036-plan-from-orchestrator-to-agent5-theorem-29-lemma-30.md
  - plans/r0036-plan-from-orchestrator-to-orchestrator-five-way-open-results.md
---

# r0036 stream 5 — `V`, `V ≅ V⁺`, and where Theorem 29's second sentence and Lemma 30 now stand

One new module, `ScottDomains/ScottDomains/Colimit.lean`, namespace
`ScottDomains.Colimit`. Nothing in `BifiniteUniversal.lean` or
`IdealCompletion.lean` was changed.

## Measurement

| # | Quantity | Value |
| -- | -------- | ----- |
| 1 | Build (`scripts/compile.sh -r r0036`) | `Build completed successfully (1138 jobs).` — 0 errors, 0 diagnostics, 0 non-`sorry` warnings, wall 1.83 s replay, peak RSS 1705 MiB single / 2503 MiB tree |
| 2 | `sorry` | **2**, both pre-existing and neither mine — `Skeleton/Recovered.lean:258` (`thm14`), `Skeleton/Section6.lean:197` (`thm18`) |
| 3 | Modules / lines / theorems | 62 / 20517 / 979 (baseline 61 / 19497 / 906 → +1 / +1020 / +73) |
| 4 | New module | `Colimit.lean`, 1020 lines |
| 5 | Axiom audit (`scripts/axioms.sh`, 19 declarations across two runs) | every one `[propext, Classical.choice, Quot.sound]`; **no `sorryAx`** |
| 6 | Stage counts, `scripts/mpair-stages.py` re-run this session | adopted reading **1, 2, 5, 20**; Smyth reading 1, 2, 5, 21; paper's stated 1, 2, 5, 20 |
| 7 | Stage count kernel-checked in Lean | stage 0 = 1 (`Subsingleton (Stg 0)`), stage 1 = 2 (`stg_one_eq` + `pointB1_ne_bot`). Stages 2 and 3 not attempted in Lean — see below |

## Acceptance

The plan's ranked acceptance, against what landed:

| # | Item | Status |
| -- | ---- | ------ |
| 1 | `V`, `Domain V`, `V ≅ V⁺`, Thm 29's second sentence, ≥1 Lemma 30 conjunct proved | partial — first three done, last two **stated only** |
| 2 | `V` with its `Domain` instance and `V ≅ V⁺` | **done** — `V`, `domain_V`, `isoPlus`, `iso_plus_V`, and additionally `isBifinite_V` |
| 3 | `A∞` countable Plotkin order with transport lemmas, `V` defined | done, and superseded by item 2 |
| 4 | reusable colimit machinery with the stage-count check reported | done — `idealCongr` is general and reusable |

Item 2, the plan's realistic target, landed in full. Items 1's two remaining
pieces did not; both are recorded as `Prop`-valued definitions
(`Thm29Second`, `Lem30Arrow`) with the missing step named, and **no `sorry`
stands in for either**.

## The route in the plan is wrong, and the correction is kernel-checked

Process rule 7 says the plan is not evidence and this stream's route in
particular is the orchestrator's reconstruction. Reading §7.4 from
`papers/Gunter Scott 1990.pdf` (pages 42–43 of the PDF) contradicts the plan on
one load-bearing point.

**The plan says to build the ω-colimit of `I ⊴ I⁺ ⊴ I⁺⁺ ⊴ ⋯` "along the
embeddings `eta`", quoting `BifiniteUniversal.lean:120–124`, and §7.4 does say
"each stage of the construction is embedded in the next one by the map
`x ↦ (x, {x})`". That colimit is not a fixed point of `M`.**

The obstruction is finite. Let `(x, u) ∈ M(A_N)`, so `[(x, u)] ∈ A_{N+1}`. Read
the same pair one stage later: its components in `A_{N+1}` are `eta x` and
`eta '' u`, so it becomes `[(eta x, eta '' u)] ∈ A_{N+2}`. For a map
`M(A_∞) → A_∞` to be well defined those two must agree, i.e. `eta` applied to
`[(x, u)]` must equal `[(eta x, eta '' u)]`; their bases are `[(x, u)]` and
`[(x, {x})]`, equal only when `↑u = ↑x`. It already fails at §7.4's own second
stage, at §7.4's own element `b = (⊥, ∅)`.

The chain that does have `M` as its colimit is the standard one: the connecting
map at stage `n+1` is `M` applied to the connecting map at stage `n`, from the
unique map out of `I = {⊥}`. The two chains **agree at stage 0 → 1** — there the
only map available is `⊥ ↦ ⊥ = (⊥, {⊥})`, which is `eta` — and first differ at
stage 1 → 2, where `eta` sends `b` to `(b, {b})` and `M(eta)` sends it to
`(a, ∅)`. Both are among §7.4's own five elements of `I⁺⁺`, so Figure 4 does not
discriminate them, and the text's sentence is consistent with the picture while
being wrong about the map.

`Colimit.stgEmb_ne_mk_eta` is that statement in Lean: `stgEmb 1 pointB1 ≠ mk (eta pointB1)`.
It is a third defect in §7.4 as printed, alongside the two `BifiniteUniversal.lean`
already records (the printed relation is not reflexive; the worked example
reverses its own definition).

**The stage sizes are unaffected**, because they are sizes of `Mⁿ(I)` modulo the
identification and the connecting map does not enter the count. So §7.4's
1, 2, 5, 20 still selects `MPair.le` over the Smyth reading's 1, 2, 5, 21, and
the check the plan required still passes — measured, not assumed
(`scripts/mpair-stages.py`, re-run this session, output quoted in row 6 above).

## A second correction: Lemma 30 has ten conjuncts, not nine

The plan says Lemma 30 is "the same nine operators of Lemma 28, p-representable
over `V`". The source lists Lemma 28's nine operators and then Lemma 30's list as
those **plus `()♮`**, the convex powerdomain — which is the entire reason §7.4
exists ("The convex powerdomain `()♮` cannot be representable over `U` because it
does not preserve bounded completeness"). `PRepresentable.lean`'s docstring
already says ten; the round plan and my stream plan say nine. The inventory row
for Lemma 30 should read 0 of **10**.

## Which colimit shape was chosen, and why

The plan offered two shapes for the direct limit and asked for both to be
prototyped on the order alone. Neither was used as stated; a third is cheaper and
was adopted after the first shape's transport lemmas were written out on paper.

**The shape used: `Antisymmetrization` of a pre-order on `Σ n, Stg n`, with
`Nat.leRecOn` supplying the transport.**

Three observations drove it.

1. **`Antisymmetrization` is forced, not a convenience.** `MPair A` is a genuine
   pre-order (`MPair.le_iff`'s second disjunct), so `MPair (MPair A)` does not
   typecheck at all — `MPair` demands `[PartialOrder A]`. The chain therefore
   cannot be `Aₙ₊₁ = MPair Aₙ` as the plan's step 1 has it. `Step A =
   Antisymmetrization (MPair A) (· ≤ ·)` performs exactly the identification §7.4
   performs by hand, and the paper's counts are counts after it ("20 elements
   **up to equivalence in the sense just mentioned**"). This was the first thing
   the plan's route ran into and it is not optional.

2. **`Nat.leRecOn` eliminates the dependent transport entirely.** The plan
   predicted the cost would be "dominated by dependent transport across
   `Aₙ → Aₙ₊ₖ`". Mathlib's `Nat.leRecOn {C : ℕ → Sort*} : n ≤ m → (∀ {k}, C k → C (k+1)) → C n → C m`
   with `C := Stg` gives `liftStg : n ≤ m → Stg n → Stg m` with **zero casts**, and
   `Nat.leRecOn_self`, `Nat.leRecOn_succ`, `Nat.leRecOn_trans` are the three
   lemmas the whole colimit needs. `≤` on `ℕ` is a `Prop`, so proof irrelevance
   is definitional and `liftStg` never depends on which proof is supplied. The
   predicted cost did not materialize; the four lemmas `liftStg_self`,
   `liftStg_succ`, `liftStg_trans`, `liftStg_le_liftStg` are 12 lines together.

3. **Comparing at a common stage, then antisymmetrizing, avoids `Quot.ind` almost
   everywhere.** `germLE p q` is literally `liftStg _ p.2 ≤ liftStg _ q.2` at
   `max p.1 q.1`, and `germLE_at` says any common stage gives the same answer.
   Every subsequent proof works with `germLE_at` at a chosen stage rather than
   with the quotient.

The cost that did bite was different from the plan's prediction: **typeclass
resolution keying on `Stg n` versus `(stage n).fst`**. Carrying each stage with
its own `PartialOrder` requires a `Sigma`-valued recursion
(`stage : ℕ → Σ T : Type, PartialOrder T`), and unifying an expected `Stg (n+1)`
against `Step ?α` unfolds through `stage` and leaves goals in `Sigma.fst` form
that the `Stg`-keyed instance does not match. Five of the eleven compile errors
in the session were that one cause. It is handled by an alias instance
`instPartialOrderStageFst` plus, in three places, `exact`/`have` in place of
`rw` — `rw` matches at `instances` transparency, which is too strict for
`instPartialOrderStg n` versus `(stage n).snd`, while `exact` at default
transparency accepts them.

## What is in the module

| # | Name | Content |
| -- | ---- | ------- |
| 1 | `mpairMap`, `mpairMap_le_mpairMap_iff`, `range_mpairMap`, `surjective_mpairMap`, `mpairMap_trans`, `mpairMap_congr` | `M` as a functor on order embeddings. `range_mpairMap : Set.range (mpairMap f) = MSub (Set.range f)` is the lemma that lets `MSub_isNormalIn` — the step Theorem 29's first sentence turns on — be reused unchanged, and it is used a second time for `expand_surjective` |
| 2 | `isNormalIn_image_range`, `isNormalIn_image_univ` | normality transported along a monotone order-reflecting map; the `◁` companion of the existing `isPlotkinOrder_image` |
| 3 | `idealCongr` | **the ideal completions of `α` and `β` agree along a monotone order-reflecting surjection.** Injectivity is *not* required, which is what lets the identification `M(A) → M(A)/≈` be an instance of it. General and reusable |
| 4 | `Step`, `stage`, `Stg`, instances | the tower, with `PartialOrder`, `OrderBot`, `Finite`, `Countable` at every stage |
| 5 | `stgEmb`, `isNormalIn_range_stgEmb` | the connecting map, and each stage normal in the next — by `MSub_isNormalIn` plus `range_mpairMap` |
| 6 | `pointB1`, `stgEmb_ne_mk_eta` | the kernel-checked defect above |
| 7 | `Germ`, `germLE`, `germLE_at`, `Ainf`, `incl` | the colimit |
| 8 | `isNormalIn_range_incl`, `exists_stage_of_finite`, `isPlotkinOrder_Ainf` | `A∞` is a Plotkin order; the finite normal witness for a finite set is a whole stage |
| 9 | `V`, `domain_V`, `isBifinite_V` | Theorem 11 applied once |
| 10 | `expand`, `expand_le_iff`, `expand_surjective` | `A∞ → M(A∞)/≈` — the fixed point. `expandStg_stgEmb` is where the corrected connecting map is spent |
| 11 | `isoPlus`, `iso_plus_V`, `isBifinite_plus_V` | **`V ≅ V⁺`**, as posets and as cpos |
| 12 | `stg_one_eq`, `incl_pointB1_ne_bot`, `principal_pointB1_ne_bot` | the counts and the nondegeneracy check |
| 13 | `Thm29Second`, `Lem30Arrow` | the two statements `V` makes type-correct |

`isoPlus` is `idealCongr` applied three times: to `expand` (the fixed point), to
`mk` backwards (the identification), and to `M(toCompacts)` (`A∞ = K(V)`, from
Theorem 11's second conclusion). Only the first is mathematical content; the
other two are bookkeeping that `idealCongr` makes uniform.

`isBifinite_V` mirrors `thm29` step for step and gives a consistency check:
`isBifinite_plus_V := thm29 V isBifinite_V` agrees with `isoPlus`.

## Nondegeneracy

`V ≅ V⁺` holds vacuously of a one-point domain, so it is checked that `A∞` and
`V` are not: `incl_pointB1_ne_bot` and `principal_pointB1_ne_bot`, with §7.4's own
`b = (⊥, ∅)` as witness at §7.4's own second stage.

## What is not proved, precisely located

1. **Theorem 29's second sentence** (`Thm29Second`). The hypothesis `D ≅ D⁺` is
   now discharged at `D = V` by `iso_plus_V`, and `isBifinite_V` supplies the
   standing assumption. What is missing is the universality argument §7.4 defers
   in full to [Gun87]: given bifinite `E`, build an embedding–projection pair
   `E ⇄ V` by matching `E`'s Plotkin order against the chain. Available for it:
   `isNormalIn_range_incl` (each stage normal in `A∞`) and `exists_stage_of_finite`
   (a finite subset of `A∞` lies in one stage). Missing: the extension step —
   from a normal embedding of a finite normal `N ◁ K(E)` into `Stg n`, produce one
   of the next finite normal subposet into `Stg (n+1)`. That is where `M`'s
   universal property among finite Plotkin orders is used, and it is not in the
   paper.

2. **Lemma 30** (`Lem30Arrow`). Only `→` can be written down at all: of the ten
   operators, only `Cpo.funSpace` exists in this development as a function
   `Cpo → Cpo`. `CombinatorRep.lean:559` already records that `()♯` and `()♭` are
   not, and `⊗, +, ⊕, ()⊥, ()♮` are likewise absent. So Lemma 30 is 1 of 10
   *statable* and 0 of 10 proved. Proving the `→` conjunct needs a representation
   of the function space over `V` — the §7.3 argument `lem23` runs for `Set ℕ`.

3. **Lean-side stage counts for stages 2 and 3.** Not attempted. `Nat.card (Stg 3)`
   by `decide` needs `DecidableEq` and a decidable `≤` through the quotient,
   including deciding `m.upper = n.upper` as a `Set` equality, plus
   `Fintype (Quotient _)`; the kernel would then dedupe ~160 pairs pairwise, on
   the order of 10⁵ decidable checks. Judged a poor return against
   `scripts/mpair-stages.py`, which is the repo's existing method and is already
   cited by `BifiniteUniversal.lean`'s docstring. Stage 1's count is checked in
   Lean (`stg_one_eq`).

## Process compliance

Namespace `ScottDomains.Colimit`, no collisions; `BifiniteUniversal` and
`IdealCompletion` imported and unmodified (plus `PRepresentable` and
`Mathlib.Data.Fintype.Powerset`, both with a comment saying why). All edits via
`Edit`/`Write`; no heredoc, no `sed -i`. One command per `Bash` call; no
chaining, no `cd`. One new script, `scripts/pdf-section.sh`, for reading §7.4
from the PDF. All builds through `scripts/compile.sh -r r0036`. Three commits on
`agent5` (`9e32c94`, `82f45b5`, `0c9044a`) plus this report; not pushed, per rule
8. `INDEX.md` updated with the new module.

## Suggested inventory edits

1. Theorem 29 — first sentence proved (`thm29`), second sentence **stated**
   (`Colimit.Thm29Second`), not proved. `V` now exists and satisfies the
   hypothesis.
2. Lemma 30 — **0 of 10**, not 0 of 9. Now statable: 1 of 10 conjuncts is
   type-correct (`Colimit.Lem30Arrow`); the other nine need their operators built
   as `Cpo → Cpo` first.
3. `BifiniteUniversal.lean:120–124` says the second sentence and `V` are "what
   [Gun87] carries and §7.4 does not: … the ω-colimit of `I ⊴ I⁺ ⊴ I⁺⁺ ⊴ ⋯` along
   the embeddings `eta`". The `V` half is now built, and the phrase "along the
   embeddings `eta`" is refuted by `Colimit.stgEmb_ne_mk_eta`. Worth a
   cross-reference from that docstring.
