---
round: r0041
from: agent4
to: orchestrator
subject: effective-presentations
date: 2026-0808-13:20
started: 2026-0808-13:02
finished: 2026-0808-13:20
related:
  - plans/r0041-plan-from-orchestrator-to-orchestrator-close-unstated.md
  - reports/r0040-report-from-agent1-to-orchestrator-property-coverage-s2-s3.md
---

# r0041 stream 4 — `ScottDomains.Effective`: §3.2 instantiated, Theorem 7's second and third sentences stated and proved

**Theorem 7's second sentence is stated and proved** (`theorem7_arrow`), and so is
its third (`theorem7_strict`). `PaperInventory` row 2e's "the only numbered
property in the paper with no Lean statement" is closed.

The round also produced a measurement that changes what those proofs mean, and it
is the most important thing in this report:

> **`EffectivePresentation` as currently defined is satisfied by every domain.**
> `nonempty_effectivePresentation` proves it in eight lines.

`Domain` already requires `K(D)` countable, `K(D)` contains `⊥`, so
`Set.Countable.exists_eq_range` gives a surjection `ℕ ↠ K(D)`; and both
"effectively decidable" conditions are `DecidablePred` fields, which
`Classical.dec` inhabits. So Theorem 7's second sentence, its third sentence, and
§3.2's closing claim that *every* operator of §§4–7 preserves effective
presentability are all corollaries of `Domain` instances the development already
had. They are now stated and proved; the proofs are one line each. That is the
finding, not the achievement.

Everything else in the stream is built so that the gap between the rendered
statement and the paper's statement is visible in Lean rather than in prose.

## Rows

| # | Row | Paper / p. | Status | Declaration |
| -- | --- | ---------- | ------ | ----------- |
| 1 | Instantiate `EffectivePresentation` at a concrete domain | §3.2 / 11 | **done, computably** | `Effective.powersetPresentation : EffectivePresentation (Set ℕ)` |
| 2 | Thm 7b: `D`, `E` effectively presented ⟹ `D → E` has an effective presentation | Thm 7 / 12 | **stated and proved**, enumeration genuine, decidability classical | `Effective.theorem7_arrow`, via `Effective.scottHom` |
| 3 | Thm 7d: the same for `D ⊸ E` | Thm 7 / 12 | **stated and proved**, hypotheses unused | `Effective.theorem7_strict` |
| 4a | Thm 7 proof: "the poset of step functions has decidable ordering and finite normal subposets … using the effective presentations of `D` and `E`" | Thm 7 proof / 12 | **stated** as a named `Prop`, open | `Effective.StepFunctionsDecidable` |
| 4b | "all of these operators preserve the property of having an effective presentation" | §3.2 / 12 | **stated and proved** at rendered strength; **stated** as a `Prop` schema at recursion-theoretic strength, open | `Effective.operator_preserves_effectivePresentation`, `Effective.PreservesRecursivePresentation` |

Four rows targeted, four rows stated, three proved, one open with a named `Prop`.
Row 4b counts once in each column because the sentence has two readings and both
are now in the file.

The paper text was checked against `papers/Gunter Scott 1990.pdf` (physical
pp. 11–13) rather than taken from the plan. Every sentence the plan attributes to
§3.2 and Theorem 7 is verbatim correct, including the three-sentence structure of
Theorem 7 that r0040 recovered. No correction to the plan is needed on this
stream.

## Row 1 — `P N` has an effective presentation, and its decision procedures run

`ScottDomains/Effective/Powerset.lean`, 252 lines, 18 declarations.

The enumeration is **not** Mathlib's `Denumerable (Finset ℕ)`, which would
discharge every field but routes both decisions through `List.mergeSort`. It is
the binary expansion, `Finset.equivBitIndices : ℕ ≃ Finset ℕ`, sending `n` to
`{i | n.testBit i}`. Under it the paper's two conditions become arithmetic on the
indices:

| # | Paper's condition | This enumeration | Declaration |
| -- | ----------------- | ---------------- | ----------- |
| 1 | `dₘ ⊑ dₙ` | `m ||| n = n` | `powersetEnum_le_iff` |
| 2 | `{dₙ \| n ∈ u} ◁ K(P N)` | `0 ∈ u ∧ ∀ i j ∈ u, i ||| j ∈ u` | `isNormalIn_powersetEnum_image_iff` |

The mathematical content is condition 2, proved for an arbitrary powerset as

    isNormalIn_compacts_set_iff :
      (∀ s ∈ N, s.Finite) →
        (N ◁ compacts (Set X) ↔ ∅ ∈ N ∧ ∀ s ∈ N, ∀ t ∈ N, s ∪ t ∈ N)

— a family of finite subsets is normal in the basis exactly when it contains `∅`
and is closed under binary union. Left to right instantiates `IsNormalIn`'s "for
every `x ∈ K(P X)`" at `x := s ∪ t`, which is legitimate because that set is
finite hence compact; directedness of `N ∩ ↓x` then returns an element of `N`
squeezed between `s ∪ t` and itself. Right to left needs `∅` for the nonemptiness
conjunct — the one `NormalSubposet.lean` records as the reason Lemma 4.3 does not
hold under Mathlib's `DirectedOn` — and the union for directedness.

**The two `Decidable` fields are programs, and this is checked by the kernel.**
Six `example`s at the end of the module are closed by `decide` — one fixing the
enumeration, five running the two conditions — which a `Classical.dec` instance
cannot do:

| # | `example` | Value |
| -- | -------- | ----- |
| 1 | `Finset.equivBitIndices 5 = {0, 2}` | `5 = 0b101` |
| 2 | `powersetEnum 1 ≤ powersetEnum 5` | condition 1, true |
| 3 | `¬ (powersetEnum 2 ≤ powersetEnum 5)` | condition 1, false |
| 4 | `(powersetEnum '' ↑{0,1}) ◁ compacts (Set ℕ)` | condition 2, true |
| 5 | `¬ ((powersetEnum '' ↑{1}) ◁ compacts (Set ℕ))` | condition 2, false — Lemma 4.3 decided by a program |
| 6 | `¬ ((powersetEnum '' ↑{0,1,2}) ◁ compacts (Set ℕ))` | condition 2, false — not closed under joins |

This answers the r0022/r0031 caution head-on for one domain: `decidableLE` being
too weak to *prove* anything computable does not stop a particular presentation
from having a decision procedure that visibly computes.

## Row 2 — Theorem 7's second sentence

`ScottDomains/Effective/FunctionSpace.lean`, 378 lines, 20 declarations.

    theorem7_arrow (d : EffectivePresentation α) (e : EffectivePresentation β) :
        Nonempty (EffectivePresentation (ScottHom α β))

proved by `scottHom d e`, whose enumeration is the paper's and not an abstract
re-indexing:

1. `Denumerable (Finset (ℕ × ℕ))` names the `n`-th finite set of index pairs.
2. `pairsOf d e` reads it as a finite set of compact pairs, using `d` and `e`.
3. `ScottHom.ofPairs` (from `FunctionSpaceCountable.lean`) joins the step
   functions those pairs name.
4. Surjectivity onto `K(D → E)` is
   `ScottHom.exists_ofPairs_of_isCompactElement` — every compact function is a
   finite join of step functions — with `d.enum_surjective` and
   `e.enum_surjective` pulling each compact pair back to a pair of indices. The
   pullback is `choose!` on a finite set, so its image names a `Finset (ℕ × ℕ)`.

So `d` and `e` are genuinely used: they supply the index set the enumeration runs
over and the surjectivity that makes it exhaust the basis.

**One guard is needed and it is exactly the paper's difficulty.** A finite set of
step functions need not be bounded above and `sSup` on `ScottHom` is total, so
`ofPairs P` is a junk value there and need not be compact. `scottHomEnum`
therefore tests `IsCompactElement (ofPairs P)` and falls back to `⊥`. Deciding
that test is what condition 2 of an effective presentation of `E` exists to
supply, and it is the sentence Theorem 7's proof calls "tedious, but not
difficult". Here the test is a classical `if`, so `scottHomEnum` and `scottHom`
are `noncomputable`, and `scottHom`'s two `Decidable` fields are `Classical.dec`.

`CompactFunction.lean`'s note that it does **not** prove "a finite join of
compacts is compact" is the reason the guard is a test rather than a theorem; that
lemma (`BddAbove` + finite + compacts ⟹ join compact, by induction on
`isCompactElement_of_isLUB_pair`) is the one piece of domain theory that would
replace the guard with a proof, and it is not in the development.

## Row 3 — Theorem 7's third sentence

    theorem7_strict [Domain (StrictHom α β)]
        (_d : EffectivePresentation α) (_e : EffectivePresentation β) :
        Nonempty (EffectivePresentation (StrictHom α β))

Stated with the paper's hypotheses and proved — but **the hypotheses are unused**,
and the underscores say so rather than the statement quietly dropping them. The
paper's reason is that "the strict step functions form a basis" for `D ⊸ E`; this
development has no strict-step-function basis. What it has is
`PRepFun.strictHomDomain` (r0037), which makes `D ⊸ E` a domain by injecting
`K(D ⊸ E)` into `K(D → E)` — countability without an enumeration. So the proof
goes through `nonempty_effectivePresentation`.

The `[Domain (StrictHom α β)]` binder is not an extra hypothesis: the statement
mentions `EffectivePresentation (StrictHom α β)`, so the instance is needed at
elaboration time, before any tactic can run. An `example` immediately below
discharges it from `PRepFun.strictHomDomain`.

## Row 4 — the two remaining §3.2 claims, and what is actually open

The recursion-theoretic reading is stated so the gap is a Lean object:

| # | Declaration | Content |
| -- | ----------- | ------- |
| 1 | `Computable.RecursiveLE` (reused from `ComputableFunction.lean`, r0031) | condition 1 as a `ComputablePred` |
| 2 | `RecursiveNormal` | condition 2 as a `ComputablePred`, indexed by `Denumerable (Finset ℕ)` because Mathlib has no `Primcodable (Finset ℕ)` and `ComputablePred` cannot be asked of a predicate on `Finset ℕ` at all |
| 3 | `IsRecursive` | the conjunction — a presentation in the paper's intended sense |
| 4 | `StepFunctionsDecidable d e` | **row 4a**, defined as `IsRecursive (scottHom d e)` |
| 5 | `Theorem7ArrowRecursive` | row 2 at that strength, universally quantified |
| 6 | `Theorem7StrictRecursive` | row 3 at that strength |
| 7 | `PreservesRecursivePresentation γ d e` | **row 4b** as a schema, one instance per operator of §§4–7 |

`exists_isRecursive_of_stepFunctionsDecidable` proves row 4a ⟹ row 2's effective
form at fixed `d`, `e` — which is the paper's own proof structure: once the
step-function poset is shown to have decidable ordering and recognizable finite
normal subposets, the theorem *is* that presentation.

**Two measured obstructions block discharging rows 4–7, and both are recursion
theory, not domain theory.**

| # | Obstruction | Measurement |
| -- | ----------- | ----------- |
| 1 | `RecursiveLE powersetPresentation` reduces to `Computable fun p : ℕ × ℕ => p.1 \|\|\| p.2` | `grep -rn "Primrec.*lor\|Primrec.*bitwise\|Computable.*lor\|Primrec.*testBit\|Computable.*testBit"` over **all** of `Mathlib/` → **0 hits**. Supplying it means deriving `Nat.bitwise` from `Primrec.nat_strong_rec` |
| 2 | composition of computable functions | already recorded in `ComputableFunction.lean`: `REPred`'s API in Mathlib v4.32.2 is five lemmas and supplies closure under neither `∧` nor `∃`. Not rediscovered, cited |

Neither caution from r0022/r0031 was rediscovered; both are cited where they bite.

## Build

| # | Measure | Baseline (start of round) | After |
| -- | ------- | ------------------------: | ----: |
| 1 | `lake build` jobs | 1229 | **1279** |
| 2 | errors | 0 | **0** |
| 3 | non-`sorry` warnings | 0 | **0** |
| 4 | `sorry` | 1 (`Skeleton/Section6.lean:196`) | **1**, unchanged |
| 5 | new modules | — | 2 |
| 6 | new lines | — | 630 |
| 7 | new declarations | — | 38 |

`scripts/axioms.sh` over `powersetPresentation`,
`isNormalIn_powersetEnum_image_iff`, `nonempty_effectivePresentation`,
`theorem7_arrow`, `theorem7_strict`,
`operator_preserves_effectivePresentation` and
`exists_isRecursive_of_stepFunctionsDecidable`: every one depends on
`[propext, Classical.choice, Quot.sound]` and nothing else. No `sorryAx`.
`powersetPresentation`'s `Classical.choice` enters only through
`Set.Finite.toFinset` inside the surjectivity *proof*; the data fields still
compute, which is what the six `decide` examples check.

## Side effect worth recording

`ComputableFunction.lean` was imported by no module and `EffectivePresentation.lean`
only by it — r0040's evidence that §3.2 was dead code.
`Effective/FunctionSpace.lean` imports `ScottDomains.ComputableFunction` and
`Effective/Powerset.lean` imports `ScottDomains.EffectivePresentation`, so both
§3.2 modules are now reachable from live modules and are re-elaborated by every
build. `INDEX.md` gained the two new entries.

## Recommendation to the orchestrator

The plan's row 4 said "without one instance the whole structure is unfalsifiable".
That was right, and the instance found something: the structure is not merely
uninstantiated, it is **unfalsifiable in the stronger sense that it holds of
everything**. Two follow-ups, in cost order:

1. **Cheap and local.** Decide whether `EffectivePresentation` should carry
   `RecursiveLE`/`RecursiveNormal` as fields rather than `DecidablePred`. The
   r0031 note left this as "an open decision"; `nonempty_effectivePresentation`
   is the argument for closing it. Changing it invalidates nothing in this stream
   — `powersetPresentation` would need obstruction 1 above, and `scottHom` would
   become `StepFunctionsDecidable`, which is precisely the point.
2. **A round of its own.** `Primrec (Nat.bitwise)` from `Primrec.nat_strong_rec`.
   It unblocks `RecursiveLE powersetPresentation`, which is the only route to a
   single non-vacuous instance of §3.2 anywhere in the development.
