---
round: r0037
from: agent2
to: orchestrator
subject: theorem-1-37
date: 2026-0807-11:30
started: 2026-0807-11:10
finished: 2026-0807-11:30
related:
  - plans/r0037-plan-from-orchestrator-to-agent2-theorem-1-37.md
  - plans/r0037-plan-from-orchestrator-to-orchestrator-last-four.md
---

# r0037 stream 2 — Jung's Theorem 1.37

One new module, `ScottDomains/ScottDomains/JungNets.lean`, 369 lines, namespace
`ScottDomains.JungNets`. `JungSFP.lean` and `MinimalUpperBounds.lean` were read
and imported; neither was edited. Acceptance item reached: **2** — the reduction
built and the remainder named as a `Prop`, not a `sorry`.

## Correction to the plan, from the source

The plan (and my own r0036 hand-off it quotes) describes Theorem 1.37 as "if
`[D → D]` is continuous then `K(D)` has property m". **The source does not say
that.** Jung 1989 p.50 reads

> **Theorem 1.37** A dcpo with continuous function space is bicomplete.

with *bicomplete* defined on p.13 as "`D` is a dcpo and `Dᵒᵖ` is a dcpo". Property
m is a separate step, taken one section later in the proof of Theorem 2.3 (p.56):

> We have proved in Theorem 1.37 that a dcpo with algebraic function space is
> bicomplete, **hence `D` has property m**.

Jung never proves that "hence". The two steps have very different costs, and the
plan's one-sentence compression hides the split. **This report's main measured
result is that the split is 1 : 0** — the "hence" is now proved in full and the
theorem is not.

## What is proved

All `#print axioms` outputs are `[propext, Classical.choice, Quot.sound]`; no
`sorryAx` anywhere (`scripts/axioms.sh` over all eight new theorems).

| # | Declaration | Statement |
| -- | ---------- | --------- |
| 1 | `IsBicomplete` | Jung's p.13 definition: every filtered subset has a `IsGLB` |
| 2 | `HasChainInfima` | the weaker condition actually consumed: every nonempty chain has a `IsGLB` |
| 3 | `IsBicomplete.hasChainInfima` | 1 ⟹ 2 (a nonempty chain is filtered) |
| 4 | `exists_minimal_mem` | Zorn downwards — the order dual of `zorn_le₀`, absent from Mathlib |
| 5 | `exists_minimal_upperBounds_le` | **Jung's "hence"**: `HasChainInfima D` ⟹ property m in `D`, for *arbitrary* subsets |
| 6 | `hasCompleteMub_of_hasChainInfima` | property m in the development's relative form, `HasCompleteMub (compacts D) u` |
| 7 | `hasCompleteMub_pair` | item 6 at a pair — literally `lemma217`'s hypothesis |
| 8 | `Thm137`, `Thm137Chains`, `Thm137.toChains` | the remainder, and the weaker obligation everything factors through |
| 9 | `forall_hasCompleteMub_of_thm137` | `isBifinite_iff_mubClosure`'s **first conjunct**, modulo `Thm137` |
| 10 | `lemma217_of_thm137` | `JungSFP.lemma217` with its property-m hypothesis discharged |
| 11 | `propertyM_pairs_of_thm137` | property M at every pair of compacts — `thm214`'s first disjunct, proved outright rather than as a disjunct |

Item 5 is the mathematical content: Zorn's lemma applied downwards inside
`ub(A) ∩ ↓x`. A chain there has an infimum by hypothesis; that infimum is still an
upper bound of `A` because each `a ∈ A` is a *lower* bound of the chain, so it is
below the *greatest* lower bound; and it is still below `x` because it is below any
member of the chain. Minimality inside `ub(A) ∩ ↓x` upgrades to minimality in
`ub(A)` since any upper bound below `m` is below `x` too.

**The shapes agree.** `lemma217`'s hypothesis is discharged by application —
`JungSFP.lemma217 hAlg hCount ha₁ ha₂ (hasCompleteMub_pair …)` typechecks with no
restatement and no edit to `JungSFP.lean`. The conversion between "minimal in
`compacts D`" and "minimal in `D`" is `JungSFP.mem_minimalUpperBounds_of_minimal`,
which was already there.

**The obligation is weaker than the plan assumed.** Everything downstream needs
only `HasChainInfima D` — infima of nonempty chains — not bicompleteness. That is
recorded as `Thm137Chains`, with `Thm137.toChains` connecting it to the source's
statement. A later round may prove either.

## Mathlib survey, measured

Run before writing any Lean, per the plan's step 2.

| # | Item | Present? | Measurement |
| -- | ---- | -------- | ----------- |
| 1 | Zorn upwards | yes | `zorn_le₀`, `Mathlib/Order/Zorn.lean:110` |
| 2 | Zorn downwards | **no** | `grep -rn "zorn_ge" Mathlib/` → 0 hits. Built here at `Dᵒᵈ`, the way `zorn_superset` (`Zorn.lean:152`) does it — 1 line |
| 3 | `Minimal`/`Maximal` duality | yes | `minimal_toDual`, `Mathlib/Order/Minimal.lean:73` |
| 4 | **Iwamura's lemma** (chain-complete ⟺ directed-complete) | **no** | `grep -rn "Iwamura\|Markowsky" Mathlib/` → 0 hits. `ChainCompletePartialOrder` exists (`Mathlib/Order/BourbakiWitt.lean:53`) with an instance to `OmegaCompletePartialOrder` and **none** to `CompletePartialOrder` |
| 5 | Ordinal-indexed nets in a poset | **no** | `grep -rln "Ordinal" Mathlib/Order/` → 3 files, all unrelated (`InitialSeg`, `Extension/Well`, `Filter/Cocardinal`) |
| 6 | Transfinite recursion | yes | `Ordinal.limitRecOn`, `Mathlib/SetTheory/Ordinal/Arithmetic.lean:158` |
| 7 | Codirected sets | partial | `IsCodirectedOrder` is whole-type (`Mathlib/Order/Directed.lean:194`); the set-level form is `DirectedOn (· ≥ ·)` |
| 8 | `IsGLB` | yes | `Mathlib/Order/Bounds/Basic.lean` |

Rows 1–3 and 8 are why the "hence" cost 12 lines of proof. Rows 4 and 5 are why
Theorem 1.37 did not land: its first step is a *missing theorem*, not a missing
notation.

## What remains: the dependency list, from the source

Jung's proof is eleven printed lines. Read against what is on disk it needs five
things. The plan's second-hand three-item summary is right as far as it goes but
omits the first and largest.

1. **Corollary 1.3, dually** — "By Corollary 1.3 we have to find infima only for
   monotone injective nets `s : αᵒᵖ → D` where `α` is an ordinal number."
   Corollary 1.3 rests on **Theorem 1.2** — "a poset is a dcpo if and only if each
   chain has a supremum", Jung's citation to Iwamura, unproved in his text.
   Absent from Mathlib (survey row 4) and from `ScottDomains/`. Independent
   difficulty; a formalization would also need "every linearly ordered set has a
   coinitial well-ordered subset", which is likewise absent.
2. **The retraction `r` onto `A ∪ αᵒᵖ`**, `r x = x` on `A = lb(αᵒᵖ)` and
   `r x = ⋀{γ ∈ αᵒᵖ | γ ≥ x}` off it. Not immediately well-defined: that infimum
   is over a proper initial segment of the chain, so it exists only under a
   least-counterexample transfinite induction on `α`, and it lands *inside* the
   chain only after the chain is normalized so every limit stage is the infimum
   of its predecessors. Jung compresses both to one sentence.
3. **Proposition 1.22** — a retract of a dcpo with continuous function space again
   has continuous function space. Two sub-results the development lacks: the
   retraction–embedding pair on function spaces, and "a retract of a continuous
   dcpo is continuous". `Projection.lean` and `NormalProjection.lean` carry
   projections but neither result.
4. **Interpolation, Proposition 1.8** — `x ≪ y` ⟹ `x ≪ z ≪ y`. Zero occurrences
   of interpolation in `ScottDomains/` (`grep -rn "interpolat" ScottDomains/ScottDomains/`
   → 1 hit, and it is `JungSFP.lean`'s own obstruction note).
5. **The successor family `g_β`** — the only part that is a proof script over
   machinery items 1–4 build.

Items 2 and 3 additionally require a sub-dcpo `D' = A ∪ αᵒᵖ` carrying its own
`CompletePartialOrder` instance and its own function space.

I did **not** build partial ordinal machinery. Nothing downstream would consume
it, and a half-built chain API would be speculative code that the next round would
have to re-derive against whatever shape item 1 turns out to need.

## The other source on disk

`Abramsky Jung Domain Theory 1994.pdf` §4.2–4.3 covers the same classification
(their Theorem 4.3.4 is Jung's Theorem 2.14; their Theorem 4.3.5 is Smyth's
Theorem 2.3) but **gives no proof of this step**: it routes through coherence
(Lemmas 4.3.1, 4.3.2) and cites [Jun89] and [Jun90]. Its Exercise 4.3.11(1) is
Jung's Theorem 1.35 and Exercise 4.3.11(10) — "Prove that FS-domains have infima
for downward directed sets" — is the bicompleteness statement, set as an exercise.
So Jung 1989 is the only proof of Theorem 1.37 on disk and there is no cheaper
route in the other paper.

## Build and counts

| # | Quantity | Value | Measured by |
| -- | -------- | ----- | ----------- |
| 1 | Build | `Build completed successfully (1218 jobs).` — 0 errors, 0 diagnostics, 0 non-`sorry` warnings | `scripts/compile.sh -r r0037`, log `compile-20260807-112706.agent2.log` |
| 2 | Modules / lines / theorems | 67 / 23952 / 1130 | `scripts/counts.sh` |
| 3 | `sorry` | 1 — `Skeleton/Section6.lean:197` (`thm18`), pre-existing, none added | `scripts/counts.sh` |
| 4 | Axioms of the 8 new theorems | `[propext, Classical.choice, Quot.sound]`, no `sorryAx` | `scripts/axioms.sh` |
| 5 | New module | `JungNets.lean`, 369 lines | `wc -l` |

Baseline was 66 / 23596 / 1119 with 1 `sorry`; this stream adds 1 module, 356
lines counted by `counts.sh` (369 by `wc -l`) and 11 declarations, and removes no
`sorry`.

## For the merge

* Namespace `ScottDomains.JungNets` — no collision.
* No script was added, so r0036's `scripts/` collision cannot recur from this
  stream.
* `INDEX.md` gained one line, after the `JungSFP.lean` entry.
* **For agent1's assembly.** `forall_hasCompleteMub_of_thm137` is stated in exactly
  the shape `MinimalUpperBounds.isBifinite_iff_mubClosure` consumes as its first
  conjunct, and `propertyM_pairs_of_thm137` is `thm214`'s first disjunct proved
  outright. Both carry `Thm137 D` (equivalently `Thm137Chains D`) as an explicit
  hypothesis, so `thm18` remains a `sorry` in `Skeleton/Section6.lean` unless
  agent1 chooses to thread that hypothesis through. **That is a decision for the
  orchestrator, not for me** — threading it would change `thm18`'s statement, and
  the plan says a shape disagreement is a finding, not an edit.
