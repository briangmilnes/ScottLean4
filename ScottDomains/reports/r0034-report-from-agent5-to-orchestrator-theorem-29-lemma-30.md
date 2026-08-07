---
round: r0034
from: agent5
to: orchestrator
subject: theorem-29-lemma-30
date: 2026-0806-23:16
started: 2026-0806-22:42
finished: 2026-0806-23:16
related:
  - plans/r0034-plan-from-orchestrator-to-agent5-theorem-29-lemma-30.md
---

# r0034 agent5 — Theorem 29, `V`, and Lemma 30

## Summary against the ranked acceptance criteria

| # | criterion | outcome |
| - | --------- | ------- |
| 1 | `thm29` proved | **first sentence proved** — `D` bifinite ⟹ `D⁺` bifinite, kernel-checked |
| 1 | `V` defined with its instances | **not delivered** — see "What did not land" |
| 2 | `IsPRepresentable` defined and distinguished | **delivered**, with the distinction itself kernel-checked |
| 3 | `lem30` for as many of the seven operators as land | **none landed**, and none could: every conjunct is a statement about `V` |
| 4 | 0 errors, 0 warnings beyond `sorry`, no new `sorry` | **met** — full build 0 errors, 0 warnings, 8 `sorry` all pre-existing |

## 1. What [Gun87] leaves deferred

**[Gun87] is unobtainable, and §7.4 contains no proof of Theorem 29 at all.**

The bibliography entry is `C. A. Gunter. Sets and the semantics of bounded
nondeterminism. Manuscript, 1987` — unpublished. It does not appear in Gunter's
own publication list at `seclab.illinois.edu`, and a web search returns nothing
under that title. §7.4 states Theorem 29, writes "A full proof of the theorem may
be found in [Gun87]", and substitutes an illustration: the chain
`I, I⁺, I⁺⁺, I⁺⁺⁺` with the element counts 1, 2, 5, 20 and Figure 4.

**The construction survives elsewhere.** Gunter, *Universal Profinite Domains*,
Information and Computation **72** (1987) 1–30, p. 23 — downloaded to
`ScottDomains/papers/Gunter 1987 Universal Profinite Domains.pdf` — gives the
same construction and attributes it to Scott:

> There is an even more explicit way of describing this operation which was
> remarked to the author by Dana Scott. Given a finite poset `A`, let `A⁺` be the
> set of pairs `⟨X, u⟩` such that `X ∈ A` and `u` is an **upwards closed** set of
> points from `A` such that `X ⊑ Y` for each `Y ∈ u`. Say that `⟨X, u⟩ ⊑ ⟨Y, v⟩`
> iff `Y ∈ u`. This more order-theoretic way of doing things helps in picturing
> the universal domain as the limit of the posets `A ⊴ A⁺ ⊴ A⁺⁺ ⊴ ⋯`.

Also downloaded, as the ICALP'85 predecessor:
`ScottDomains/papers/Gunter 1985 A Universal Domain Technique for Profinite Posets.pdf`.

Reading the two together fixes §7.4. `Pf(A)` is a *finite generating set* for
Gunter's upward-closed `u`, and §7.4's printed relation `∃ z ∈ u, z ⊑ y` is
Gunter's `Y ∈ u` transported along `u ↦ ↑u`. Two defects remain, both
kernel-checked in `BifiniteUniversal.lean`.

**Defect 1 — the printed relation is not reflexive, so it is not a pre-ordering.**
Reflexivity at `(x, u)` demands `∃ z ∈ u, z ⊑ x`, while membership in `M(A)`
demands `x ⊑ z` for every `z ∈ u`; together these force `x ∈ u`. The paper's own
second-step element `b = (⊥, ∅)` fails `b ⊢ b` (`paperLE_irrefl_pointB`), and so
does `(false, {true})` over `Bool`, where the cover is non-empty
(`paperLE_irrefl_boolPair`) — so the defect is not an artifact of admitting `∅`.
Gunter's form has the identical gap (`⟨X, ∅⟩ ⊑ ⟨X, ∅⟩` would need `X ∈ ∅`): in
both papers the printed relation is the **strict part**, and the order is its
reflexive closure. On finite generating sets that reflexive part is exactly the
identification §7.4 performs by hand — `(x, u)` and `(x, v)` are one element when
`↑u = ↑v`, which is how the paper identifies `(a, {a})` with `(a, {a, b})`.

**Defect 2 — the worked example reverses its own definition.** The text asserts
`b ⊢ a`. The printed definition yields `a ⊢ b` and refutes `b ⊢ a`
(`paperLE_pointA_pointB`, `not_paperLE_pointB_pointA`), as does Gunter's; and the
rest of the example needs `a ⊑ b`, since `(a, {b})` and `(a, {a, b})` are members
of `M(I⁺)` only under `a ⊑ b`.

**A second candidate repair is refuted by the paper's own numbers.** Comparing
covers in the Smyth (upper) pre-order — `(x,u) ⊑ (y,v)` iff `x ⊑ y` and every
`z ∈ v` is above some `z' ∈ u` — is also a pre-order containing the printed
relation, and it agrees with the reading adopted here at stages 0–2. It first
differs on whether `(a, ∅) ⊑ (b, ∅)`. Enumerating both
(`scripts/mpair-stages.py`, measured):

| # | reading | `I, I⁺, I⁺⁺, I⁺⁺⁺` |
| - | ------- | ------------------ |
| 1 | §7.4's stated counts | 1, 2, 5, **20** |
| 2 | printed relation + reflexive part (adopted) | 1, 2, 5, **20** |
| 3 | Smyth order on covers | 1, 2, 5, **21** |

Row 3 is refuted by the paper at the third step. This measurement is what
selected the definition; without it the wrong order compiles just as well.

**Consequence for the plan's premise.** The plan (and r0032 row 11) says the
paper "defers the full proof to [Gun87]". That is right, and stronger than it
sounds: there is no proof to transcribe and no source to consult, so Theorem 29
here is reconstructed from the statement plus Gunter 1987's definition. Anyone
extending this work should know that `V` inherits the same status.

## 2. Theorem 29 — what landed

`ScottDomains/ScottDomains/BifiniteUniversal.lean`, 485 lines, 38 declarations,
namespace `ScottDomains.BifiniteUniversal`, 0 `sorry`.

`thm29 : IsBifinite D → IsBifinite (Plus D)` — the **first sentence** of Theorem
29, with `Plus D = IdealCompletion (MPair ↥(compacts D))`, the domain of ideals
over `⟨M(K(D)), ⊢⟩`. Kernel-checked; axioms `[propext, Classical.choice,
Quot.sound]`, no `sorryAx`.

The argument is one construction and two transports:

| # | step | declaration |
| - | ---- | ----------- |
| 1 | `K(D)` a Plotkin order as a subset ⟹ as a poset | `isPlotkinOrder_univ_subtype` |
| 2 | `N ◁ A` finite ⟹ `M(N) ◁ M(A)` finite | `MSub_isNormalIn`, `MSub_finite` |
| 3 | `M` preserves Plotkin orders | `isPlotkinOrder_MPair` |
| 4 | a monotone order-reflecting map carries a Plotkin order | `isPlotkinOrder_image` |
| 5 | applied to `principal`, whose range is `K(D⁺)` | `thm29` |

Step 2 is the content. Directedness of `M(N) ∩ ↓(y,v)` is short under the
repaired order: two members below `(y,v)` supply `z₁ ∈ N`, `z₂ ∈ N` below `y`;
one application of `N ◁ A` at `y` joins them to `x₃ ∈ N` with `x₃ ⊑ y`; and
`(x₃, {x₃}) = eta x₃` — a point of the copy of `N` embedded by the paper's own
`x ↦ (x, {x})` — is above both and below `(y,v)`. The join never needs a cover
richer than a singleton. `M(N)` has `|N| · 2^|N|` members, which is the size of
the finite normal subposet the proof carries at each step.

Supporting results, all kernel-checked: `instPreorder` (the repaired order),
`MPair.le_of_paperLE` (the order contains the printed relation),
`MPair.equiv_of_upper_eq` (§7.4's identification), `eta_le_eta_iff` (each stage
embeds in the next), `instOrderBot` (`(⊥, {⊥})` is least — the paper's `a`),
`instCountable`, `nonempty_domain_plus` (`D⁺` is a domain, via Theorem 11), and
`mpair_punit_eq` (`I⁺` has exactly the paper's two elements).

## 3. `IsPRepresentable` — what landed

`ScottDomains/ScottDomains/PRepresentable.lean`, 157 lines, 6 declarations, same
namespace, 0 `sorry`.

`IsPRepresentable` and `IsPRepresentable₂` draw §7.3's square over `↥(Fp U)` —
the finitary **projections** — with `FpImage`, built from
`ScottHom.IsProjection.rangeCompletePartialOrder`. `ScottDomains.IsRepresentable`
draws the same square over `Fc(U)`, the finitary **closures**.

The distinction is not left to the docstring. `eq_id_of_mem_Fp_of_mem_Fc` proves
that anything both a finitary projection and a finitary closure is `ScottHom.id`:
`p ⊑ id` and `id ⊑ r` collapse under antisymmetry, pointwise. Outside that single
point the two posets are disjoint, so no representing map transfers between the
notions — which is the reason Lemma 28 (`Fc`, over §7.3's `U`) and Lemma 30
(`Fp`, over §7.4's `V`) are different theorems and the reason reusing the
existing class would have produced a theorem that compiles and is not the
paper's.

`isProjection_repOf` supplies the projection half of the paper's own recipe for a
representing map (`R♮(p) = ♮⁺ ∘ (p♮) ∘ ♮⁻` for a pair with `♮⁻ ∘ ♮⁺ = id` and
`♮⁺ ∘ ♮⁻ ⊑ id`). The conjugation `R(C) = gr ∘ C ∘ fn` and the isomorphism
`im(R(C)) ≅ im(C)` already exist in `Powerdomain/Universal.lean` stated with no
closure hypothesis, so they are reused rather than duplicated; the one new
obligation is that `R(C)` is a projection when `C` is. Note the pair condition
points the other way here — `gr ∘ fn ⊑ id`, where the `Fc` case has
`id ⊑ gr ∘ fn`.

## 4. What did not land, and why

| # | item | reason |
| - | ---- | ------ |
| 1 | Theorem 29's second sentence (`D ≅ D⁺` and `E` bifinite ⟹ projection `D → E`) | the universality argument is exactly what [Gun87] carries and §7.4 omits; it is not reconstructible from the two sentences the paper prints |
| 2 | `V`, the fixed point of `D ↦ D⁺` | needs the ω-colimit of `I ⊴ I⁺ ⊴ I⁺⁺ ⊴ ⋯` along `eta`. `Recursive.thm21` does not apply: it solves equations for operators *representable over a fixed cpo*, and `D ↦ D⁺` is a functor on domains, not such an operator. Building the colimit means an iterated type family `MIter : ℕ → Type` with its `Preorder` instances and the transported comparison `MIter n → MIter (n+k)`, i.e. dependent transport across `n + m` vs `m + n`. That is a self-contained round's work and could not be finished without leaving a `sorry`, so it was not started |
| 3 | `lem30`, all ten operators (`→, ⇸, ×, ⊗, +, ⊕, ()⊥, ()♯, ()♭, ()♮`) | every conjunct is "p-representable **over `V`**". With no `V` there is no instantiation, so **zero** conjuncts are provable, not merely the hard ones. `isProjection_repOf` is the reusable part that each conjunct will consume once `V` exists |

Nothing was stubbed: no new `sorry` anywhere.

## 5. Measurements

| # | metric | value |
| - | ------ | ----- |
| 1 | new modules | 2 (`BifiniteUniversal.lean`, `PRepresentable.lean`) |
| 2 | new lines of Lean | 642 |
| 3 | new declarations | 44 (38 + 6) |
| 4 | new `sorry` | 0 |
| 5 | full build | 0 errors, 0 warnings, exit 0, wall 3.14 s |
| 6 | `sorry` in the library | 8, all pre-existing (`Skeleton/Recovered.lean` ×7, `Skeleton/Section6.lean` ×1) |
| 7 | library totals after this round | 47 modules, 14 690 lines, 688 theorem-ish declarations |
| 8 | axiom audit | 20 declarations, all `[propext, Classical.choice, Quot.sound]`; `eta_le_eta_iff`, `MPair.le_of_paperLE`, `paperLE_irrefl_boolPair` are choice-free; none depends on `sorryAx` |
| 9 | composition check | both new modules imported into one environment by `scripts/axioms.sh`; no duplicate-name clash |

Logs: `ScottDomains/logs/compile-20260806-231442.agent5.log` (full build).

## 6. Files

| # | path | note |
| - | ---- | ---- |
| 1 | `ScottDomains/ScottDomains/BifiniteUniversal.lean` | `M(A)`, `D⁺`, `thm29`, the two defects |
| 2 | `ScottDomains/ScottDomains/PRepresentable.lean` | `IsPRepresentable`, the `Fp`/`Fc` separation, `isProjection_repOf` |
| 3 | `scripts/mpair-stages.py` | enumerates the `I, I⁺, I⁺⁺, I⁺⁺⁺` sizes under both candidate orders |
| 4 | `ScottDomains/papers/Gunter 1987 Universal Profinite Domains.pdf` | carries the construction [Gun87] was cited for |
| 5 | `ScottDomains/papers/Gunter 1985 A Universal Domain Technique for Profinite Posets.pdf` | ICALP'85 predecessor |

## 7. Recommendations to the orchestrator

1. **Record Theorem 29 as split.** The inventory should show the first sentence
   proved and the second deferred, not the theorem as a unit — the two sentences
   have different evidential status now that [Gun87] is known to be unobtainable.
2. **`V` is a round of its own.** The ω-colimit of `Mⁿ(1)` is the only remaining
   obstacle to Lemma 30, and it blocks all ten conjuncts at once. Scope it as
   "build the colimit and its `Preorder`/`OrderBot`/`Countable` instances", with
   `thm29` and `eta` as the given input.
3. **Cite the counts test.** `scripts/mpair-stages.py` is the artifact that
   distinguishes the correct order from a plausible wrong one. Any later change
   to `MPair`'s order should be re-checked against it.
4. **Coordinate with agent2 on `+`.** No overlap arose: this stream touched
   neither the coalesced sum `⊕` nor the separated sum `+`.
