---
round: r0014
from: orchestrator
to: user
subject: lemma5
date: 2026-0806-14:57
started: 2026-0806-14:55
finished: 2026-0806-14:57
related:
  - plans/r0014-plan-from-orchestrator-to-orchestrator-lemma5.md
  - reports/r0013-report-from-orchestrator-to-user-projection-image.md
---

# r0014 — Lemma 5 proved

**Third of the 28 numbered results.** `ScottDomains/FinitaryProjection.lean`,
0 `sorry`, 0 warnings, one elaboration failure. Elapsed 2 minutes.

| # | Criterion | Measurement |
| -- | --------- | ----------- |
| 1 | Builds | 0 errors, 0 warnings |
| 2 | Nothing unproved | 0 `sorry`, no `sorryAx` |
| 3 | Lemma 5 complete | both sentences |
| 4 | Hypotheses attributed | the first sentence is stated for `IsProjection`, not `IsFinitaryProjection` |

## The first sentence needs far less than the paper assumes

Lemma 5 is stated for a **domain `D`** and a **finitary** projection. The first
sentence — the compacts of `im(p)` are exactly `im(p) ∩ K(D)` — uses neither.
`IsProjection.isCompactElement_iff` needs only the two projection equations:

* `⟸` a directed set of the subtype has the same least upper bound computed in
  `im(p)` or in `D`, so compactness transfers down;
* `⟹` a directed `s ⊆ D` is pushed into `im(p)` by `p`, and `p x ≤ x` converts
  the witness back.

*Finitary* is spent only on the second sentence, and only in one place:
directedness of `im(p) ∩ K(D) ∩ ↓x` comes from algebraicity of `im(p)` applied
to `p x`. `D` being a domain is not used at all.

That is the fourth result in this development whose formalized hypotheses are
strictly weaker than the paper's — after Theorem 7, the two halves of
`IsAlgebraic`, and Lemma 4's union facts.

## The lemma worth isolating

`isLUB_val_image`: a least upper bound in `im(p)` is a least upper bound in `D`.
The obstacle is that an upper bound `v` of the image need not lie in `im(p)` —
but `p v` does, and it is still an upper bound, because `p` fixes the image and
is monotone. Then `p v ≤ v` finishes it. No completeness is assumed anywhere in
that argument, which is why the whole first sentence comes so cheaply.

## The instance splice earned its keep

The proof of the second sentence brings the `im(p)` cpo into scope with `letI`
and its `Domain` with `haveI`, then uses `IsAlgebraic.directedOn_compactsBelow`
on `p x`. That only typechecks because `rangeCompletePartialOrder` **spliced**
`Subtype.partialOrder` rather than rebuilding one: the `compactsBelow` of the
`letI` instance and the `IsCompactElement` of the statement must be about the
same order, and they are definitionally.

## Elaboration failure

One. `hu.2 hpv` has type `u ≤ ⟨p v, _⟩` in the subtype, so `.trans` expected
another subtype inequality where the next step was about `α`. Subtype `≤` is
definitionally the underlying `≤`, so a `show u.val ≤ p v` coercion fixes it —
the same shape as the `dsimp only` fixes in r0006 and r0008: the mathematics was
right, the elaborated form was not what the tactic wanted.

## Totals

Twelve modules, 1751 lines, 0 `sorry`, 0 warnings. Numbered results **3 of 28**
(Lemmas 4 and 5, Theorem 7). Definitions **7 of ≈13**.

Next is **Theorem 6**: the isomorphism between the cpo of normal substructures of
`K(D)` and the poset `Fp(D)` of finitary projections, via `N ↦ p_N` with
`p_N(x) = ⨆{y ∈ N | y ⊑ x}`. Lemma 5's second sentence is one half of that
correspondence.
