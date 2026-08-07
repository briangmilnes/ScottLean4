---
round: r0031
from: agent3
to: orchestrator
subject: theorem-18
date: 2026-0806-20:45
started: 2026-0806-20:22
finished: 2026-0806-20:45
related:
  - plans/r0031-plan-from-orchestrator-to-agent3-theorem-18.md
  - reports/r0028-report-from-agent4-to-orchestrator-minimal-upper-bounds.md
---

# r0031 agent3 — `ContinuousConstruction.lean`; Theorem 18 still `sorry`

## Measurement

| # | Quantity | Value |
| -- | -------- | ----- |
| 1 | Final build | `Build completed successfully (976 jobs).` |
| 2 | Errors | 0 |
| 3 | Warnings | 1, the declared `sorry` at `Skeleton/Section6.lean:196` (`thm18`) |
| 4 | New module | `ScottDomains/ContinuousConstruction.lean`, 597 lines, 44 declarations (9 definitions, 35 theorems) |
| 5 | `sorry` in the development | 1, unchanged — `thm18` |
| 6 | Files edited outside the new module | 0. `Skeleton/Section6.lean` is untouched, so there is nothing to conflict with agent2's round |
| 7 | Axioms | every new theorem: `[propext, Classical.choice, Quot.sound]` or a subset; `sorryAx` occurrences in the audit: **0** |
| 8 | Build cost | wall 3.39 s incremental, peak RSS 1667 MiB single process |
| 9 | Commit (branch `agent3`) | see the tail of this report |

The axiom audit was run as a temporary module `#print axioms`-ing the fourteen
headline results and then deleted; its log is
`logs/compile-20260806-203330.agent3.log`. Two results —
`scottContinuous_familyFun` and `minimalUpperBounds_subset_image` — depend on no
axioms at all.

## The constructor, exactly as stated

A **family** is a set `s ⊆ D × E` of pairs, read as "offer at least `e` once `k`
has arrived", defining

    valuesAt s x = {e | (k, e) ∈ s and k ⊑ x}
    familyFun s x = ⨆ (valuesAt s x)

    theorem scottContinuous_familyFun
        (hd : ∀ x, DirectedOn (· ≤ ·) (valuesAt s x))
        (hk : ∀ p ∈ s, IsCompactElement p.1) :
        ScottContinuous (familyFun s)

Hypotheses: `[PartialOrder α] [CompletePartialOrder β]`. **No completeness on the
domain, no algebraicity, and no bounded completeness anywhere** — `D` need only be
a partial order. Compactness of the keys is spent exactly once, in the least-upper-
bound half; the upper-bound half is monotonicity.

The observation that makes this work is that r0007's
`scottContinuous_pointwiseSup_of_forall_isLUB` never required the *family* of step
functions to be directed, only each **evaluation image** to attain its supremum.
`CompactFunction.lean`'s decomposition fails without `[BoundedComplete β]` because
it takes suprema of bounded, non-directed sets of functions; `familyFun` takes
suprema of directed sets of *values* instead, and that condition is checkable.

Three further results carry the weight:

* `familyFun_le_iff` — the adjunction, generalizing `ScottHom.step_le_iff` from
  one pair to a family: `(∀ x, familyFun s x ⊑ f x) ↔ ∀ (k,e) ∈ s, e ⊑ f k` for
  monotone `f`. Every later fact goes through it.
* `isLUB_of_iUnion` — a union of families is the least upper bound of its pieces
  in `D → E`. This is the "the perturbation converges" tool; the proof is the
  adjunction twice.
* `basisExtension` — **every monotone assignment on `K(D)` extends to a continuous
  function**:

      theorem directedOn_valuesAt_graphOn (hv : MonotoneOn v (compacts α)) (x : α) :
          DirectedOn (· ≤ ·) (valuesAt (graphOn v) x)
      def basisExtension (v : α → β) (hv : MonotoneOn v (compacts α)) : ScottHom α β
      theorem basisExtension_apply_of_isCompactElement … : basisExtension v hv k = v k
      theorem eq_basisExtension_of_eqOn … (hf : ∀ k, IsCompactElement k → f k = v k) :
          ⇑f = basisExtension v hv

  which is r0028's stated prerequisite verbatim — "the least continuous function
  above a given monotone partial assignment on `K(D)`" — with existence
  unconditional and uniqueness proved. `valuesAt` on the graph is `v ''
  compactsBelow x`, the monotone image of a directed set, so directedness is free.
  Read backwards, `coe_eq_basisExtension_self` is a structure theorem: every
  continuous function *is* the basis extension of its own restriction to `K(D)`,
  which is what `CompactFunction.lean` obtains only under `[BoundedComplete β]`.

The second admissible class is families totally ordered in both coordinates
(`directedOn_valuesAt_of_comparable`), where `valuesAt` is a chain. Its instance
is the perturbation r0028 could exhibit only inside a hand-worked example:

    def shift (hx : StrictAnti x) (hc : ∀ n, IsCompactElement (x n)) : ScottHom α α
    theorem shift_chain … : shift hx hc (x n) = x (n + 1)
    theorem shift_apply_le … : shift hx hc z ≤ z

## Smyth's cases: which are complete

**None of the three is complete.** What is proved is a reduction of (a) and (b) to
a single finiteness statement, and the sufficiency of that statement.

Case (a), a finite `u ⊆ K(D)` with no complete set of minimal upper bounds. Three
steps, all kernel-accepted:

1. `exists_isCompactElement_le` — the entry point, formalizing fact 2 of the plan:

       theorem exists_isCompactElement_le [IsAlgebraic (ScottHom α α)] {f : ScottHom α α}
           (hu : u.Finite) (huc : u ⊆ compacts α) (hf : ∀ k ∈ u, k ≤ f k) :
           ∃ g : ScottHom α α, IsCompactElement g ∧ g ≤ f ∧ ∀ k ∈ u, k ≤ g k

   With `f = idHom` this is the compact `g ⊑ id` with `g k = k` on `u`. The
   diagonal step functions `step k k` are compact and below `f`, and
   `exists_mem_upperBounds_of_directedOn` collapses the finitely many of them
   inside the directed set `compactsBelow f`.
2. `apply_mem_upperBounds` — `g` carries upper bounds of `u` to upper bounds of
   `u`, and `g ⊑ id` puts each image below its argument, so `g '' ub(u)` is a
   *complete set of upper bounds*.
3. `hasCompleteMub_of_finite_image` — if that image is finite and lands back in
   `A`, then `HasCompleteMub A u`. Minimality inside a finite complete set
   upgrades to minimality outright, the argument of
   `hasCompleteMub_of_isNormalIn`.

Case (b), infinitely many minimal upper bounds, reduces to the **same** statement:
`minimalUpperBounds_subset_image` shows each minimal upper bound `m` satisfies
`g m = m`, so `minimalUpperBounds A u ⊆ g '' upperBoundsIn A u`.

Case (c), `U^∞(u)` infinite, was not attacked: König's lemma is downstream of a
case (a)/(b) contradiction that does not exist yet. No Mathlib König search was
performed, since nothing consumes it.

Also proved, in the opposite direction, and the most reusable result of the round
after the constructor:

    theorem isBifinite_of_exists_finite_projection
        (h : ∀ u : Set α, u.Finite → u ⊆ compacts α → ∃ p : ScottHom α α,
          ScottHom.IsProjection p ∧ (Set.range ⇑p).Finite ∧ u ⊆ Set.range ⇑p) :
        IsBifinite α

The finite range *is* the finite normal subposet: it consists of compacts
(`isCompactElement_of_mem_range` — the image of a directed set under `p` is a
directed subset of a finite set, hence has a greatest element), it is mub-closed
by `minimalUpperBounds_subset_image`, and each finite subset is mub-complete by
`hasCompleteMub_of_finite_image`; `isNormalIn_of_isMubClosed` assembles them. So
Theorem 18 is now *equivalent* to producing finite projections, which is the shape
Smyth's argument actually delivers.

## The obstacle, with the failing step

`thm18` is unchanged and still `sorry`. The single remaining obligation for cases
(a) and (b) is:

> **(★)** a compact deflation `g ⊑ id` on a domain `D` with `D → D` a domain has
> a finite image on `upperBoundsIn (compacts D) u`.

Two measurements on (★), both from failed attempts this round rather than
speculation:

1. **(★) is not a lemma below Theorem 18; it is equivalent to it.** In a bifinite
   `D` it is a three-line consequence of the finite deflations: `g = ⨆ₙ pₙ ∘ g` is
   directed, compactness gives `g ⊑ p_N ∘ g`, and `pₙ ⊑ id` then forces
   `g z = p_N (g z) ∈ im(p_N)`, a finite set. Conversely `isBifinite_of_exists_-
   finite_projection` above turns (★) plus idempotence back into bifiniteness. So
   any proof of (★) from `[Domain α] [Domain (ScottHom α α)]` *is* Smyth's proof.

2. **The perturbation route blocks on one monotonicity side condition, and it is
   not an artifact of the formalization.** The intended contradiction is: from
   `¬ HasCompleteMub` extract the strictly descending chain of upper bounds
   `x₀ ⊐ x₁ ⊐ …` (proved, `exists_strictAnti_of_not_hasCompleteMub`), then build
   an increasing family `qₙ ↑ g` with `g ⋢ qₙ`, contradicting compactness of `g`.
   Each `qₙ` must be the basis extension of a monotone assignment `wₙ` on `K(D)`
   that agrees with `g` off the chain and is shifted one step down along it:

       wₙ(k) = g k                      if k is not above any x_m with m ≥ n
       wₙ(k) = g (x_{m₀+1})             where m₀ = least m ≥ n with x_m ⊑ k

   Monotonicity of `wₙ` holds in every case but one. For `k₁ ⊑ k₂` with `k₁` in
   the first branch and `k₂` in the second it requires

       g k₁ ⊑ g (x_{m₀+1}),

   and nothing supplies it: `k₁ ⊑ k₂` and `x_{m₀} ⊑ k₂` put `k₁` and `x_{m₀+1}`
   below a common element, but a domain that is not bounded complete has no join
   to compare them at. In the worked counterexample of r0028 the condition holds
   only because every compact there is either an upper bound of `u` or below every
   `x_m`. The same side condition defeats the variants tried: restricting `g` to an
   upward-closed set of keys (pointwise directedness survives — that is
   `{k | k ⋢ x}` — but the assignment then drops the members of `u` to `⊥`, so the
   family does not converge to `g`), composing `g` with a deflation `rₙ` built the
   same way (identical failing case), and adjoining the chain pairs to the graph of
   `g` (the union of the two families is not pointwise directed at points above no
   chain element).

So the missing step is not a construction of continuous functions any more — that
is what this module supplies — but the combinatorial content of Smyth's proof: a
*choice of chain* for which the shifted assignment is monotone, which is where the
property-M failure has to be spent. Case (c) and König's lemma are downstream of
it and were not reached.

## Recommendation

Merge the module: it is a self-contained, kernel-accepted result set that does not
touch any other file, and three of its results (`basisExtension`,
`coe_eq_basisExtension_self`, `isBifinite_of_exists_finite_projection`) are
statements §3 and §6 want independently of Theorem 18.

If Theorem 18 gets another round, the target should be stated as (★) or, better,
as "every finite `u ⊆ K(D)` lies in the range of a finite projection", since
`isBifinite_of_exists_finite_projection` now discharges everything after it. The
intermediate lemma worth having first is "a continuous deflation with finite image
has an idempotent iterate" — the images `im(gⁿ)` decrease and stabilize, and a
deflationary bijection of a finite poset is the identity — which converts (★) into
that target. It was not attempted here; it is perhaps 60 lines and is not on the
critical path, because (★) itself is.
