---
round: r0049
from: agent6
to: orchestrator
subject: fpimages-bifinite
date: 2026-0809-16:55
started: 2026-0809-16:41
finished: 2026-0809-16:55
related:
  - plans/r0049-plan-from-orchestrator-to-orchestrator-six-at-the-unproven.md
  - reports/r0047-report-from-agent4-to-orchestrator-boundedcomplete.md
---

# r0049 agent6 — `FpImagesBifinite V` is proved; `Lemma30AtV` drops to arity 1

## 1. Outcome

**Discharged.** `R47.Agent4.FpImagesBifinite V` is a theorem with no hypotheses
and no instance binders: `R49.Agent6.fpImagesBifinite_V`. Conjuncts 1 and 2 of
`LemThirty.Lemma30AtV` follow from `LemThirty.Thm29SecondAtDomains` alone, and
`Lemma30AtV` itself now follows from `LemThirty.Thm29Normal` alone.

| # | claim | status before r0049 | status after |
| - | ----- | ------------------- | ------------ |
| 1 | `FpImagesBifinite V` | open; no declaration anywhere concluded `IsBifinite` of a projection image | **discharged**, unconditional (`fpImagesBifinite_V`) |
| 2 | `FpImagesBifinite U`, general | open | **discharged at `[IsAlgebraic U]`** (`fpImagesBifinite_of_isBifinite`); also recorded at `[Domain U]`, the binder every consumer already carries |
| 3 | `Lemma30AtV` conjunct 1 (`→` p-representable over `V`) | needed `Thm29SecondAtDomains` **and** `FpImagesBifinite V` | **closes** from `Thm29SecondAtDomains` alone (`rep_fun_V_of_thm29Second`) |
| 4 | `Lemma30AtV` conjunct 2 (`⇸`) | same | **closes** from `Thm29SecondAtDomains` alone (`rep_strictFun_V_of_thm29Second`) |
| 5 | `LemThirty.Lemma30AtV` | **reduced**, arity 3 (r0046: `Thm29Normal` + the two arrow conjuncts) | **reduced to arity 1** (`lemma30AtV_of_thm29Normal`) — open at exactly one named proposition, `Thm29Normal` |

Everything is in `ScottDomains/A6ProjectionBifinite.lean`, namespace
`ScottDomains.R49.Agent6`. No existing declaration was edited and no `def` was
changed.

## 2. Re-deriving agent4's two obstructions

The plan required the recorded blockers be re-derived, not assumed. Both were,
and they came out differently.

**The absence claim is correct.** r0047's agent4 wrote that "measured over every
module, no declaration concludes `IsBifinite` of a projection image".
Re-measured, by enumerating every declaration in `ScottDomains/` whose signature
line mentions `IsBifinite`, the ones that *conclude* it are: `lem17_prod`,
`lem17_sum`, `lem17_smash`, `lem17_separated`, `lem17_lift`, `lem17_fun`,
`lem17_strictFun`, `lem17_hoare`, `lem17_smyth`, `lem17_plotkin`,
`BifiniteUniversal.thm29`, `Colimit.isBifinite_V`, `isBifinite_plus_V`,
`A3Thm29.isBifinite_flat`, `isBifinite_plotkin_TT`,
`FinitaryProjectionEmbedding.isBifinite` (at `TwoMub`), `Skeleton.prop15` and
`Skeleton.thm18`. **None is about a projection image** — the operator arguments
are products, sums, lifts, function spaces and powerdomains, never `im(p)`. The
claim stands as written.

**Obstruction 1 — "transporting a normal subposet along `p` fails because
`p a ≤ x` does not give `a ≤ x`" — is real, and is bypassed rather than met.**
The naive witness for a finite `u ⊆ K(im p)` is `p(N)` for a finite `N ◁ K(D)`
containing `u`. That set is finite and contains `u`, but it is *not* normal in
`K(im p)`: for `a, b ∈ p(N)` below `x ∈ im p` there is no reason a member of
`p(N)` sits between them and `x`, and this is exactly agent4's point. The witness
used here is the strictly smaller set

    M = { y | G y = y },   G = p ∘ p_N,

the `G`-fixed part of `p(N)`. `M` *is* normal, and the proof of normality never
transports `N`: it uses only that `G` has a fixed point below each `x`. So
obstruction 1 is a correct statement about the route agent4 tried and has no
bearing on the route that works.

**Obstruction 2 — "the finite-image-deflation argument needs an idempotence that
`q ∘ p_i ∘ q` lacks" — is overstated, and that is this round's substantive
finding.** `G = p ∘ p_N` is Scott continuous, satisfies `G ⊑ id`, and has finite
image `⊆ p(N)`; it is indeed **not** idempotent, and nothing below assumes it is.
The argument does not need the maps idempotent. It needs, for each `x`, a
`G`-fixed point below `x` dominating every `G`-fixed point below `x` — and a
finite image supplies one *along the orbit*:

> `x ⊒ G x ⊒ G² x ⊒ ⋯` is antitone and, from index 1 on, confined to the finite
> `im(G)`. If no term were `G`-fixed, every step would be strict, the sequence
> would be strictly antitone hence injective, and its range would be an infinite
> subset of a finite set.

That is `R49.Agent6.exists_iterate_fixed`, twelve lines of tactic script. It
*produces* the idempotence the naive argument assumes, which is why the
obstruction does not bind. On the plan's own tally — five recorded blockers found
overstated or wrong in the last three rounds — this is the sixth, and it is grade
A by r0046's scale: the blocker's stated reason was refuted, not merely
re-attempted and found hard.

## 3. The proof

Fix a projection `p` on an algebraic cpo `α` with `IsBifinite α`, and a finite
`u ⊆ K(im p)`.

1. `Subtype.val '' u ⊆ K(α)` by Lemma 5's first sentence
   (`IsProjection.isCompactElement_iff`, which needs only that `p` is a
   projection). Bifiniteness of `α` gives finite `N ◁ K(α)` containing it.
2. `G := p ∘ p_N` as a `ScottHom`, continuous by `ScottContinuous.comp` over
   `scottContinuous_normalFun`. Then `G ⊑ id`, `im(G) ⊆ p(N)` is finite
   (`SFP.range_normalHom_of_finite` puts `p_N x ∈ N`), and `im(G) ⊆ im(p)`.
3. `M := {y | G y = y}` is finite, since `M ⊆ im(G)`.
4. Every `y ∈ M` is **compact in `α`**: for directed `s` with `IsLUB s v` and
   `y ⊑ v`, the set `G '' s` is a nonempty directed subset of the finite `im(G)`,
   so it has a greatest element `G a` which is its least upper bound
   (`SFP.exists_mem_isLUB_of_finite`); continuity gives `G v = G a`, and
   `y = G y ⊑ G v = G a ⊑ a`. This is
   `SFP.isCompactElement_of_mem_range_of_finite`'s argument, restated because
   that lemma asks for a projection and `G` is not one.
5. `Subtype.val ⁻¹' M` is finite, contains `u` (because `p_N` fixes `N ⊇ u` and
   `p` fixes `im(p)`), sits inside `K(im p)` by step 4 and
   `isCompactElement_iff`, and is **normal** in `K(im p)`: the orbit fixed point
   `c ⊑ x` of step 2's `G` is itself in `M`, and any `y ∈ M` with `y ⊑ x`
   satisfies `y = Gᵏ⁺¹ y ⊑ Gᵏ⁺¹ x = c`. `c` serves as both the nonemptiness
   witness and the directedness witness.

`im(p)` being a domain is never used, so the theorem is stated for a bare
`ScottHom.IsProjection` and `FpImagesBifinite` is the corollary at `Fp α`.

## 4. Declarations added, with axiom footprints

Eleven declarations, all in `ScottDomains/A6ProjectionBifinite.lean`, namespace
`ScottDomains.R49.Agent6`.

| # | declaration | axioms |
| - | ----------- | ------ |
| 1 | `iterate_le_self` | `propext, Quot.sound` |
| 2 | `monotone_iterate` | `propext, Quot.sound` |
| 3 | `exists_iterate_fixed` | `propext, Classical.choice, Quot.sound` |
| 4 | `exists_fixed_le` | `propext, Classical.choice, Quot.sound` |
| 5 | `isBifinite_range_of_isProjection` | `propext, Classical.choice, Quot.sound` |
| 6 | `fpImagesBifinite_of_isBifinite` | `propext, Classical.choice, Quot.sound` |
| 7 | `fpImagesBifinite_at_domain` | `propext, Classical.choice, Quot.sound` |
| 8 | `fpImagesBifinite_V` | `propext, Classical.choice, Quot.sound` |
| 9 | `rep_fun_V_of_thm29Second` | `propext, Classical.choice, Quot.sound` |
| 10 | `rep_strictFun_V_of_thm29Second` | `propext, Classical.choice, Quot.sound` |
| 11 | `lemma30AtV_of_thm29Normal` | `propext, Classical.choice, Quot.sound` |

No `sorryAx` anywhere; the package remains at `sorry 0`. Rows 1 and 2 are
`Classical.choice`-free, which is worth recording only because it locates where
choice enters: `Set.Finite` and the ambient cpo machinery, not the orbit
argument.

## 5. Discharged versus discharged-at

Row 8 — the round's assigned target — is a **discharge**: `fpImagesBifinite_V`
takes no hypothesis and adds no instance binder.

Row 6, the general statement, carries `[IsAlgebraic U]`, which
`R47.Agent4.FpImagesBifinite`'s own `def` does not. By the plan's rule that is a
**discharge-at**, and it is reported as one. Two measurements bound what it
costs:

* The binder is spent in exactly one place, `scottContinuous_normalFun`, and
  `NormalProjection.lean`'s module docstring already names that as "the only
  place the argument needs `D` to be algebraic" — so it is not a slack binder
  carried for convenience.
* Row 7, `fpImagesBifinite_at_domain`, records the statement at `[Domain U]`.
  Every consumer of `FpImagesBifinite` in the tree —
  `R47.Agent4.rep_arrow_of_fpImagesBifinite`,
  `rep_strictArrow_of_fpImagesBifinite`,
  `domain_range_strictArrowFamily_of_bifinite` — already carries `[Domain U]`,
  which extends `IsAlgebraic`. **The added binder therefore costs nothing at any
  existing call site**, and at `V` it costs nothing at all, `Colimit.domain_V`
  supplying it.

## 6. Build

`scripts/compile.sh -r r0049` over the whole package:
**1366 jobs, exit 0, zero errors, zero warnings, `sorry 0`**
(`logs/compile-20260809-165254.agent6.log`).

## 7. For the orchestrator

1. **`docs/Status.md` row 6** should change from "`Lemma30AtV` — item 4, plus
   `FpImagesBifinite V`" to "`Lemma30AtV` — item 4 only". The second input is
   gone.
2. **`A3Lemma30Schemes.lean:253`** says `Lemma30AtV` is "open at exactly two
   named obstructions — [Gun87]'s `Thm29Normal`, and the development's own
   bounded-completeness route to `Domain (D → E)`". The second is now closed;
   the sentence is stale and is a candidate for agent8's staleness check, which
   is precisely the class of defect r0046 measured (seven of eight false
   proof-claims were true when written).
3. **`A4RepArrow.lean:29–37`** states `FpImagesBifinite U` as "a new open item".
   Also stale.
4. `LemThirty.retracts_fun_of_boundedComplete` and
   `retracts_strictFun_of_boundedComplete` are now superseded twice over —
   r0047's agent4 flagged them for deliberate retirement and nothing on the
   critical path reaches them.
5. Coordination note for **agent5**, whose target is `Thm29Normal`: after this
   round `Thm29Normal` is the *only* thing between the development and
   `Lemma30AtV`, by `lemma30AtV_of_thm29Normal`. The payoff for closing or
   refuting it went up by two claims this round.
