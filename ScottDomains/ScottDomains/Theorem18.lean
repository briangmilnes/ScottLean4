import ScottDomains.JungFinite
import ScottDomains.JungNets
import ScottDomains.Skeleton.Recovered

/-!
# Theorem 18, assembled: the reduction to Jung's two open propositions

Gunter & Scott, *Semantic Domains*, §6.2, printed page 33:

> **Theorem 18** If `D` and `D → D` are domains, then `D` is bifinite.

The paper gives no proof — "The theorem is due to Smyth and its proof may be found
in [Smy83a]" — so the development follows A. Jung, *Cartesian Closed Categories of
Domains*, CWI Tract 66 (1989), whose five-step route `ScottDomains/Section62.lean`
maps. Four of the five steps and all the glue between them are kernel-checked;
what remains are exactly **two named propositions**, neither stubbed with `sorry`:

| # | Proposition | Jung | Declaration |
| -- | ----------- | ---- | ----------- |
| 1 | a dcpo with algebraic function space is bicomplete | Theorem 1.37 | `JungNets.Theorem137` |
| 2 | a fixed point of a compact deflation is compact | Corollary 1.36 | `JungFinite.FixedPointOfCompactDeflationIsCompact` |

## Why this file exists

The two halves of the reduction were proved in separate worktrees that could not
see each other: `JungFinite.theorem_18_of_propertyM` consumes property m at every
finite subset of `K(D)`, and `JungNets.forall_hasCompleteMub_of_jung_theorem_1_37` produces
it from Theorem 1.37. `lake build` never puts the two modules in one environment —
neither imports the other — so it cannot check that the hypothesis shapes agree.
`scripts/check-theorem_18-composition.sh` elaborated the composite in a scratch file
and reported that it does, but **a script is not a library theorem**: it is not
built by `lake`, not counted, and nothing can cite it. r0040's agent4 measured
that no declaration recorded the composition. `theorem_18_of_jung_theorem_1_37_and_jung_corollary_1_36` below
is that declaration, so the reduction is now checked by every build and citable
by name.

## What is spent, and what is not

`theorem_18_of_jung_theorem_1_37_chains` is the sharp form. `JungNets.Theorem137` concludes
`IsBicomplete D` — infima of *all* filtered subsets — but every use factors
through Zorn's lemma, which quantifies over chains, so only
`JungNets.Theorem137Chains` (infima of nonempty **chains**) is consumed. Proving
`Theorem137Chains` alone therefore suffices for Theorem 18; the full Theorem 1.37 is
more than the route needs. `theorem_18_of_jung_theorem_1_37_and_jung_corollary_1_36` is the same statement in
Jung's own hypothesis, obtained through `JungNets.Theorem137.toChains`.

Countability of `K(D → D)` enters exactly once, inside `JungSFP.jung_lemma_2_17`, via
`Domain.countable_compacts` on the function space. Without it Theorem 18 is false
— the algebraic L-domains are the counterexamples (Abramsky & Jung 4.3.4 vs
4.3.5) — so its appearance in the instance hypotheses is not incidental.

## The conclusion in the paper's own words

`IsBifinite` is defined in `ScottDomains/Bifinite.lean` as `IsPlotkinOrder
(compacts α)`, which is the *second* conjunct of clause 2 of the paper's Theorem
14, not the paper's definition of "bifinite". The paper defines (printed page 29):

> **Definition:** Let `D` be a cpo. Let `M` be the set of finitary projections
> with finite image. Then `D` is said to be bifinite if `M` is countable,
> directed and `⨆M = id`.

`Recovered.theorem_14 : IsBifiniteViaProjections α ↔ Domain α ∧ IsBifinite α` (proved
in r0036) is what licenses reading one as the other, and under Theorem 18's own
hypothesis `[Domain α]` the two conclusions coincide.
`theorem_18_viaProjections_of_jung_theorem_1_37` states Theorem 18 with the paper's
literal conclusion, so the identification is kernel-checked rather than asserted.
-/

namespace ScottDomains.Theorem18

open ScottDomains

variable {α : Type*} [CompletePartialOrder α] [Domain α] [Domain (ScottHom α α)]

/-- **Theorem 18, reduced to Jung's Corollary 1.36 and the chain form of his
Theorem 1.37.**

> If `D` and `D → D` are domains, then `D` is bifinite.

This is the sharp reduction: `h137` asks only for infima of nonempty *chains* in
`D` (`JungNets.Theorem137Chains`), which is what Zorn's lemma consumes in
`JungNets.exists_minimal_upperBounds_le`, and is strictly weaker than the
bicompleteness `JungNets.Theorem137` concludes.

The composite is Jung's five steps: `h137` supplies step 1 (property m at every
finite subset of `K(D)`, through `JungNets.hasCompleteMub_of_hasChainInfima`),
`JungFinite.theorem_18_of_propertyM` supplies steps 2–5 with `hcor` — Corollary 1.36 —
as its only other hypothesis. -/
theorem theorem_18_of_jung_theorem_1_37_chains
    (h137 : JungNets.Theorem137Chains α)
    (hcor : JungFinite.FixedPointOfCompactDeflationIsCompact α) :
    IsBifinite α :=
  JungFinite.theorem_18_of_propertyM hcor fun _ hvc hvfin =>
    JungNets.hasCompleteMub_of_hasChainInfima (h137 inferInstance) hvfin hvc

/-- **Theorem 18, reduced to Jung's Theorem 1.37 and his Corollary 1.36** — the
two propositions in the form Jung states them.

> If `D` and `D → D` are domains, then `D` is bifinite.

Discharging `JungNets.Theorem137` and `JungFinite.FixedPointOfCompactDeflationIsCompact`
closes Theorem 18 outright; nothing else is outstanding on the route. The proof is
`theorem_18_of_jung_theorem_1_37_chains` after `JungNets.Theorem137.toChains`. -/
theorem theorem_18_of_jung_theorem_1_37_and_jung_corollary_1_36
    (h137 : JungNets.Theorem137 α)
    (hcor : JungFinite.FixedPointOfCompactDeflationIsCompact α) :
    IsBifinite α :=
  theorem_18_of_jung_theorem_1_37_chains h137.toChains hcor

/-- **Theorem 18 with the paper's own conclusion**: `D` is bifinite in the sense
of Gunter & Scott's §6 definition — the finitary projections of finite image are
countable, directed, and join to the identity.

The step from `IsBifinite` to `Recovered.IsBifiniteViaProjections` is
`Recovered.theorem_14`, whose right-hand side is `Domain α ∧ IsBifinite α`; the
`Domain α` conjunct is Theorem 18's own first hypothesis. This declaration exists
so that the identification of the two readings of "bifinite" is checked by the
kernel wherever Theorem 18 is cited, rather than left to a docstring. -/
theorem theorem_18_viaProjections_of_jung_theorem_1_37
    (h137 : JungNets.Theorem137 α)
    (hcor : JungFinite.FixedPointOfCompactDeflationIsCompact α) :
    Recovered.IsBifiniteViaProjections α :=
  Recovered.theorem_14.mpr ⟨inferInstance, theorem_18_of_jung_theorem_1_37_and_jung_corollary_1_36 h137 hcor⟩

end ScottDomains.Theorem18
