---
round: r0032
from: agent1
to: orchestrator
subject: lemma-24-theorem-25
date: 2026-0806-21:10
started: 2026-0806-20:35
finished: 2026-0806-21:10
related: plans/r0032-plan-from-orchestrator-to-agent1-lemma-24-theorem-25.md
---

# r0032 agent1 — Lemma 24 and Theorem 25: universality of `P N`

## Result

Both statements are proved and kernel-accepted, together with the instance at
`U = P N`. One new file, `ScottDomains/ScottDomains/Universality.lean`, 546
lines, 28 declarations, **0 `sorry`**, namespace `ScottDomains.Universality`
throughout. No shared module was edited.

Final `lake build` line, verbatim from
`ScottDomains/logs/compile-20260806-210312.agent1.log`:

    Build completed successfully (1067 jobs).

and the wrapper's own summary line:

    compile: exit 0 · wall 0:02.64 · mem 1677 MiB single / 2221 MiB tree pss / 8822 MiB tree rss · jobs 1067 · diagnostics 0 · lake errors 0 · sorry 1 · other warnings 0

Errors 0, warnings 0. The `sorry 1` is `Skeleton/Section6.lean:196` (Theorem 18),
pre-existing since r0028 (`cfaf320`) and untouched by this round; the count in
`Universality.lean` is 0 by `grep -c sorry`.

## The paper's text

Extracted with `pdftotext -layout` from `ScottDomains/papers/Gunter Scott 1990.pdf`,
§7.2, and quoted in the module docstring:

> **Lemma 24** Let `U` be a non-trivial cpo. If the product and function space
> operators can be represented over `U`, then there are non-trivial domains `D`
> and `E` such that `E ≅ E × E` and `D ≅ D → E`.

> **Theorem 25** If `U` is a non-trivial domain which represents products and
> function spaces, then there is a non-trivial domain `D` such that
> `D ≅ D × D ≅ D → D` and `D` is the image of a closure on `U`.

> We note, in fact, that `D` will have `P N` itself represented by a closure on
> `U`. Hence, to get a non-trivial solution for `D ≅ D → D ≅ D × D`, take `U` in
> the theorem to be `P N`.

## The statements proved

    theorem lem24 (U : Type u) [CompletePartialOrder U] [Nontrivial U]
        (hprod : IsRepresentable₂ U prodCpo) (hfun : IsRepresentable₂ U Cpo.funSpace) :
        ∃ D E : Cpo.{u}, Nontrivial D.carrier ∧ Nontrivial E.carrier ∧
          IsClosureOf D (cpoOf U) ∧ IsClosureOf E (cpoOf U) ∧
          Iso E (prodCpo E E) ∧ Iso D (Cpo.funSpace D E)

    theorem thm25 (U : Type u) [CompletePartialOrder U] [Nontrivial U]
        (hprod : IsRepresentable₂ U prodCpo) (hfun : IsRepresentable₂ U Cpo.funSpace) :
        ∃ D : Cpo.{u}, Nontrivial D.carrier ∧ IsClosureOf D (cpoOf U) ∧
          Iso D (prodCpo D D) ∧ Iso D (Cpo.funSpace D D)

    theorem thm25_powerset :
        ∃ D : Cpo.{0}, Nontrivial D.carrier ∧ IsClosureOf D powersetCpo ∧
          Iso D (prodCpo D D) ∧ Iso D (Cpo.funSpace D D)

    theorem thm25_isUniversal :
        ∃ D : Cpo.{0}, Nontrivial D.carrier ∧ Iso D (prodCpo D D) ∧
          Iso D (Cpo.funSpace D D) ∧ IsUniversal powersetCpo (fun X => Iso X D)

`IsClosureOf` and `IsUniversal` are `RecursiveDomain.lean`'s (r0029);
`IsRepresentable₂`, `Cpo`, `Cpo.funSpace`, `ClosurePoset` are
`UniversalDomain.lean`'s (r0028); `prodCpo` is `Powerdomain/Universal.lean`'s
(r0031). `thm25_powerset` is `thm25 (Set ℕ) isRepresentable_prod lem23` — one
line, both hypotheses discharged by the two results the plan named.

Lemma 24 is kept as the *setup*, not folded into Theorem 25: it delivers the pair
`(D, E)` with `E ≅ E × E` and `D ≅ D → E`, and Theorem 25 consumes exactly that
pair. Theorem 25's proof is the paper's two displayed chains and nothing else.

## Which universality predicate Theorem 25 concludes, and why

**`Recursive.IsUniversal`** — the image-of-a-closure phrasing — via
`thm25_isUniversal`. The reasoning, in three steps.

Theorem 25's own conclusion is not a universality statement about a class. It is
an *existence* statement about one domain `D`, ending "and `D` is the image of a
closure on `U`". That last clause is literally `Recursive.IsClosureOf D (cpoOf U)`:
`IsClosureOf E D := ∃ r : ClosurePoset D.carrier, Nonempty (E.carrier ≃o r.image.carrier)`.
So `thm25` carries `IsClosureOf` as a conjunct rather than inventing a wrapper.

`Recursive.IsUniversal U C := ∀ D, C D → IsClosureOf D U` is the universal
quantification of that same relation over a class `C`. The largest class Theorem
25 supports is `D`'s isomorphism class, because `IsClosureOf` is invariant in its
first argument under `≅` (`IsClosureOf.of_iso`). Hence

    IsUniversal powersetCpo (fun X => Iso X D)

is exactly what the theorem proves — and it would be false to state it for the
class of *all* cpos satisfying `X ≅ X × X ≅ X → X`, since nothing in §7.2 shows
every such cpo is a closure of `P N`.

`IsUniversalRetract` is the wrong predicate here. It asks for a closure pair
`r : U → D`, `s : D → U`, which is Theorem 22's conclusion shape; Theorem 25
produces a closure *on* `U` and takes its image, which is the other phrasing.
`IsUniversal.of_retract` runs only in the direction retract ⟹ closure-image, so
the retract form is not derivable from what Theorem 25 gives.

No third formalization of universality was introduced.

## Is `P N` shown universal?

Yes, in the sense Theorem 25 establishes and in no larger sense:
`thm25_powerset` gives a non-trivial cpo `D` which is the image of a closure on
`P N` and satisfies `D ≅ D × D` and `D ≅ D → D`; `thm25_isUniversal` restates
that as `IsUniversal powersetCpo` over `D`'s isomorphism class. This is a
different statement from the already-proved `Recursive.powersetCpo_isUniversal`
(Theorem 22: `P N` is universal for the countably based algebraic lattices), and
both use the same predicate.

## "Non-trivial" — an explicit hypothesis, and expressible

The plan asked whether the paper's "non-trivial" is something the development
cannot yet express. It is expressible: the paper fixes the meaning by its own
counterexample — the one-point cpo `I`, for which `I ≅ I → I` holds vacuously —
so *non-trivial* is "at least two elements", which is Mathlib's `Nontrivial`.
It is carried as an explicit instance hypothesis `[Nontrivial U]` on `lem24` and
`thm25`, never assumed silently, and at `U = P N` it is discharged by
`Set.nontrivial_of_nonempty`.

## Two places the formal statement differs from the paper's prose

Both are deliberate and both are recorded in the module docstring.

**Stronger.** Lemma 24 additionally concludes that `D` and `E` are closures of
`U`. Its own proof needs this ("Now, `E` is a closure of `U` so `G(X) = X → E`
is representable over `U`"), and Theorem 25's "`D` is the image of a closure on
`U`" is nothing else. `Recursive.thm21` discards the closure it fixes, so
`thm21_image` restates Theorem 21 retaining it — same proof, wider existential.

**Weaker.** The paper says "non-trivial **domains** `D` and `E`". Its own proof
produces cpos: "Hence there is a **cpo** `D ≅ D → E`". Lemma 24's hypothesis is a
non-trivial *cpo*, Theorem 21 is stated over a cpo, and `Skeleton/Section6.lean`'s
`lem19` establishes only that `im(r)` carries a `CompletePartialOrder`, not that
it is algebraic with a countable basis — the gap `UniversalDomain.lean` already
records against `ClosurePoset`. So `D` and `E` are `Cpo`, which is what the proof
supports. Correspondingly `thm25`'s hypothesis is `U` a **cpo**, not the paper's
"non-trivial domain": no step of the proof spends algebraicity or countability of
`K(U)`, so the theorem proved is strictly stronger than the one stated.

## What had to be built, and why

`Product.lean` and `Currying.lean` supply Lemma 8 parts 1–4, but only for bare
carrier types. Both §7.2 proofs rewrite under `×` and `→` at almost every step,
so `≅` must be a **congruence**, and Mathlib has no `OrderIso.prodCongr` (checked
by grep over all of Mathlib for `prodCongr` at `≃o`). Seven toolkit declarations
close that gap:

| # | Declaration | Content |
| -- | ----------- | ------- |
| 1 | `scottContinuous_orderIso` | an order isomorphism is Scott continuous — one line from `OrderIso.isLUB_image'` |
| 2 | `scottContinuous_pairConst` / `…Right` | pairing with a constant, over **bare preorders** — `Currying.scottContinuous_pairLeft` demands `CompletePartialOrder`, which `ClosurePoset U` does not have as an instance |
| 3 | `prodOrderIso` | `×` is a congruence for `≃o` |
| 4 | `scottHomOrderIso` | `→` is a congruence for `≃o`, transport `g ↦ f ∘ g ∘ e⁻¹`, continuity from row 1 |
| 5 | `prodShuffle` | `((u₁,a₁),(u₂,a₂)) ↦ (u₁,(u₂,(a₁,a₂)))`, the paper's `(U × A) × (U × A) ≅ U × (U × A × A)` |
| 6 | `nontrivial_scottHom` | `D → E` is non-trivial when `E` is — two constant maps, differing at `⊥` |
| 7 | `idClosureImageIso` | `im(id) ≅ U`, so the constant operator `X ↦ U` is representable |

Row 2's constraint is worth flagging for future rounds: `Recursive.closureCpo`
is deliberately not an instance (instance-diamond avoidance), so anything proved
about `Fc(U)` must be stated at `Preorder`/`PartialOrder` strength or take the
structure by `letI`.

Two derived operators are then represented over `U`:

* `isRepresentable_selfProdSquare` — `F(X) = U × (X × X)` from `×`, with
  `R_F(r) = R×(id, R×(r,r))`; the constant `id` supplies the `U` factor.
* `isRepresentable_funSpaceConst` — `G(X) = X → E` from `→` and `IsClosureOf E U`,
  with `R_G(r) = R→(r, c)` for the closure `c` with `im(c) ≅ E`.

These two are the formal content of the paper's remark that a constant operator
`X ↦ D` is representable over `U` exactly when `D` is a closure of `U`, used only
in the direction and at the two closures the proof needs.

## Axiom audit

`#print axioms` was run on all 28 declarations, the output recorded in a trailing
comment in the file, and the commands removed so the build emits no `info` lines
(the convention `Powerdomain/Universal.lean` established). **No declaration
depends on `sorryAx`.** Three are axiom-free: `scottContinuous_pairConst`,
`scottContinuous_pairConstRight`, `cpoOf`. Every other declaration depends only
on `propext`, `Quot.sound`, and — where `ScottHom`'s cpo structure is in play —
`Classical.choice`, which enters through the same door as in `lem23` and
`isRepresentable_prod`: `ScottHom`'s `SupSet` instance is a `dite` on an
undecidable continuity predicate, plus `thm22`'s choice of a basis enumeration.

Named results: `lem24`, `thm25`, `thm25_powerset`, `thm25_isUniversal` all
report `[propext, Classical.choice, Quot.sound]`.

## Unproved

Nothing in the plan's deliverables is unproved. Two adjacent facts are *not*
claimed, and neither is an obstacle to this round:

1. That `D` and `E` are **domains** (algebraic, countable basis) rather than
   cpos. This needs Lemma 19's full strength — `im(r)` is a domain — which
   `Skeleton/Section6.lean` does not currently supply, and
   `FinitaryProjectionPoset.mem_Fc_iff` supplies only over `[Domain α]`. It is a
   separable piece of work and would strengthen `lem24`/`thm25` in place.
2. The paper's parenthetical "`D` will have `P N` itself represented by a
   closure on `U`". The paper gives no argument for it and it is not used by
   Theorem 25.

## Files and commit

Changed:

* `ScottDomains/ScottDomains/Universality.lean` — new, 546 lines
* `INDEX.md` — one entry added for the new module
* `ScottDomains/logs/compile-*.agent1.log` — build telemetry
* this report

Commit SHAs on branch `agent1`, both by `scripts/gitcp.sh`:

| # | SHA | Contents |
| -- | --- | -------- |
| 1 | `e5b7a45` | `Universality.lean`, `INDEX.md`, build logs, this report |
| 2 | `9129671` | this table of SHAs |
| 3 | last commit on `agent1` | row 2's own SHA, filled in after it existed |

All three touch only this report except row 1, which carries the whole
deliverable.

Branch parent is `main` at `f4f9b00`, verified before work began. Not pushed and
no upstream set, per the plan; `gitcp.sh` reported `fatal: The current branch
agent1 has no upstream branch`, which is the documented expected outcome for an
`agentN`.
