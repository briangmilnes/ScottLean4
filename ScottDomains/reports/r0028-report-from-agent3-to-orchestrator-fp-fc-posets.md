---
round: r0028
from: agent3
to: orchestrator
subject: fp-fc-posets
date: 2026-0806-20:30
started: 2026-0806-19:05
finished: 2026-0806-20:30
related:
  - plans/r0028-plan-from-orchestrator-to-orchestrator-five-fold-parallel.md
---

# r0028 stream 3 — `Fp(D)` and `Fc(D)` as posets, Theorem 16, Lemma 20

## Measurement

| # | Quantity | Value |
| -- | -------- | ----- |
| 1 | Final build | `Build completed successfully (964 jobs).` |
| 2 | Errors | 0 |
| 3 | Warnings from the two new files | 0 |
| 4 | `sorry` in `ScottDomains/` | 1 — `thm18` only, agent4's, untouched |
| 5 | New modules / lines | 2 / 816 (`FinitaryProjectionPoset.lean` 731, `Skeleton/Section6b.lean` 85) |
| 6 | New declarations | 51 |
| 7 | Numbered results landed | 2 — Theorem 16 (first conjunct), Lemma 20 |
| 8 | Axioms of every new result | `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx` |
| 9 | Commit | `8319c17` on branch `agent3`, not pushed |

## The posets

Both `Fp(D)` and `Fc(D)` are subsets of the function space, `Set (ScottHom α α)`,
and the order on each is the **pointwise order** `p ⊑ q ⟺ ∀ x, p(x) ⊑ q(x)`
inherited from `D → D` through `Subtype.partialOrder`. `Fp.le_def` and
`Fc.le_def` record that by `Iff.rfl`. Three reasons fix the choice, stated in the
module docstring: every statement the paper makes about these posets is pointwise
(Theorem 6's monotonicity clause, Lemma 17's `⨆M = id`); Theorem 16's second
conjunct calls the inclusion into `D → D` an embedding, which presupposes the
subspace order; and on projections the pointwise order coincides with inclusion
of bases, which is what makes Theorem 6 an order isomorphism.

`Fc(D)` needed a definition of *finitary closure* to exist at all:
`IsFinitaryClosure r := ∃ hr : IsClosure r, Domain im(r)`, the exact dual of
`ScottHom.IsFinitaryProjection`.

## Lemma 19 had to be strengthened first

`Skeleton/Section6.lean`'s `lem19` asserts only that `im(r)` carries **a cpo
structure**. Lemma 20 cannot be proved from that: `Fc(D)` is defined by "`im(r)`
is a domain", so the supremum of a directed family of closures is a *member of
`Fc(D)*` only once every closure's image is known to be a domain. So
`IsClosure.domain_range` proves Lemma 19 at the paper's strength — `im(r)` is a
domain — with the basis the paper names, `{r(k) | k ∈ K(D)}`:

* `IsClosure.isCompactElement_apply` — `r(k)` is compact in `im(r)` for compact
  `k`;
* `isLUB_closureApprox` — `y = r(y)` is the least upper bound of
  `{r(k) | k ∈ K(D), k ⊑ y}`, by continuity of `r`;
* `IsClosure.countable_compacts_range` — every compact of `im(r)` *is* some
  `r(k)`, so the basis is countable.

`Section6.lean` was not edited; the strengthening lives in the new file and the
docstring says so.

## Lemma 20

`Fc.completePartialOrder` is the witness. `id` is the least element (every
closure is inflationary), and the least upper bound of a directed family is the
pointwise supremum, a closure by `isClosure_sSup`.

Two design points worth carrying forward:

* `sSup` branches on **membership of the candidate value in `Fc α`**, per the
  rule the `ScottHom`/`Smash` defects established — not on directedness.
* The candidate is `sSup (insert id (val '' S))`, not `sSup (val '' S)`.
  Adjoining `id` changes no supremum of a nonempty family and makes the inserted
  family nonempty and directed for *every* directed `S`, so `S = ∅` needs no
  separate case. Without it the empty case is real: `sSup ∅` in `ScottHom` is the
  constant `⊥` function, which is not a closure.

## Theorem 16 and the mub argument

The proof runs through Theorem 6, as the paper's sketch says: `Fp(D)` is
order-isomorphic to the normal subposets of `K(D)` under `⊆`
(`Fp.le_iff_fpBasis_subset`), so it suffices that *those* form an algebraic
lattice. The whole argument turns on one fact about **minimal upper bounds**:

* `IsPlotkinOrder.exists_isMinimalUpperBound` — in a Plotkin order every upper
  bound `c` of a pair dominates a minimal upper bound `m ⊑ c`. Proof: take the
  *finite* normal `N ∋ a, b, c` the Plotkin condition supplies and minimize
  inside the finite set `{y ∈ N | a, b ⊑ y ⊑ c}`; normality upgrades minimality
  there to minimality in all of `A`.
* `IsNormalIn.mem_of_isMinimalUpperBound` — a normal subposet containing `a` and
  `b` contains **every** minimal upper bound of `a, b`.

Together these give `isNormalIn_sInter`: the normal subposets of a Plotkin order
are closed under **arbitrary** intersection, because the directedness witness can
be taken to be a minimal upper bound, which then lies in every member of the
family at once. That is the closure system, and everything else follows:
`Fp.completeLattice` via `completeLatticeOfInf`, compactness of `p_N` for finite
`N` via "the basis of a directed least upper bound is the union of the bases",
and enough compact elements via `normalClosure_finite`.

This is worth flagging for **agent4**: bifiniteness is spent here through
*finiteness alone*. No `U^∞` operator and no König argument were needed — a
minimal element of a finite set does the work. That may or may not shorten
Theorem 18; it certainly shows the mub vocabulary is now partly in the tree
(`IsMinimalUpperBound`, `IsPlotkinOrder.exists_isMinimalUpperBound`).

## Does `IsCompactlyGenerated` fit?

**Yes, without adjustment.** Mathlib's algebraic lattice is `CompleteLattice` +
`IsCompactlyGenerated`, and its `IsCompactElement` is *the same predicate* this
development already uses for `K(D)` — `ScottDomains.WayBelow` is defined from it
— so "compactly generated" here means exactly "every finitary projection is the
least upper bound of the finitary projections with a finite basis", which is what
`Fp.isCompactlyGenerated` proves.

One accommodation was forced: `IsBifinite` is a `def`-level proposition, not a
class, so `CompleteLattice ↥(Fp α)` cannot be an `instance`. `thm16` is therefore
existential, with a conjunct pinning the lattice order to the pointwise order
(`Iff.rfl`, since `completeLatticeOfInf` splices in the ambient `PartialOrder`).
Without that conjunct the existential would be satisfied by any complete lattice
whatever and would say nothing.

## What is *not* proved

Theorem 16's **second** conjunct, that the inclusion `i : Fp(D) ↪ (D → D)` is an
embedding, is not stated. It is a separate claim about an embedding–projection
pair, and the paper's sketch does not obviously produce the projection half
`i ∘ s ⊑ id`. Concretely: `S_f = {x ∈ K(D) | x ⊑ f(x)}` is in general **not**
normal, so the least normal `N_f ⊇ S_f` is strictly larger — a minimal upper
bound `m` of `a, b ∈ S_f` must lie in `N_f`, but `f(m)` is only an upper bound of
`{a, b}` and need not dominate the *minimal* one `m`, so `m ⊑ f(m)` can fail and
with it `p_{N_f} ⊑ f`. Recording a guessed proof strategy would be worse than
recording the gap. The assigned statement, and the `PaperInventory.md` row, are
the algebraic-lattice conjunct, which is proved.

## Naming to check at merge

`ScottHom.id` is new (the identity of the function space; the `⊤` of `Fp(D)` and
the `⊥` of `Fc(D)`). If agent5's closure work introduced the same name in
`UniversalDomain.lean`, the merge will report a duplicate declaration; the fix is
to keep one copy in whichever file is imported earlier.

`PaperInventory.md` and `INDEX.md` were not edited — the inventory is shared
across all five streams this round, and `INDEX.md` does not list `ScottDomains`
modules. Rows 260 and 264 of `docs/PaperInventory.md` (Theorem 16, Lemma 20) are
the ones to flip.
