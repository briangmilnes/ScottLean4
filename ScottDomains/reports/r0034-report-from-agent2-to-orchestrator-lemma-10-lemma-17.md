---
round: r0034
from: agent2
to: orchestrator
subject: lemma-10-lemma-17
date: 2026-0807-07:19
started: 2026-0806-22:41
finished: 2026-0807-07:19
related:
  - plans/r0034-plan-from-orchestrator-to-agent2-lemma-10-lemma-17.md
  - docs/PaperInventory.md
---

# r0034 agent2 — Lemma 10 at 7 of 7, Lemma 17 at 10 of 10

All six missing conjuncts are proved. Both lemmas are additionally stated as a
single theorem each, so the conjunct count is now checked by the kernel rather
than tracked in prose.

## Measured outcome

| # | measurement | value |
| - | ----------- | ----- |
| 1 | Lemma 10 conjuncts proved | **7 of 7** |
| 2 | Lemma 17 conjuncts proved | **10 of 10** |
| 3 | new conjuncts this round | 6 (`+` twice, `◦→`, `D♮`, `D♯`, `D♭`) |
| 4 | new `sorry` | 0 |
| 5 | `sorry` in the library, before and after | 8, in 2 files (`Skeleton/Recovered.lean` ×7, `Skeleton/Section6.lean` ×1) — unchanged |
| 6 | full build | 0 errors, 0 lake errors, 0 warnings beyond `sorry` (1076 jobs) |
| 7 | new modules | 4 |
| 8 | new lines | 957 |
| 9 | new declarations | 49 |
| 10 | library totals after | 49 modules, 15005 lines, 698 theorem-ish declarations |
| 11 | axioms of every new declaration | `[propext, Classical.choice, Quot.sound]`; none depends on `sorryAx` |

## The two roll-up theorems

`ScottDomains/ClosureProperties.lean` states each lemma once, as the conjunction
over the paper's own list of operators. This is the acceptance artifact: a
missing conjunct is now a type error, not an absence.

    theorem lemma10 [Domain α] [BoundedComplete α] [Domain β] [BoundedComplete β] :
        BoundedComplete (ScottHom α β) ∧ BoundedComplete (StrictHom α β) ∧
        BoundedComplete (α × β) ∧ BoundedComplete (Smash α β) ∧
        BoundedComplete (SeparatedSum α β) ∧ BoundedComplete (CoalescedSum α β) ∧
        BoundedComplete (WithBot α)

    theorem lemma17 [Domain α] [Domain β] [BoundedComplete β]
        (h₁ : IsBifinite α) (h₂ : IsBifinite β) :
        IsBifinite (ScottHom α β) ∧ IsBifinite (StrictHom α β) ∧
        IsBifinite (α × β) ∧ IsBifinite (Smash α β) ∧
        IsBifinite (SeparatedSum α β) ∧ IsBifinite (CoalescedSum α β) ∧
        IsBifinite (WithBot α) ∧ IsBifinite (Plotkin.Powerdomain α) ∧
        IsBifinite (Smyth.Powerdomain α) ∧ IsBifinite (Hoare.Powerdomain α)

## Conjunct-by-conjunct

| # | operator | Lemma 10 | Lemma 17 |
| - | -------- | -------- | -------- |
| 1 | `D → E` | `ScottHom`'s `BoundedComplete` instance (r0007) | `lem17_fun` (r0027) |
| 2 | `D →⊥ E` | `lem10_strict` (r0027) | **`lem17_strictFun` (r0034)** |
| 3 | `D × E` | `lem10_prod` (r0027) | `lem17_prod` (r0027) |
| 4 | `D ⊗ E` | `lem10_smash` (r0027) | `lem17_smash` (r0028) |
| 5 | `D + E` | **`lem10_separated` (r0034)** | **`lem17_separated` (r0034)** |
| 6 | `D ⊕ E` | `lem10_sum` (r0028) | `lem17_sum` (r0028) |
| 7 | `D⊥` | `lem10_lift` (r0027) | `lem17_lift` (r0027) |
| 8 | `D♮` | — | **`lem17_plotkin` (r0034)** |
| 9 | `D♯` | — | **`lem17_smyth` (r0034)** |
| 10 | `D♭` | — | **`lem17_hoare` (r0034)** |

## What the PDF says, checked rather than paraphrased

The plan's rule 5 was decisive twice.

`pdftotext -layout` on `papers/Gunter Scott 1990.pdf` renders Lemma 10 (§4.5) as
seven operators, not six: the extraction in `Skeleton/Lemma10.lean`'s docstring
lists `D + E` and drops `D ⊕ E`, because `⊕` prints as a blank in the extracted
text and the two names collapsed. §4.4 settles which is which:

> Given cpo's `D` and `E`, we define the **separated sum** `D + E` to be the cpo
> `D⊥ ⊕ E⊥`.

So `+` is a *defined* operator — the coalesced sum of the two lifts — and the
conjunct proved in r0028 over `CoalescedSum` is `⊕`, not `+`. The plan's expected
route is exactly the paper's definition, and that is how both `+` conjuncts are
proved.

Lemma 17 (§6.2) lists ten operators, the last three being `D♮`, `D♯` and `D♭`;
its proof sketch works `D♮` out in the powerdomain of a finitary projection with
finite image, which is what the proof below does on the basis.

## Three findings

**1. `D⊥` was not a domain.** `Lift.lean` (r0027) supplied `WithBot α` as a cpo
only. Both `⊕` conjuncts are stated for *domains*, so `D + E = D⊥ ⊕ E⊥` could not
even be stated until `Domain (WithBot α)` existed. `SeparatedSum.lean` proves it:
`compactsBelow_coe` gives `K(D⊥) ∩ ↓↑a = {⊥} ∪ ↑(K(D) ∩ ↓a)` from r0027's
`isCompactElement_coe_iff`, algebraicity follows in four cases, and countability
of `K(D⊥)` is countability of `K(D)` plus one point. `liftIsAlgebraic` and
`liftDomain` are instances, so nothing downstream has to thread them.

**2. The strict function space needed strictification, in one direction only.**
`K(D →⊥ E) = K(D → E) ∩ (D →⊥ E)` is what lets `(q, p)` be reused verbatim, and
the two inclusions cost very different amounts:

* A strict `f` compact in `D → E` is compact in `D →⊥ E` in four lines, because
  the suprema of the subtype *are* the ambient suprema (`StrictHom.lean` — the
  one construction in the development whose supremum needs no case split).
* The converse is not four lines. A directed family in `D → E` need not be
  strict, so compactness in the subtype says nothing about it. The repair is
  `σ g = (x ↦ if x = ⊥ then ⊥ else g x)`: continuous, below `g`, fixing the
  strict functions, and carrying the least upper bound of a directed family to
  the least upper bound of the strictified family. Its continuity is the one step
  with content — on a directed `d` with `⨆d ≠ ⊥` some `x₀ ∈ d` is not `⊥`, and
  `g ⊥ ≤ g x₀ = σ g x₀` is why discarding the value at `⊥` does not lower the
  supremum.

`lem17_fun`'s step-function argument is factored out as
`exists_finite_projection_fixing`, which returns `p`, `q`, their projection
proofs, `p ⊥ = ⊥`, `q ⊥ = ⊥`, finiteness of `im (q, p)`, and `(q, p) f = f` for
each `f ∈ u`. `Skeleton/Lemma17.lean` is agent3's file and was **not edited**;
the factored version is a separate theorem in `ClosureProperties/StrictFunction.lean`.

**3. The three powerdomain conjuncts are one argument, and the obvious candidate
is wrong for one of them.** Since `IsBifinite` is the Plotkin condition on the
basis and Theorem 11 gives `K(D♮) = {↓u | u ∈ Pf(K(D))}` with `principal`
order-reflecting, the claim reduces to a statement about the *pre-order*:

    isNormalIn_image_principal : SelectsGreatest M → principal '' M ◁ compacts (IdealCompletion P)

where `SelectsGreatest M` says `M` has a greatest member below every `w`. Then
for a finite normal `N ◁ K(D)`, `p_N y` is the greatest member of `N ∩ ↓y`
(finite, nonempty and directed), and `Pf(N)` selects greatest approximants with
witness `p_N[w]` — the image of `w` under `p_N`, which is the paper's `p♮`.

The non-obvious part: the *Hoare-maximal* candidate `{n ∈ N | ∃ y ∈ w, n ⊑ y}` —
the largest subset of `N` that is `⊑♭`-below `w` — is greatest for `⊑♭` but
**not** for `⊑♮`. Its Smyth conjunct requires, for `x, z ∈ N ∩ ↓y`, that `x ⊑ z`;
normality gives only that both lie under `p_N y`. Taking the image under `p_N`
instead is greatest for all three orderings, which is why one lemma covers
`D♭`, `D♯` and `D♮`.

Neither countability of `K(D)` nor bounded completeness is used in the
powerdomain argument. `[Domain D]` enters only through `Countable` on the
pre-order, which Theorem 11 consumes to make the powerdomain a domain at all.

## Files

| # | file | lines | decls | content |
| - | ---- | ----- | ----- | ------- |
| 1 | `ScottDomains/ClosureProperties.lean` | 107 | 2 | `lemma10`, `lemma17` — the two roll-ups |
| 2 | `ScottDomains/ClosureProperties/SeparatedSum.lean` | 164 | 8 | `Domain (WithBot α)`, `SeparatedSum`, `lem10_separated`, `lem17_separated` |
| 3 | `ScottDomains/ClosureProperties/StrictFunction.lean` | 343 | 18 | strictification, `K(D →⊥ E)` both ways, `exists_finite_projection_fixing`, `lem17_strictFun` |
| 4 | `ScottDomains/ClosureProperties/Powerdomain.lean` | 343 | 21 | `SelectsGreatest`, `isNormalIn_image_principal`, `isBifinite_idealCompletion`, `normalGreatest`, `lem17_hoare`, `lem17_smyth`, `lem17_plotkin` |

Every declaration is under namespace `ScottDomains.ClosureProperties`, per the
plan's collision rule. No file outside `ScottDomains/ClosureProperties*` was
edited: `Skeleton/Lemma10.lean`, `Skeleton/Lemma17.lean`, `Skeleton/Sum.lean` and
the three `Powerdomain/` modules are untouched.

## For the orchestrator

`docs/PaperInventory.md` rows 2 and 2b move from partial to complete: Lemma 10 at
7 of 7 conjuncts, Lemma 17 at 10 of 10. Rows for the powerdomain operators may
now cite `lemma17`'s last three components rather than recording them as dropped
from the extraction. The paraphrase in `Skeleton/Lemma10.lean`'s docstring is
still six operators wide and undercounts the paper's list by one (`D ⊕ E`); that
file is agent1's and was not edited.

Two hypotheses are carried that the paper's sentences do not name, and both are
worth an inventory note rather than a silent pass:

1. `[BoundedComplete β]` in the `→` and `→⊥` conjuncts of Lemma 17. It comes from
   the step-function decomposition of a compact function, not from the paper's
   argument. §6 exists precisely because bifiniteness does not need it, so
   removing it is a real open item.
2. `[Domain _]` on each operand of Lemma 17, spent on the countability half only.
