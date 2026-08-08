---
round: r0041
from: agent1
to: orchestrator
subject: flat-cpo
date: 2026-0808-13:45
started: 2026-0808-13:02
finished: 2026-0808-13:45
related:
  - plans/r0041-plan-from-orchestrator-to-orchestrator-close-unstated.md
  - reports/r0040-report-from-agent1-to-orchestrator-property-coverage-s2-s3.md
  - reports/r0040-report-from-agent3-to-orchestrator-property-coverage-thm11-s5.md
---

# r0041, stream 1 — the flat cpo, §5's `N⊥` powerdomain calculations, and `(T × T)♮`

**Eleven properties targeted, eleven stated, eleven proved. No `sorry` added; the
development still holds exactly one, `Skeleton/Section6.lean:197`.**

Four new modules, 1843 lines, 114 new theorems. Every headline declaration
depends only on `propext`, `Classical.choice` and `Quot.sound`; none depends on
`sorryAx`.

## 1. Per-property status

`§ / p.` is the **printed** page of `ScottDomains/papers/Gunter Scott 1990.pdf`
(physical = printed + 1). Every sentence below was read off a 170 dpi render of
the physical page, not off `pdftotext`, which renders `♮`/`♯`/`♭` as `\`/`]`/`[`.

| # | Property (paper's sentence) | § / p. | r0040 row | Status | Declaration |
| -- | --------------------------- | ------ | --------- | ------ | ----------- |
| 1 | the flat cpo `S⊥` — "adding a new element `⊥` to `S` … `x ⊑ y` iff `x = ⊥` or `x = y`" | 2.1 / 3 | (the missing construction) | **proved** | `Flat`, `Flat.instCompletePartialOrder` |
| 2 | `K(N⊥) = N⊥` | 5.2 / 26 | — | **proved** | `Flat.compacts_eq_univ` |
| 3 | `(N⊥)♭` is isomorphic to `P N`, all subsets of `N` under subset inclusion | 5.2 / 26 | a3-16 | **proved** | `Flat.hoare_natBot_orderIso_powerset` |
| 4 | `(N⊥)♯` is isomorphic to `{N} ∪ P*f(N)` ordered by superset inclusion | 5.2 / 26 | a3-17 | **proved** | `Flat.smyth_natBot_orderIso` |
| 5 | for `u, v ∈ P*f(N⊥)`: `u ⊢♮ v` iff (1) `⊥ ∈ v` and `u ⊇ v`, or (2) `u = v` | 5.2 / 26 | a3-18 | **proved, with the printed clause 1 refuted** | `Flat.plotkin_le_iff`, `Flat.plotkin_printed_clause_one_fails` |
| 6 | `(N⊥)♮` corresponds to the finite non-empty subsets of `N` unioned with the arbitrary subsets of `N⊥` containing `⊥` | 5.2 / 26 | a3-19 | **proved** | `Flat.plotkin_natBot_orderIso` |
| 7 | in `(N⊥)♯`: `{\|1, ⊥\|} = ⊥ = {\|⊥\|}` | 5.3 / 27 | a3-25 | **proved** | `Flat.smyth_oneBot_eq_bot_eq_unit_bot` |
| 8 | in `(N⊥)♭`: `{\|1, ⊥\|} = {\|1\|}`, and `{\|1, ⊥\|} ≠ ⊥` | 5.3 / 27 | a3-26 | **proved** | `Flat.hoare_oneBot_eq_one`, `Flat.hoare_oneBot_ne_bot` |
| 9 | in `(N⊥)♮`: `{\|1, ⊥\|}`, `{\|1\|}`, `{\|⊥\|}` are all distinct | 5.3 / 27 | a3-27 | **proved** | `Flat.plotkin_three_distinct` |
| 10 | "only the convex powerdomain `(·)♮` does not take bounded complete domains to bounded complete domains … `(T × T)♮` is therefore not bounded complete" | 6 / **29** | a3 cross-ref (§6) | **proved** | `Flat.convex_does_not_preserve_boundedComplete`, `Flat.not_boundedComplete_plotkin_TT` |
| 11 | "`u′` and `v′` are *minimal* upper bounds for `{u, v}` with respect to the ordering `⊢♮`" | 6 / 29 | a3 cross-ref | **proved** | `Flat.setU'_minimal`, `Flat.setV'_minimal`, `Flat.not_setU'_le_setV'` |

Three further rows of r0040's §2/§3 table were closed because the same
construction unblocks them:

| # | Property | § / p. | r0040 row | Status | Declaration |
| -- | -------- | ------ | --------- | ------ | ----------- |
| 12 | "any monotone function `f : N⊥ → E` is continuous" | 2.1 / 4 | a1-34 (N7) | **proved** | `Flat.scottContinuous_of_monotone` |
| 13 | "the ordinal `ω` … is not a cpo" | 2.1 / 3 | a1-29 (N3) | **proved** | `Flat.omega_not_cpo` |
| 14 | "the function `f : ω⊤ → O` … is monotone, but it is not continuous" | 2.1 / 4 | a1-35 (N8) | **proved** | `Flat.omegaTop_monotone_not_continuous` |

**14 stated, 14 proved, 0 as `Prop` obstructions.**

### Rows in the plan's group of 16 that this round did *not* close

| # | Property | § / p. | Why not |
| -- | -------- | ------ | ------- |
| 1 | "`Q` … fail[s] to be a cpo" | 2.1 / 3 | needs `ℝ` or a Dedekind-cut argument; `ℝ` still occurs 0 times in the package. Independent of the flat cpo |
| 2 | "the unit interval `[0,1]` … does form a cpo" | 2.1 / 3 | same; and row 38's cpo-continuity-vs-topological-continuity claim sits on it |
| 3 | "The compact elements of the domain `N⊥ → N⊥` are the functions with finite domain of definition" | 3 / 9 | now *statable* — `N⊥` exists — but it is a characterization of `K(N⊥ → N⊥)`, a function-space theorem, not a flat-cpo one |
| 4 | "the bounded complete domain `N⊥ ⊸ N⊥` lacks a top element and therefore fails to be an algebraic lattice" | 3.2 / 11 | same: statable now, and cheap next round |
| 5 | "all of the cpo's we have mentioned so far are domains" / "all the domains so far are bounded complete" | 3 / 9, 3.2 / 11 | meta-claims quantified over the whole example list, which still lacks `Q` and `[0,1]` |

Rows 3 and 4 are the cheapest work the flat cpo leaves for r0042: both are now
type-correct and neither needs a new carrier.

## 2. The construction, and why this one

**`Flat X` is an `inductive` with two constructors, `bot` and `up`, carrying its
own `PartialOrder`.** The alternatives were weighed and rejected:

| # | Candidate | Rejected because |
| -- | --------- | ---------------- |
| 1 | `WithBot X` | adjoins the bottom but keeps `X`'s order. `WithBot ℕ` and `WithBot Bool` are **linear**: `↑0 ≤ ↑1` and `↑false ≤ ↑true`. The flat order needs `X` **discrete**, and Mathlib has no discrete-order type synonym to feed `WithBot` |
| 2 | `WithBot` over a local `LE X := Eq` | a second, non-defeq `LE` instance on `ℕ` — exactly the incoherence `IdealCompletion`, `Hoare.Pf` and `Smyth.Basis` are type synonyms and structures to avoid |
| 3 | `def Flat X := Option X` | a plain `def` blocks instance search in both directions, so nothing is inherited anyway; and it leaves a reducibility hazard for no gain |

The `inductive` cannot pick up an unwanted instance, derives `DecidableEq`, and
gives the two-case recursor that every proof in the three downstream modules runs
on. `ScottDomains.Lift` (`WithBot` as a cpo, §4.4's `D⊥`) is a **different**
operator and the two do not overlap: `Lift` needs `[CompletePartialOrder X]`,
`Flat` needs nothing on `X`.

Everything about suprema in `X⊥` reduces to one lemma,
`Flat.mem_upperBounds_of_up_mem`: a non-`⊥` member of a directed set is its
greatest element. `flatSup`'s case split is on whether such a member exists, and
`Flat.mem_of_isLUB` — a directed set contains its own least upper bound — is what
makes row 12 immediate.

### Instances supplied

| # | Instance | Hypothesis on `X` |
| -- | -------- | ----------------- |
| 1 | `PartialOrder (Flat X)`, `OrderBot (Flat X)` | none |
| 2 | `CompletePartialOrder (Flat X)` | none (`noncomputable`: `flatSup` chooses the unique non-`⊥` member) |
| 3 | `IsAlgebraic (Flat X)` | none, via `isAlgebraic_of_forall_isCompactElement` — whose docstring in `Domain.lean` already anticipated the flat case |
| 4 | `Domain (Flat X)` | `[Countable X]` |
| 5 | `BoundedComplete (Flat X)` | none |
| 6 | `Countable (Flat X)` | `[Countable X]` |

### Non-degeneracy witness

`Prop`-valued classes with no instance are unfalsifiable and one-point orders
satisfy all three vacuously, so `T = Flat Bool` is checked explicitly:

* `Flat.truth_forall_eq` — `T` has exactly the three points `⊥`, `up true`, `up false`;
* `Flat.truth_nondegenerate` — `⊥ < up true`, `⊥ < up false`, and the two are
  **incomparable** in both directions. The incomparability is the load-bearing
  half: it is what `WithBot Bool` fails, and it is what makes `(T × T)♮`'s
  counterexample possible at all.

`Flat.truth_nondegenerate` **depends on no axioms whatsoever** — it is the only
declaration in the four modules of which that is true.

## 3. Two places where the paper's printed text is wrong

Both are kernel-checked, not editorial.

### 3.1 The printed characterization of `⊢♮` over `P*f(N⊥)` is false (§5.2, p. 26)

The paper prints

> `u ⊢♮ v` iff 1. `⊥ ∈ v` and `u ⊇ v` or 2. `u = v`.

Take `u = {1}`, `v = {1, ⊥}`. Then `u ⊢♯ v` holds because `⊥ ∈ v`, and `u ⊢♭ v`
holds because `1 ∈ u` covers `1 ∈ v` and `1 ⊒ ⊥` covers `⊥ ∈ v`; so `u ⊢♮ v`. But
`⊥ ∉ u`, so `u ⊉ v`, and `u ≠ v`. **Clause 1 as printed is strictly stronger than
the relation it characterizes.** The correct condition is

> `u ⊢♮ v` iff 1. `⊥ ∈ v` and `v ∖ {⊥} ⊆ u`, or 2. `u = v`,

which agrees with the paper's exactly when `⊥ ∈ u`. `Flat.plotkin_le_iff` proves
the corrected form and `Flat.plotkin_printed_clause_one_fails` refutes the printed
one at that witness. The paper's two *following* sentences — the principal ideals
at `⊥`-free sets, and `⋃x ⊆ ⋃y` for the rest — are both correct under the
corrected clause, and row 6's isomorphism is built on it.

### 3.2 §6's `{u, u′}` is a typo for `{u, v}` (§6, p. 29)

The printed sentence is *"Hence no least upper bound for `{u, u′}` exists"*, one
sentence after *"`u′` and `v′` are minimal upper bounds for `{u, v}`"*. If `u′` is
an upper bound of `{u, v}` it is trivially the least upper bound of `{u, u′}`, so
the printed pair cannot be what is meant. The Lean statement is for `{u, v}`.

**A third, smaller correction to the round's inputs.** My task brief and r0040's
agent3 report disagree on where §6's opening sits: the brief says printed page 30,
agent3 says printed 29. **Printed 29 is right** — printed 30 is §6.1, *Plotkin
orders*, which opens "The bifinite cpo's are motivated, in part, by
considerations from category theory". Both renders are in this session's record.

## 4. What the `(T × T)♮` refutation actually needs

The plan describes the argument as "`u′` and `v′` are minimal upper bounds, so no
least upper bound exists". That is the paper's argument **in the pre-order**, and
it does not transfer as stated: bounded completeness is a property of the *ideal
completion* `(T × T)♮`, whose elements are ideals, not finite sets. Two distinct
minimal upper bounds in the pre-order do not by themselves refute the existence of
a least upper bound among ideals.

What does transfer is one step longer and needs no minimality at all. A least
upper bound `I` of `{↓u, ↓v}` would contain `u` and `v`; being an ideal it is
directed, so it would contain a single `w` above both; and `I ≤ ↓u′` and
`I ≤ ↓v′` put `w` in both. `Flat.no_common_refinement` shows no such `w` exists,
and the contradiction is carried by **one** member `b` of `w`:

* sitting above `u` forces `b`'s second coordinate to be `true` or `false`, not `⊥`;
* sitting above `v` forces the same of the first;
* sitting below `u′` forces the two coordinates **equal**;
* sitting below `v′` forces them **different**.

Minimality is proved anyway, as `Flat.setU'_minimal` and `Flat.setV'_minimal`,
because the paper asserts it; `Flat.not_setU'_le_setV'` shows the two are
incomparable, which is what makes them *two* minimal upper bounds rather than one.

`Domain (T × T)` and `BoundedComplete (T × T)` are supplied as instances from
`PowerdomainRep.domain_prod` and `lem10_prod`, so
`Flat.convex_does_not_preserve_boundedComplete` states §6's opening sentence
complete: `T × T` **is** a bounded complete domain and its convex powerdomain is
**not** bounded complete.

## 5. What the isomorphism proofs cost

All three are order isomorphisms onto a concrete poset, built the same way. Two
generic tools were needed and neither existed:

* `Flat.exists_mem_upperBound` — a finite subset of an ideal is bounded inside the
  ideal. `Order.Ideal` carries only **binary** directedness, while the paper's own
  definition of *ideal* quantifies over arbitrary finite subsets. This is the
  induction that reconciles the two, and it is exactly the gap r0040's agent3 row
  14 labelled `P` (the ideal definition's finite-subset clause). Declared in this
  agent's namespace, not added to `IdealCompletion`, since its only consumers are
  here.
* concrete carriers as **`structure`s, never subtypes** — `SmythCarrier` and
  `PlotkinCarrier` both carry an order that is *not* `⊆`, so the subtype form
  would inherit `Subtype.partialOrder` and produce a second non-defeq
  `PartialOrder`. This is the same decision `Smyth.Basis` records, and it was
  measured: the first draft used subtypes and the build reported 11 diagnostics,
  all traceable to it.

| # | Isomorphism | Concrete poset | Order | Where the work is |
| -- | ----------- | -------------- | ----- | ----------------- |
| 1 | `(N⊥)♭ ≅ P N` | `Set ℕ` | `⊆` | the `⊇` half of the round trip: a finite `u` whose non-`⊥` part lies in `⋃x` is dominated by a single member of `x` |
| 2 | `(N⊥)♯ ≅ {N} ∪ P*f(N)` | `SmythCarrier` | **⊇** | surjectivity. The paper says a non-trivial ideal "is the principal ideal generated by the intersection of its non-trivial elements"; the Lean proof takes the `⊥`-free member of **least cardinality** instead, since on `⊥`-free points the Smyth order *is* reverse inclusion, and `Finset.eq_of_subset_of_card_le` collapses the directedness witness onto it |
| 3 | `(N⊥)♮ ≅ P*f(N) ∪ {S ⊆ N⊥ \| ⊥ ∈ S}` | `PlotkinCarrier` | `Ple`, the corrected `⊢♮` read on arbitrary subsets — the paper's "like the pre-ordering `⊢♮` but extended to include infinite sets" | surjectivity again, in two cases: a `⊥`-free member makes the ideal principal, and otherwise the ideal is `⋃x` and a finite-domination induction recovers it |

`Ple` is proved to be a partial order (`Ple.refl`, `Ple.trans`, `Ple.antisymm`)
and `Ple_pset_iff` proves it restricts on finite sets to the convex pre-order —
so the "extended ordering" is not a new definition but the same one.

## 6. Measured build counts

`scripts/counts.sh`, before and after:

| # | Measure | before (r0040 close) | after | Δ |
| -- | ------- | -------------------: | ----: | -: |
| 1 | modules | 78 | **82** | +4 |
| 2 | lines | 28617 | **30460** | +1843 |
| 3 | theorems | 1326 | **1440** | +114 |
| 4 | `sorry` | 1 | **1** | 0 |

Full `lake build` after the last change: **1243 jobs, exit 0, 0 lean diagnostics,
0 lake errors, 0 non-`sorry` warnings, 1 `sorry`** — the pre-existing
`Skeleton/Section6.lean:197` (`thm18`), untouched. Wall clock 6.53 s cold on the
new modules, peak PSS 1752 MiB across the process group.

Log: `ScottDomains/logs/compile-20260808-133609.agent1.log`.

## 7. Axiom audit

`scripts/axioms.sh` over every new headline declaration, with all four new modules
imported **together** in one environment (the composition check that `lake build`
cannot perform):

    Flat.instDomain                             [propext, Classical.choice, Quot.sound]
    Flat.instBoundedComplete                    [propext, Classical.choice, Quot.sound]
    Flat.compacts_eq_univ                       [propext, Classical.choice, Quot.sound]
    Flat.scottContinuous_of_monotone            [propext, Classical.choice, Quot.sound]
    Flat.truth_nondegenerate                    (no axioms)
    Flat.hoare_natBot_orderIso_powerset         [propext, Classical.choice, Quot.sound]
    Flat.smyth_natBot_orderIso                  [propext, Classical.choice, Quot.sound]
    Flat.plotkin_natBot_orderIso                [propext, Classical.choice, Quot.sound]
    Flat.plotkin_le_iff                         [propext, Classical.choice, Quot.sound]
    Flat.plotkin_printed_clause_one_fails       [propext, Classical.choice, Quot.sound]
    Flat.smyth_oneBot_eq_bot_eq_unit_bot        [propext, Classical.choice, Quot.sound]
    Flat.hoare_oneBot_eq_one                    [propext, Classical.choice, Quot.sound]
    Flat.hoare_oneBot_ne_bot                    [propext, Classical.choice, Quot.sound]
    Flat.plotkin_three_distinct                 [propext, Classical.choice, Quot.sound]
    Flat.convex_does_not_preserve_boundedComplete  [propext, Classical.choice, Quot.sound]
    Flat.setU'_minimal                          [propext, Classical.choice, Quot.sound]
    Flat.setV'_minimal                          [propext, Classical.choice, Quot.sound]
    Flat.not_setU'_le_setV'                     [propext, Classical.choice, Quot.sound]
    Flat.not_boundedComplete_plotkin_TT         [propext, Classical.choice, Quot.sound]
    Flat.omega_not_cpo                          [propext]
    Flat.omegaTop_monotone_not_continuous       [propext, Classical.choice, Quot.sound]
    Flat.isLUB_natRange                         [propext, Classical.choice, Quot.sound]

**No declaration depends on `sorryAx`.** `Classical.choice` enters through
`flatSup`'s `dite`, through `IdealCompletion.idealSup`'s `dite` on the undecidable
`Order.IsIdeal`, and through `Equiv.ofBijective` in the two isomorphisms built
from bijectivity.

## 8. Files

| # | File | Lines | Content |
| -- | ---- | ----: | ------- |
| 1 | `ScottDomains/Flat.lean` | 367 | the construction, its six instances, `K(X⊥) = X⊥`, `N⊥`, `T`, the non-degeneracy witness, and row 12 |
| 2 | `ScottDomains/FlatPowerdomain.lean` | 1040 | rows 3–9: the three isomorphisms, the corrected `⊢♮`, the three non-determinism identities |
| 3 | `ScottDomains/FlatSection6.lean` | 331 | rows 10–11: `(T × T)♮` |
| 4 | `ScottDomains/FlatOmega.lean` | 105 | rows 13–14: `ω` and `ω⊤` |

All four in namespace `ScottDomains.Flat`, per the round's namespace-per-agent
rule; `grep` finds no collision with any existing declaration, and the composition
check in §7 confirms it at the kernel.

`INDEX.md` updated with all four.

## 9. Commits on branch `agent1`

| # | Commit | Content |
| -- | ------ | ------- |
| 1 | `dc24902` | the flat cpo |
| 2 | `ac0ff12` | `(N⊥)♭ ≅ P N`, the corrected `⊢♮`, the three identities |
| 3 | `2788fb7` | `(T × T)♮` |
| 4 | `e5e288e` | `(N⊥)♯ ≅ {N} ∪ P*f(N)`, and monotone-implies-continuous |
| 5 | `d88fca1` | `(N⊥)♮` described |
| 6 | (this report) | `ω`, `ω⊤`, `INDEX.md`, and the report |

Not pushed, per the agents-commit-orchestrator-pushes rule.

## 10. Suggested orchestrator checks

1. `scripts/axioms.sh -i` over all four new modules **together with** the other
   streams' new modules — the four here compose, but that does not test them
   against agent2–agent5's namespaces.
2. **Read `Flat.plotkin_le_iff` against printed p. 26.** It deliberately does not
   state the paper's sentence; `plotkin_printed_clause_one_fails` is the reason,
   and it is the round's one claim that the paper is wrong about a definition
   rather than about a proof.
3. `PaperInventory.md` row 3's prose-claim table has no §5 entry (r0040's agent3
   finding); rows 3–9 above are all §5 and all now have declarations.
4. `docs/PropertiesVsTheorems.md` §1 places Theorem 14 in §4 and Lemma 13's
   negation nowhere; the negation now exists as
   `Flat.convex_does_not_preserve_boundedComplete` and belongs next to Lemma 13's
   row.
