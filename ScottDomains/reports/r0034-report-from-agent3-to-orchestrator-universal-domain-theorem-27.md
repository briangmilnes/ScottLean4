---
round: r0034
from: agent3
to: orchestrator
subject: universal-domain-theorem-27
date: 2026-0807-07:46
started: 2026-0806-22:40
finished: 2026-0807-07:46
related:
  - plans/r0034-plan-from-orchestrator-to-agent3-universal-domain-theorem-27.md
---

# r0034 agent3 — §7.3's universal domain `U`, and Theorem 27

Both parts landed. One new module, `ScottDomains/ScottDomains/Dyadic.lean`, 649
lines, 59 `theorem`/`lemma` declarations, **0 `sorry`**, and
`scripts/compile.sh -r r0034` reports **0 errors and 0 warnings** on the whole
library. Theorem 27 is proved from one named hypothesis — the paper's own
Boolean-algebra step — and that hypothesis is the only thing not formally
verified; see "What Theorem 27 rests on" below for why it cannot be discharged
against Mathlib v4.32.2.

## Interface note for agent4 and agent5 — `U` as built

Module: `ScottDomains/ScottDomains/Dyadic.lean`, namespace
`ScottDomains.Dyadic`. Import it as `import ScottDomains.Dyadic`. This section
was committed at 6bdb61b, before Part 2 was written, and has not changed since.

### The points

    def S : Set ℚ := {q | ∃ n m : ℕ, 0 < m ∧ n < 2 ^ m ∧ q = (n : ℚ) / 2 ^ m}

the paper's `S`, the dyadic rationals of `[0, 1)`. `mem_Ico_of_mem_S` proves
`q ∈ S → 0 ≤ q ∧ q < 1`.

    def E : Set ℚ := {q | ∃ n m : ℕ, 0 < m ∧ n ≤ 2 ^ m ∧ q = (n : ℚ) / 2 ^ m}

the admissible interval endpoints — the dyadic rationals of the *closed*
`[0, 1]`, i.e. `S` together with `1`. `max_mem_E`, `min_mem_E`, `zero_mem_E`,
`one_mem_E`.

    def Ivl (r t : ℚ) : Set ℚ := {s | s ∈ S ∧ r ≤ s ∧ s < t}   -- the paper's `[r, t)`

with `Ivl_zero_one : Ivl 0 1 = S` and
`Ivl_inter : Ivl r t ∩ Ivl r' t' = Ivl (max r r') (min t t')`.

### The basis `U₀` — carrier and pre-order

    def unionOf (F : Finset (ℚ × ℚ)) : Set ℚ := ⋃ p ∈ F, Ivl p.1 p.2

    def IsBasic (X : Set ℚ) : Prop :=
      X.Nonempty ∧ ∃ F : Finset (ℚ × ℚ), (∀ p ∈ F, p.1 ∈ E ∧ p.2 ∈ E) ∧ X = unionOf F

    def U₀ : Type := {X : Set ℚ // IsBasic X}

`U₀` is the paper's basis: the finite **non-empty** unions of dyadic half-open
intervals of `[0, 1)`. Access the underlying set with `U₀.toSet X : Set ℚ`
(`U₀.mk`, `U₀.ext`, `U₀.toSet_mk` round it out); it is a plain `def`, not an
`abbrev`, so that Mathlib's `Subtype.partialOrder` — which orders by `⊆`, the
*wrong* direction — is not found.

**The pre-order is superset**, in Mathlib's orientation:

    theorem U₀.le_iff {X Y : U₀} : X ≤ Y ↔ toSet Y ⊆ toSet X

More information is a *narrower* set of dyadic points. Instances on `U₀`:
`PartialOrder` (the display above), `OrderBot` with `⊥ = [0, 1) = S`
(`U₀.toSet_bot : toSet ⊥ = S`), `Countable` (`U₀.countable_isBasic` is the
underlying `Set.Countable`), and `Nontrivial`.

### `U` and `K(U)`

    abbrev U : Type := IdealCompletion U₀

An `abbrev`, so Theorem 11's instances on `IdealCompletion U₀` —
`CompletePartialOrder`, `IsAlgebraic`, `Domain` — are found by instance search at
`U`. Five further facts:

| # | Statement | Name |
| - | --------- | ---- |
| 1 | `U` is a domain | `Domain U` by `inferInstance`; `thm11_at_U` states it with the `K(U)` conjunct |
| 2 | `K(U) = {↓X ∣ X ∈ U₀}` | `compacts_U : compacts U = Set.range (IdealCompletion.principal : U₀ → U)` |
| 3 | compact ⇔ principal | `isCompactElement_iff : IsCompactElement I ↔ ∃ X : U₀, I = IdealCompletion.principal X` |
| 4 | membership in a compact | `mem_principal_iff : Y ∈ (principal X : U) ↔ toSet X ⊆ toSet Y` |
| 5 | `U` is bounded complete | `instance : BoundedComplete U` |

Read row 4 as: the compact element `↓X` of `U` is the set of basis elements
**containing** `X` — a superset is a coarser approximation. Row 5 is not in the
plan but is the property §7.3 exists for: the least upper bound of a bounded pair
`X, Y` of `U₀` is the *intersection* `toSet X ∩ toSet Y`
(`U₀.exists_isLUB_pair`), and `IdealCompletion.boundedComplete` lifts that to
`U`. §7.4 opens by observing that the convex powerdomain cannot be represented
over `U` precisely because a projection of `U` inherits bounded completeness.

Nothing about ideals, cpos, algebraicity or compactness is re-proved in this
module. Part 1 is exactly three instances on `U₀` — the superset order, the
least element `[0, 1)`, and countability — after which Theorem 11
(`IdealCompletion.instDomain`, `IdealCompletion.thm11`) supplies the rest.

### The order was checked, not assumed

Agent5's finding that §7.4's printed relation is not reflexive prompted a check
of this one. `U₀`'s order is kernel-checked to be a partial order: the
`PartialOrder U₀` instance discharges `le_refl`, `le_trans` and `le_antisymm`
against `X ≤ Y ↔ toSet Y ⊆ toSet X`, and `OrderBot U₀` discharges
`⊥ ≤ X` — the paper's "`[0, 1)` is the least element" — from
`U₀.toSet_subset_S`. §7.3's printed order survives the check; §7.4's did not.

The definitions are also checked to be non-vacuous. `isBasic_lowerHalf` proves
`[0, 1/2)` is a basis element and `bot_lt_lowerHalf` that `⊥ < [0, 1/2)`
strictly, so `U₀` is not a one-point poset and `U` is not the one-point cpo —
which is what a mis-stated `E` or `Ivl` would have collapsed it to while leaving
every instance above provable.

## Part 2 — Theorem 27

> **Theorem 27** For any bounded complete domain `D`, there is a projection
> `p : U → D`.

**Proved, modulo one named hypothesis.** The paper's proof paragraph ends at

> … if `j : B' → B` maps `B'` isomorphically onto a subalgebra of `B`, then the
> composition `j ∘ i` cuts down to an isomorphism between `A` and a normal
> subposet `A' ◁ U₀`.

Everything before that sentence is Boolean algebra; everything after it is order
theory. The formalization splits exactly there:

    def IsNormallyRepresented (A : Type*) [PartialOrder A] : Prop :=
      ∃ N : Set U₀, IsNormalIn N (Set.univ : Set U₀) ∧ Nonempty (A ≃o ↥N)

    theorem thm27_of_isNormallyRepresented (D : Type u) [CompletePartialOrder D] [Domain D]
        (h : IsNormallyRepresented ↥(compacts D)) :
        ∃ (e : ScottHom D U) (p : ScottHom U D), ScottHom.IsEmbeddingProjectionPair e p

`thm27` is the same with `[BoundedComplete D]` present, as the paper states it.

### What is proved

`thm27_of_isNormallyRepresented` constructs both halves of the
embedding–projection pair and proves the two equations, all kernel-checked:

| # | Object | Definition | Name |
| - | ------ | ---------- | ---- |
| 1 | `ψ : K(D) → U₀` | `(φ k : U₀)` | `emb`, with `emb_le_emb` (order-reflecting), `emb_bot` |
| 2 | `e : D → U` | `e x = {Y ∣ ∃ k ∈ K(D), k ⊑ x ∧ Y ⊑ ψ k}` | `embIdeal`, `embHom` |
| 3 | `p : U → D` | `p I = ⨆ {k ∈ K(D) ∣ ψ k ∈ I}` | `projElem`, `projHom` |
| 4 | `p ∘ e = id` | via `projSet (e x) = compactsBelow x` | `projElem_embIdeal` |
| 5 | `e ∘ p ⊑ id` | | `embIdeal_projElem_le` |

Three places where a hypothesis is actually spent, worth recording because they
say what each part of the data is for:

1. **Compactness of the members of `K(D)`** makes `e` Scott-continuous: a compact
   `k ⊑ ⨆S` already sits below some member of `S` (`scottContinuous_embIdeal`).
2. **Normality of `N`** — and nothing else — makes `{k ∣ ψ k ∈ I}` directed, so
   that `p I` is a least upper bound of a directed set rather than of an
   arbitrary one (`directedOn_projSet`). This is the only use of normality.
3. **Algebraicity of `D`** gives `p (e x) = x`: the set of compacts named by
   `e x` is exactly `compactsBelow x`, whose least upper bound is `x`.

`BoundedComplete D` is *not* used. It is spent inside the hypothesis, where the
paper needs the subsets `↑x` to generate a Boolean algebra in which a bounded
family has non-empty intersection. That is a real finding about the proof's
structure: past the Boolean algebra, Theorem 27 holds for every domain that is
normally represented in `U₀`, bounded complete or not.

The construction deliberately avoids the route through `NormalProjection.normalHom`
and `im(p_N)`. That route pays twice — the cpo on `im(p_N)` is
`IsProjection.rangeCompletePartialOrder`, which is not an instance because it
depends on the projection *proof*, and identifying `im(p_N)` with `D` needs the
ideal completion to be functorial on order isomorphisms. Building `e` and `p`
directly between `D` and `U` needs neither.

### What Theorem 27 rests on

`IsNormallyRepresented ↥(compacts D)` is **not** proved. Discharging it needs
the paper's sentence

> up to isomorphism — the only countable atomless Boolean algebra is the free one
> on countably many generators. But this Boolean algebra has the property that
> every countable Boolean algebra is isomorphic to a subalgebra.

which is Vaught's theorem, proved by back-and-forth. Mathlib v4.32.2 does not
have it, and does not have the vocabulary to state it: `IsAtomless` has **zero**
occurrences in `Mathlib/`, and "atomless" has zero occurrences in
`Mathlib/ModelTheory/`. Nothing weaker substitutes, because the paper's `j` is
exactly the embedding that theorem supplies. Formalizing it is a self-contained
project of its own — the countable atomless Boolean algebra, its uniqueness, and
the universality that follows — and it is the entire remaining gap in Theorem 27.

Two further steps would then remain, both order theory rather than model theory,
and both smaller: that `B = U₀ ∪ {∅}` is a Boolean algebra (closure of finite
unions of dyadic intervals under complement — `isBasic_inter` is the
intersection half, already proved), and that `B'`'s embedding *cuts down* to a
**normal** subposet, which the paper asserts without proof.

## Measured counts

| # | Metric | Value |
| - | ------ | ----- |
| 1 | New module | `ScottDomains/ScottDomains/Dyadic.lean` |
| 2 | Lines in the new module | 649 |
| 3 | `theorem`/`lemma` declarations in the new module | 59 |
| 4 | `sorry` in the new module | 0 |
| 5 | Development totals after this round | 46 modules, 14697 lines, 718 theorems |
| 6 | Pre-existing `sorry` elsewhere | 8, in `Skeleton/Recovered.lean` (7) and `Skeleton/Section6.lean` (1) — untouched |
| 7 | `scripts/compile.sh -r r0034 ScottDomains.Dyadic` | exit 0, 0 errors, 0 warnings, 0 `sorry`, wall 3.46 s |
| 8 | `scripts/compile.sh -r r0034` (whole library) | exit 0, 0 errors, 0 warnings beyond the 8 pre-existing `sorry`, wall 7.81 s, 1122 jobs |
| 9 | Axiom audit (`scripts/axioms.sh`) | `thm27`, `thm27_of_isNormallyRepresented`, `thm11_at_U`, `compacts_U`, `U₀.exists_isLUB_pair`, `isBasic_inter`, `U₀.countable_isBasic` each depend on `[propext, Classical.choice, Quot.sound]` only — no `sorryAx` |

## Commits on branch `agent3`

| # | SHA | Content |
| - | --- | ------- |
| 1 | 779c1b3 | work in progress, first draft of `Dyadic.lean` |
| 2 | b470e00 | Part 1 compiles: `U` with its `Domain` and `BoundedComplete` instances and `K(U)` |
| 3 | 6bdb61b | the interface note above, committed for agent4 and agent5 before Part 2 |
| 4 | 1c2fd14 | Theorem 27: `IsNormallyRepresented` and `thm27_of_isNormallyRepresented` |
| 5 | 4cc2912 | nondegeneracy: `[0, 1/2)` is a basis element strictly above `[0, 1)` |

Not pushed, per the agent/orchestrator split.

## One correction to the plan

The plan lists Prop 15 (`ScottDomains.prop15`) and Theorem 22
(`ScottDomains.thm22`) as "on the paper's route" to Theorem 27. Neither is used,
and neither is on it. §7.3's proof paragraph cites no earlier result of the
paper: it goes through the Boolean algebra `B` and lands on a normal subposet,
which is §4's machinery, not §6's bifiniteness or §7.2's closures on `P N`.
Theorem 22 concerns *closures* onto an algebraic lattice over `P(ℕ)`; Theorem 27
concerns *projections* onto a bounded complete domain over `U`, and §7.3 opens by
saying `U` exists because `P N` cannot represent `+`.
