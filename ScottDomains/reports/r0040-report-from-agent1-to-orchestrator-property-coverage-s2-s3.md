---
round: r0040
from: agent1
to: orchestrator
subject: property-coverage-s2-s3
date: 2026-0808-11:58
started: 2026-0808-11:34
finished: 2026-0808-11:58
related:
  - plans/r0040-plan-from-orchestrator-to-orchestrator-property-coverage.md
  - docs/PropertiesVsTheorems.md
  - docs/PaperInventory.md
---

# r0040, §2 and §3 — does every property the paper asserts have a Lean statement?

Sections audited: **§2** (Recursive definitions of functions, printed pp. 3–8) and
**§3** (Effectively presented domains, printed pp. 8–12) of Gunter & Scott,
*Semantic Domains*, `ScottDomains/papers/Gunter Scott 1990.pdf`. Physical PDF page
= printed page + 1; every operator glyph below was read off a 150–200 dpi render
of the physical page, not off `pdftotext`.

Direction: **paper → development.** The properties were enumerated from the PDF
first; the Lean development was searched only afterwards.

## 1. Headline

| # | Measurement | Value |
| -- | ----------- | ----- |
| 1 | properties the paper asserts in §2 and §3 | **60** |
| 2 | of which conjuncts of numbered results (Thm 1–3, Lem 4–5, Thm 6–7) | **15** |
| 3 | of which unnumbered prose claims | **45** |
| 4 | `S+P` stated and proved | **33** |
| 5 | `S+H` stated, proof open | **0** |
| 6 | `S≠` stated, but not the paper's statement | **3** |
| 7 | `P` prose only (docstring, never under the kernel) | **0** |
| 8 | `N` not stated in any form | **24** |

Two of the 24 `N` rows are conjuncts of Theorem 7; the other 22 are prose claims.

**The one confirmed `N` was one of two, and both are Theorem 7's.** r0038 recorded
Theorem 7's second sentence — "if `D` and `E` have effective presentations then
`D → E` has one" — as unstated. The paper's third sentence, "Similar facts hold
for `D ⊸ E`", carries the same claim for the strict function space, and it is
unstated for the same reason. Section 4 gives the greps.

**The gap is much wider than 2.** `PropertiesVsTheorems.md` §1 counts 11 prose
claims in §2/§3 (12 curated, minus the one r0038 struck). The paper makes **45**.
The 34 the curated list omits are 9 `S+P`, 3 `S≠`, and **22 `N`** — the whole of
§2.1's example calculus, both §2.2 applications, both §2.3 prose claims, and four
of §3.2's five.

## 2. Re-derived conjunct counts against `PropertiesVsTheorems.md` §1

| # | Result | `PropertiesVsTheorems.md` §1 | re-derived | moved? |
| -- | ------ | ---: | ---: | ------ |
| 1 | Thm 1 | 1 | **2** | **+1** — the printed conclusion is a conjunction: "`fix(f) = f(fix(f))` **and** `fix(f) ⊑ x` for any `x` with `x = f(x)`". By the doc's own rule ("one atomic assertion") that is two. Both are `S+P`, so the label total is unaffected |
| 2 | Thm 2 | 1 | 1 | — |
| 3 | Thm 3 | 1 | 1 | — (see the note below) |
| 4 | Lem 4 | 4 | 4 | — |
| 5 | Lem 5 | 2 | 2 | — |
| 6 | Thm 6 | 1 | 1 | — |
| 7 | Thm 7 | 4 | **4** | count unchanged, **decomposition wrong** — see below |
| — | §2/§3 numbered total | 14 | **15** | **+1** |
| 8 | §2/§3 prose claims | 11 | **45** | **+34** |
| — | §2/§3 total | 25 | **60** | **+35** |

**Theorem 7's four conjuncts are not the four the doc names.** Row 5 of
`PropertiesVsTheorems.md` §1 reads "cpo, bounded complete, algebraic, countably
based" — that is the *first* sentence's conclusion unfolded into the four
components of "bounded complete domain". It is a decomposition of one conjunct,
and it silently drops the theorem's other two sentences. The printed theorem
(physical p. 13, printed p. 12) is:

> **Theorem 7** If `D` and `E` are bounded complete domains, then `D → E` is also
> a bounded complete domain. Moreover, if `D` and `E` have effective
> presentations, then `D → E` has an effective presentation as well. Similar
> facts hold for `D ⊸ E`.

Three sentences, and the third distributes over the first two, so the conjuncts
are:

| # | Theorem 7 conjunct | label |
| -- | ------------------ | ----- |
| 7a | `D`, `E` bounded complete domains ⟹ `D → E` is a bounded complete domain | `S+P` |
| 7b | `D`, `E` effectively presented ⟹ `D → E` has an effective presentation | **`N`** |
| 7c | `D`, `E` bounded complete domains ⟹ `D ⊸ E` is a bounded complete domain | `S+P` |
| 7d | `D`, `E` effectively presented ⟹ `D ⊸ E` has an effective presentation | **`N`** |

This is why `PaperInventory.md` row 2e records the effective-presentation gap as a
single isolated oddity: the conjunct decomposition in use had no slot for it.

**A note on Theorem 3.** The printed theorem is "`fix` is the unique uniform
fixed point operator", which presupposes that `fix` *is* uniform — a claim the
paper makes one paragraph earlier ("We leave it to the reader to show that `fix`
is a uniform fixed point operator"). I count Theorem 3 as **1** conjunct
(uniqueness, which is what the theorem adds) and carry "`fix` is uniform" as a
§2.3 prose claim, where it is row 33 below and is **`N`**. `UniformFixedPoint.lean`
is explicit about this at line 168: "`fix` is itself uniform is left to the reader
by the paper; what Theorem 3 establishes is that **no other** uniform operator
exists."

## 3. Property table

`§`/`p.` is the printed page. Declaration names are given with the file and line
where they are declared; every `S+P` row below was opened and read, not taken
from a docstring.

### 3.1 Conjuncts of the numbered results — 15 rows

| # | Paper's sentence | § / p. | Label | Declaration | Evidence |
| -- | ---------------- | ------ | ----- | ----------- | -------- |
| 1 | Thm 1: `fix(f) ∈ D` with `fix(f) = f(fix(f))` | 2.1 / 5 | `S+P` | `ScottDomains.theorem1`.1, `map_kleeneFix` | `FixedPoint.lean:108, 73`; `IsLeast {a \| f a = a} (kleeneFix f)`, first component |
| 2 | Thm 1: …and `fix(f) ⊑ x` for every `x` with `x = f(x)` | 2.1 / 5 | `S+P` | `ScottDomains.theorem1`.2, `kleeneFix_le` | `FixedPoint.lean:108, 101`; second component of the same `IsLeast` |
| 3 | Thm 2 (Schröder–Bernstein): injections `f : S → T`, `g : T → S` give a bijection `h : S → T` | 2.2 / 6 | `S+P` | `Function.Embedding.schroeder_bernstein` (Mathlib) | `Mathlib/SetTheory/Cardinal/SchroederBernstein.lean:90`, inside `namespace Function` (37) / `namespace Embedding` (39). **`PaperInventory.md:483` names it `Function.schroeder_bernstein`; that name does not exist.** The row corrected an earlier draft's `Function.Embedding.schroederBernstein` — which had the right namespace and the wrong casing — into a name with the right casing and the wrong namespace. The declaration is `Function.Embedding.schroeder_bernstein` |
| 4 | Thm 3: `fix` is the *unique* uniform fixed point operator | 2.3 / 7 | `S+P` | `ScottDomains.theorem3` | `UniformFixedPoint.lean:130`; `(F : FixedPointOperator) (hF : F.IsUniform) → F.op D f = kleeneFix ⇑f`. Uniqueness only; existence is row 33 |
| 5 | Lem 4.1: `A ◁ B ◁ C` ⟹ `A ◁ C` | 3.1 / 9 | `S+P` | `ScottDomains.IsNormalIn.trans` | `NormalSubposet.lean:67` |
| 6 | Lem 4.2: `A ⊆ B ⊆ C` and `A ◁ C` ⟹ `A ◁ B` | 3.1 / 9 | `S+P` | `ScottDomains.IsNormalIn.mono_right` | `NormalSubposet.lean:81` |
| 7 | Lem 4.3: `A ◁ C` ⟹ `⊥ ∈ A` | 3.1 / 9 | `S+P` | `ScottDomains.IsNormalIn.bot_mem` | `NormalSubposet.lean:104`; the module docstring records that this is what forces nonemptiness into `IsNormalIn` |
| 8 | Lem 4.4: `⟨P(C), ◁⟩` is a cpo with `{⊥}` least | 3.1 / 9 | `S+P` | `IsNormalIn.refl`, `.antisymm`, `.trans`, `isNormalIn_sUnion`, `isNormalIn_sUnion_of_mem`, `isNormalIn_sUnion_le`, `singleton_bot_isNormalIn_of_isNormalIn` | `NormalSubposet.lean:60, 91, 67, 130, 143, 152, 116`. Unbundled — no `CompletePartialOrder` instance on a subtype of `Set α`; the seven facts are the cpo axioms plus the least element, and the module docstring (lines 27–33) says so |
| 9 | Lem 5, sentence 1: the compacts of `im(p)` are `im(p) ∩ K(D)` | 3.1 / 10 | `S+P` | `ScottDomains.ScottHom.IsProjection.isCompactElement_iff` | `FinitaryProjection.lean:58`; proved from `IsProjection` alone, weaker than the paper's finitary hypothesis |
| 10 | Lem 5, sentence 2: `im(p) ∩ K(D) ◁ K(D)` | 3.1 / 10 | `S+P` | `ScottDomains.ScottHom.IsFinitaryProjection.isNormalIn_compacts` | `FinitaryProjection.lean:101` |
| 11 | Thm 6: for a domain `D`, the cpo of normal substructures of `K(D)` and the poset `Fp(D)` are isomorphic | 3.1 / 11 | `S+P` | `ScottDomains.theorem6` | `Theorem6.lean:175`; a four-fold conjunction — each map lands in the other's domain, both round trips, both monotone. Unbundled rather than an `OrderIso`, as its docstring states |
| 12 | Thm 7a: `D`, `E` bounded complete domains ⟹ `D → E` bounded complete domain | 3.2 / 12 | `S+P` | `ScottDomains.ScottHom.isBoundedCompleteDomain_scottHom` | `FunctionSpaceCountable.lean:134`; `Domain (ScottHom α β) ∧ BoundedComplete (ScottHom α β)` under `[Domain α] [Domain β] [BoundedComplete β]` — strictly stronger than the paper, `BoundedComplete α` unused |
| 13 | Thm 7b: `D`, `E` effectively presented ⟹ `D → E` has an effective presentation | 3.2 / 12 | **`N`** | — | §4, row N1 |
| 14 | Thm 7c: the same for `D ⊸ E` — bounded complete domain | 3.2 / 12 | `S+P` | `ScottDomains.PRepFun.strictHomDomain` + `ScottDomains.lem10_strict` | `PRepFun.lean:450` (`Domain (StrictHom α β)`) and `Skeleton/Lemma10.lean:218` (`BoundedComplete (StrictHom α β)`). Unbundled across two modules; together they are the paper's conclusion |
| 15 | Thm 7d: the same for `D ⊸ E` — effective presentation | 3.2 / 12 | **`N`** | — | §4, row N2 |

Numbered subtotal: **13 `S+P`, 2 `N`**.

### 3.2 Unnumbered prose claims — 45 rows

Rows 16–26 are the eleven §2/§3 members of the curated list in
`PaperInventory.md` (its rows 1–7 and 9–12; row 8 was struck by r0038 and I
confirm the strike — see §5). Rows 27–60 are claims the paper makes that the
curated list omits.

| # | Paper's sentence | § / p. | Label | Declaration | Evidence |
| -- | ---------------- | ------ | ----- | ----------- | -------- |
| 16 | "the compact elements [of `P N`] are just the finite subsets of `N`" | 3 / 9 | `S+P` | `ScottDomains.isCompactElement_iff_finite` | `Powerset.lean:37` |
| 17 | "`P N` … is a domain" | 3 / 9 | `S+P` | `instance [Countable X] : Domain (Set X)` | `Powerset.lean:87`; `example : Domain (Set ℕ) := inferInstance` at line 93 |
| 18 | "the poset of continuous functions `D → E` is itself a cpo" | 2.1 / 4, restated in Thm 7's proof / 12 | `S+P` | `instance : CompletePartialOrder (ScottHom α β)` | `ScottHom.lean:239` |
| 19 | "`D → E` is a bounded complete cpo whenever `E` is" | Thm 7 proof / 12 | `S+P` | `instance [BoundedComplete β] : BoundedComplete (ScottHom α β)` | `ScottHom.lean:286` |
| 20 | "`step(s) : D → E` … is continuous" | Thm 7 proof / 12 | `S+P` | `ScottDomains.ScottHom.scottContinuous_stepFun` | `StepFunction.lean:73` |
| 21 | "…and compact in the ordering on `D → E`" | Thm 7 proof / 12 | `S+P` | `ScottDomains.ScottHom.isCompactElement_step` | `StepFunction.lean:140` |
| 22 | "it is possible to show that they form a basis for `D → E`" | Thm 7 proof / 12 | `S+P` | `instance : IsAlgebraic (ScottHom α β)` + `exists_finite_isLUB_of_isCompactElement` | `FunctionSpaceDomain.lean:121`, `CompactFunction.lean:142`. The development's `step k e` is one step function; the paper's `step(s)` over a finite `N ◁ K(D)` is the finite join, which is what `CompactFunction` supplies |
| 23 | "an embedding is an injection" | 3.1 / 10 | `S+P` | `ScottDomains.ScottHom.IsEmbeddingProjectionPair.injective_embedding` | `Projection.lean:69` |
| 24 | "a projection is a surjection" | 3.1 / 10 | `S+P` | `ScottDomains.ScottHom.IsEmbeddingProjectionPair.surjective_projection` | `Projection.lean:74` |
| 25 | "it is easy to check that the function `p_N` … is a finitary projection" | 3.1 / 10–11 | `S+P` | `ScottDomains.isFinitaryProjection_normalHom` | `Theorem6.lean:123` |
| 26 | "the poset of strict continuous functions `D ⊸ E` is also a cpo" | 2.1 / 4 | `S+P` | `ScottDomains.strictHomCpo` | `StrictHom.lean:79` |
| 27 | "any finite poset that has a least element is a cpo" | 2.1 / 3 | `S+P` | `ScottDomains.FpEmbedding.isLUB_of_finite_directed` | `FinitaryProjectionEmbedding.lean:141`; a finite nonempty directed set has a greatest element, hence a lub. The least-element half is the hypothesis, not a claim |
| 28 | "`P S` … forms a cpo whose least upper bound operation is just set [union]" | 2.1 / 3 | `S+P` | Mathlib `Set.instCompleteLattice`, `Set.sSup_eq_sUnion` | The development consumes it at `Powerset.lean:51, 83`; every `Set X` result there presupposes the instance |
| 29 | "the ordinal `ω` … is not a cpo" | 2.1 / 3 | **`N`** | — | §4, row N3 |
| 30 | "`Q` [the rationals] … fail[s] to be a cpo" | 2.1 / 3 | **`N`** | — | §4, row N4 |
| 31 | "the unit interval `[0,1]` of real numbers does form a cpo" | 2.1 / 3 | **`N`** | — | §4, row N5 |
| 32 | "when `f : D → E` is monotone and `D` is finite, then `f` is continuous" | 2.1 / 4 | `S+P` | `ScottDomains.FpEmbedding.scottContinuous_of_monotone_of_finite` | `FinitaryProjectionEmbedding.lean:165`; `[PartialOrder α] [Finite α]`, weaker than the paper's cpo hypothesis |
| 33 | "In fact, this is true whenever `D` has no infinite ascending chains" | 2.1 / 4 | **`N`** | — | §4, row N6 |
| 34 | "any monotone function `f : N⊥ → E` is continuous" | 2.1 / 4 | **`N`** | — | §4, row N7 |
| 35 | "the function `f : ω⊤ → O` … is monotone, but it is not continuous" | 2.1 / 4 | **`N`** | — | §4, row N8 |
| 36 | "The function `f*` is monotone" | 2.1 / 4 | **`N`** | — | §4, row N9 |
| 37 | "`f*(⋃ᵢ Xᵢ) = ⋃ᵢ f*(Xᵢ)`. In particular, `f*` is continuous" | 2.1 / 4–5 | **`N`** | — | §4, row N9 |
| 38 | "a function `f : [0,1] → [0,1]` … may be continuous in the cpo sense without being continuous in the usual sense" | 2.1 / 5 | **`N`** | — | §4, row N10 |
| 39 | factorial: "`F` is continuous (but not strict)", and "by the Fixed Point Theorem, `F` has a least fixed point `fix(F)` and this solution will satisfy the equation for `fact`" | 2.2 / 5 | **`N`** | — | §4, row N11 |
| 40 | grammars: the three operators "are all continuous in the variable `X`", the three equations "all have least solutions", and "These solutions are the languages defined by the grammars" | 2.2 / 6 | **`N`** | — | §4, row N12 |
| 41 | "the function `fix_D : (D → D) → D` given by `fix_D(f) = ⨆ₙ fⁿ(⊥)` is actually continuous" | 2.3 / 7 | **`N`** | — | §4, row N13 |
| 42 | "We leave it to the reader to show that `fix` is a uniform fixed point operator" | 2.3 / 7 | **`N`** | — | §4, row N14 |
| 43 | "With the exception of the unit interval of real numbers, all of the cpo's we have mentioned so far are domains" | 3 / 9 | **`N`** | — | §4, row N15 |
| 44 | "The compact elements of the domain `N⊥ → N⊥` are the functions with finite domain of definition" | 3 / 9 | **`N`** | — | §4, row N7 |
| 45 | "one may recover from `G_f` the value of `f` on `x` as `f(x) = ⨆{y' \| (x',y') ∈ G_f and x' ⊑ x}`" | 3 / 9 | **`S≠`** | `ScottDomains.ContinuousConstruction.coe_eq_basisExtension_self` | `ContinuousConstruction.lean:307`. The recovery formula *shape* is `familyFun s x = ⨆{b \| (k,b) ∈ s, k ⊑ x}` (line 141), and the theorem says every continuous `f` is `familyFun (graphOn ⇑f)`. **The family is not the paper's `G_f`**: `graphOn v = {(k, v k) \| k ∈ K(D)}` (line 245) restricts only the *first* coordinate to compacts and pins the second to the exact value, where `G_f = {(x',y') ∈ K(D) × K(E) \| y' ⊑ f(x')}` restricts both and is downward closed in the second. The two agree in value when `E` is algebraic, but the paper's countability corollary (row 46) follows only from its own version |
| 46 | "This allows us to characterize … a continuous function `f : P N → P N` between uncountable cpo's with a countable set `G_f`" | 3 / 9 | **`N`** | — | §4, row N16 |
| 47 | "One can show that each of `f` and `g` uniquely determines the other" | 3.1 / 10 | **`N`** | — | §4, row N17 |
| 48 | Example: "there is a strict continuous function `strict : (D → E) → (D ⊸ E)` given by `strict(f)(x) = f(x)` if `x ≠ ⊥`, `⊥` if `x = ⊥`" | 3.1 / 10 | `S+P` | `ScottDomains.ClosureProperties.scottContinuous_strictFun`, `strictFun_bot`, `strictHom` | `ClosureProperties/StrictFunction.lean:92, 65, 124`; `strictFun` (line 63) is the paper's `strict(f)` verbatim |
| 49 | Example: "The function `strict` is a projection whose corresponding embedding is the inclusion map `incl : (D ⊸ E) ↪ (D → E)`" | 3.1 / 10 | `S+P` | `ScottDomains.ClosureProperties.strictHom_val_of_isStrict`, `strictHom_val_le` | `ClosureProperties/StrictFunction.lean:144, 130`. Unbundled: `IsEmbeddingProjectionPair g f := (∀x, f (g x) = x) ∧ (∀y, g (f y) ≤ y)` (`Projection.lean:44`), and these two are exactly `strict ∘ incl = id` and `incl ∘ strict ⊑ id`. The predicate itself is never applied to this pair — there is no bundled `incl : ScottHom (D ⊸ E) (D → E)` |
| 50 | "the inclusion map from `im(p)` into `D` is an embedding (which has the corestriction of `p` to its image as the corresponding projection)" | 3.1 / 10 | `S+P` | `ScottHom.IsProjection.apply_of_mem_range`, `IsProjection.le`, `PRepFun.scottContinuous_val`, `PRepFun.scottContinuous_corestrict` | `Projection.lean:56, 53`; `PRepFun.lean:157, 169`. Unbundled in the same sense as row 49: both defining equations and both continuity facts are stated; `IsEmbeddingProjectionPair` is never applied to this pair |
| 51 | "the correspondence `N ↦ p_N` is inverse to the correspondence `p ↦ im(p) ∩ K(D)`" | 3.1 / 11 | `S+P` | `ScottDomains.theorem6` (conjuncts 1 and 2) | `Theorem6.lean:175–181`, via `range_normalHom_inter_compacts` and `normalFun_range_inter_compacts` |
| 52 | "if `M ⊆ Fp(D)` is directed then `im(⨆M)` is a domain" | 3.1 / 11 | `S+P` | `ScottDomains.PRep.isFinitaryProjection_sSup` | `PRep.lean:463`; `IsFinitaryProjection (sSup d)` for a nonempty directed `d` of finitary projections, and `IsFinitaryProjection p` is by definition `im(p)` a domain (`Projection.lean:170`) |
| 53 | "there are domains `D, E` such that the cpo `D → E` is *not* a domain" | 3.2 / 11 | **`S≠`** | `ScottDomains.JungSFP.lemma213` | `JungSFP.lean:475–481`: `¬ IsAlgebraic (ScottHom D E)` **under seven hypotheses** — two compacts of `D` with infinitely many minimal upper bounds, and two distinct minimal upper bounds in `E` of a compact pair with a common bound. Nothing in the development exhibits domains satisfying them, so the paper's *existential* is not obtained. It is a sufficient condition for the failure, not a witness of it |
| 54 | "A domain `D` is bounded complete if and only if the cpo `D⊤` which results from adding a new top element to `D` is an algebraic lattice" | 3.2 / 11 | **`N`** | — | §4, row N18 |
| 55 | "The poset `P N` is an example of an algebraic lattice" | 3.2 / 11 | `S+P` | `instance [Countable X] : Domain (Set X)` + Mathlib `Set.instCompleteLattice` | `Powerset.lean:87`; `Powerset.lean:79–83`'s docstring states the completeness explicitly ("it is a complete lattice, so *every* subset has a least upper bound"). The paper's "(countably based) algebraic lattice" is exactly a domain in which every subset has a lub |
| 56 | "the bounded complete domain `N⊥ ⊸ N⊥` lacks a top element and therefore fails to be an algebraic lattice" | 3.2 / 11 | **`N`** | — | §4, row N7 |
| 57 | "All of the domains we have discussed so far are bounded complete" | 3.2 / 11 | **`N`** | — | §4, row N15 |
| 58 | Thm 7 proof: "The proof that the poset of step functions has decidable ordering and finite normal subposets is tedious, but not difficult, using the effective presentations of `D` and `E`" | Thm 7 proof / 12 | **`N`** | — | §4, row N1 |
| 59 | Thm 7 proof: "The proof of these facts for `D ⊸ E` is essentially the same since the strict step functions form a basis" | Thm 7 proof / 12 | **`S≠`** | `ScottDomains.PRepFun.strictHomIsAlgebraic` | `PRepFun.lean:426`: `IsAlgebraic (StrictHom α β)`, so `D ⊸ E` has a basis. The basis is **not** identified as the strict step functions — the proof transports algebraicity from `D → E` through `ClosureProperties.isCompactElement_val_of_isCompactElement` (`StrictFunction.lean:192`), and the compacts of `D → E` it lands on are finite joins of step functions that need not be strict. `grep -Ei 'strictStep\|stepStrict\|strict step'` over the package: 0 |
| 60 | "we will discuss a great many operators like `· → ·` and `· ⊸ ·`. We will leave it to the reader to convince himself that all of these operators preserve the property of having an effective presentation" | 3.2 / 12 | **`N`** | — | §4, row N19 |

Prose subtotal: **20 `S+P`, 3 `S≠`, 22 `N`**.

## 4. The `N` rows, with their greps

`N` is this round's product, so each concept was searched under at least three
names. All counts are `grep -rEi --include='*.lean'` over
`ScottDomains/ScottDomains/`, docstrings included — a docstring hit is what would
have made a row `P` instead of `N`. The probe script is
`scripts/a1-absence-greps.sh`; it is read-only and writes nothing.

| # | Property | Grep 1 | Grep 2 | Grep 3 | Verdict |
| -- | -------- | ------ | ------ | ------ | ------- |
| N1 | **Thm 7b** — `D`, `E` effectively presented ⟹ `D → E` effectively presented (rows 13, 58) | `EffectivePresentation` → 21, **all inside `EffectivePresentation.lean` and `ComputableFunction.lean`** | `EffectivePresentation \((ScottHom\|StrictHom)` → **0** | `decidableNormal\|decidableLE` → 6, all the structure's own field declarations and their docstrings | **`N`, confirmed independently.** Stronger than r0038 recorded: **the structure `EffectivePresentation` is never instantiated at any type at all** — no domain in the development is given an effective presentation, not the function space and not `P N`. §3.2 is definitional only. `ComputableFunction.lean` is imported by nothing (`grep 'import ScottDomains.ComputableFunction'` → 0) and is absent from `ScottDomains.lean`; `EffectivePresentation.lean` is imported only by it |
| N2 | **Thm 7d** — the same for `D ⊸ E` (row 15) | as N1 | as N1 | `preserve.{0,20}presentation\|presentation.{0,20}preserve` → **0** | **`N`.** The same hole, one arrow over. r0038 found one instance of this gap; the paper's third sentence makes it two |
| N3 | `ω` is not a cpo (row 29) | `omegaTop\|omega_top\|OmegaTop` → **0** | `Ordinal` → 7, all in `JungNets.lean`/`JungSFP.lean` on Jung's ordinal-indexed nets | `not a cpo\|fails to be a cpo` → **0** | `N` |
| N4 | `Q` is not a cpo (row 30) | `sqrt\|square root` → **0** | `LinearOrderedField\|Rat.instCompletePartialOrder` → **0** | `CompletePartialOrder .{0,3}(Rat\|ℚ)` → **0** | `N`. `ℚ` occurs 76 times, all in `Dyadic.lean`/`Atomless.lean` building §7.3's `U` |
| N5 | `[0,1]` is a cpo (row 31) | `unitInterval\|Set\.Icc` → **0** | `ℝ\|Real\.\|import Mathlib.Data.Real` → **0** — the reals do not occur in the package | `unit interval` → 1, `Dyadic.lean:100`, about `ℚ ∩ [0,1)` | `N` |
| N6 | monotone ⟹ continuous when `D` has no infinite ascending chains (row 33) | `WellFoundedGT\|IsWellFounded` → **0** | `ascendingChain\|noInfiniteAscending\|StrictMono.{0,20}bounded` → **0** | `ascending chain` → 4, all `FixedPoint.lean` docstrings about the Kleene chain `⊥ ⊑ f⊥ ⊑ …` | `N`. The finite case is proved (row 32); the chain-condition generalization is not |
| N7 | anything about `N⊥` (rows 34, 44, 56) | `WithBot (Nat\|ℕ)\|Option (Nat\|ℕ)` → **0** | `flatDomain\|FlatOrder\|natBot\|NatBot` → **0** | `discrete order\|discreteOrder\|flat cpo` → 2, `Domain.lean:202` and `LemThirty.lean:509`, both generic remarks | **`N`, and it is one root cause of three rows.** The paper's running example `N⊥` — the flat naturals — is not constructed anywhere in the development, so its three claims (monotone maps out of it are continuous; its function space's compacts are the finite-support functions; `N⊥ ⊸ N⊥` has no top) have no subject to be about |
| N8 | `f : ω⊤ → O` is monotone but not continuous (row 35) | as N3 | `not continuous` → 3, all unrelated: `JungSFP.lean:19, 67` (Jung's `[D → E]` in the domain-theoretic sense) and `ScottHom.lean:217` (the junk branch of `sSup`) | as N7 | `N`. Neither `ω⊤` nor `O` is constructed |
| N9 | `f*`, the extension of `f : S → T` to `P S → P T` (rows 36, 37) | `monotone_image\|scottContinuous_image\|image_isLUB` → **0** | `image_sUnion\|image_iUnion\|image_union` → **0** | `extension of f\|fStar\|imageHom` → **0** | `N` |
| N10 | cpo-continuity on `[0,1]` differs from topological continuity (row 38) | `TopologicalSpace\|nhds\|Metric` → 5, all prose (`Powerdomain/Hoare.lean` on antisymmetry, `NormalSubposet.lean`) | `usual sense\|topologically continuous` → **0** | `ScottTopology\|scottTopology` → **0** | `N`. `ScottDomains.lean` imports `Mathlib.Topology.Order.ScottTopology`, but no declaration in the package uses it |
| N11 | the factorial functional `F` is continuous, and `fix(F)` satisfies the factorial equation (row 39) | `factorial` → **0** | `recursive equation\|recursion equation` → **0** | `Nat\.rec\|fact\(` → 1, `JungFinite.lean:401`, an unrelated recursor | `N`. §2.2's first application is absent |
| N12 | the three context-free-grammar operators are continuous, the equations have least solutions, and the solutions are the languages (row 40) | `grammar\|contextFree\|CFG` → **0** | `alphabet\|language` → 2, `Atomless.lean:54` ("Boolean-algebra language") and `RecursiveDomain.lean:12` (a §7.1 quotation) | `concatenation\|Kleene star\|List\.append` → **0** | `N`. §2.2's second application is absent |
| N13 | `fix_D : (D → D) → D` is continuous (row 41) | `scottContinuous_kleeneFix\|monotone_kleeneFix` → **0** | `fixHom\|kleeneHom\|fixOperatorHom` → **0** | `ScottContinuous \(kleeneFix\|Monotone kleeneFix` → **0** | **`N`.** Every `kleeneFix` occurrence in the package was read: `kleeneFix` is a bare `(α → α) → α` function (`FixedPoint.lean:65`), never bundled as a `ScottHom`, and nothing states it is monotone or continuous in `f` |
| N14 | `fix` is a uniform fixed point operator (row 42) | `kleeneOperator\.IsUniform\|IsUniform kleeneOperator` → **0** | `isUniform_kleene\|kleeneOperator_isUniform` → **0** | `fix is .{0,12}uniform\|uniform fixed point operator` → 3, all `UniformFixedPoint.lean` docstrings **that say it is not proved** | **`N`**, not `P`: the docstring at line 168 does not assert the claim, it reports that the paper leaves it to the reader and that Theorem 3 gives uniqueness "if it exists". `kleeneOperator` (line 121) supplies `isFixedPt` and nothing else; `FixedPointOperator.IsUniform` (line 115) is applied only as a hypothesis, at `theorem3`, `eq_kleeneOperator_op`, and `Audit/Foundations.lean:131` |
| N15 | "all the cpo's mentioned so far are domains" / "all the domains so far are bounded complete" (rows 43, 57) | union of N3–N8's greps | — | — | `N`. Both are quantified over §2.1's example list (`I`, `O`, `T`, `N⊥`, `ω⊤`, `P S`, `Q`, `[0,1]`), of which only `P S` exists in the development. If the orchestrator prefers to exclude meta-claims of this shape, the property total drops 60 → 58 and `N` drops 24 → 22 |
| N16 | a continuous `f : P N → P N` is named by a *countable* `G_f` (row 46) | `countable.{0,20}graph\|graph.{0,20}countable` → 1, `LemThirty.lean:148`, about `V`'s basis | `uncountable` → 8, all §6–§7 (Jung's uncountable family, `LemThirty`'s countability obstruction) | `Countable \(Set (Nat\|ℕ)\)` → **0** | `N`. `FunctionSpaceCountable.countable_compacts_scottHom` (line 113) proves `K(D → E)` countable, which is a different statement — it is about the compacts of the function space, not about one function's graph |
| N17 | each of `f` and `g` uniquely determines the other in an embedding–projection pair (row 47) | `uniquely determines\|unique_projection\|projection_unique` → **0** | `eq_of_isEmbeddingProjectionPair\|embedding_eq\|projection_eq` → **0** | `determines the other\|determined by` → 6, and all six were read: `SFP.lean:172` (a projection is determined by its image), `NormalProjection.lean:4`, `ContinuousConstruction.lean:289`, `Section62.lean:360`, `ContinuousAlgebra.lean:636`, `Skeleton/Lemma17.lean:363` — none is the pair claim | `N` |
| N18 | `D` bounded complete ⟺ `D⊤` is an algebraic lattice (row 54) | `WithTop\|adjoinTop\|addTop` → 2, both Mathlib imports (`Isomorphism/Lift.lean:3`, `Isomorphism/Smash.lean:2`) | `algebraic lattice.{0,30}iff\|iff.{0,30}algebraic lattice` → **0** | `boundedComplete_iff\|BoundedComplete .{0,3}↔` → **0** | `N`. Adjoining a top to a domain is never performed |
| N19 | all the chapter's operators preserve the property of having an effective presentation (row 60) | `preserve.{0,20}presentation\|presentation.{0,20}preserve` → **0** | `effectively presented` → 4, `effective presentation` → 7, all in the two §3.2 modules | as N1 | `N`. This is the widest of the effective-presentation gaps: it is the claim that carries §3.2 forward over §§4–7, and it has no statement |

## 5. The `P` rows

**There are none.** No property of §2 or §3 is asserted in a docstring without a
kernel-checked statement. Row 42 (`fix` is uniform) is the near miss, and it fails
to be `P` because the docstring declines to assert it rather than asserting it —
see N14.

## 6. Two corrections to `docs/`

1. **`PaperInventory.md:483`** names Theorem 2's Mathlib declaration
   `Function.schroeder_bernstein`. That name does not exist. The declaration is
   **`Function.Embedding.schroeder_bernstein`**, at
   `Mathlib/SetTheory/Cardinal/SchroederBernstein.lean:90`, inside `namespace
   Function` (line 37) and `namespace Embedding` (line 39). The row's own
   parenthetical says it is correcting an earlier draft's
   `Function.Embedding.schroederBernstein`; that draft had the namespace right and
   the casing wrong, and the correction fixed the casing while breaking the
   namespace.

2. **`PropertiesVsTheorems.md` §1 row 5** decomposes Theorem 7 as "cpo, bounded
   complete, algebraic, countably based". Those are the four components of *one*
   conjunct — the first sentence's conclusion — and the decomposition has no slot
   for the theorem's other two sentences. The four conjuncts are 7a–7d in §2 above.

3. **r0038's strike of curated claim 8 is correct.** "Every compact function is a
   *finite* join of step functions" is not a claim the paper makes: the paper's
   `step(s)` is defined over a finite `N ◁ K(D)` and so is *already* the finite
   join. The finiteness is an artifact of the development's decomposition into
   single step functions `step k e`, not of the text. `exists_finite_isLUB_of_isCompactElement`
   (`CompactFunction.lean:142`) is real and load-bearing — it is what makes row 22
   `S+P` — but it serves the paper's claim rather than being one.

## 7. Measurement invariance

No `.lean` file was read-write opened this round. `scripts/counts.sh` at the start
and at the end of the round:

    modules:  78
    lines:    28562
    theorems: 1326
    sorry:    1 in 1 file(s)
    ScottDomains/ScottDomains/Skeleton/Section6.lean:197

The one file written is `scripts/a1-absence-greps.sh`, which is read-only over the
package and is the evidence for §4.
