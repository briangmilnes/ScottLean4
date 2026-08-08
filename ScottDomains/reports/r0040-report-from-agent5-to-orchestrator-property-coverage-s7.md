---
round: r0040
from: agent5
to: orchestrator
subject: property-coverage-s7
date: 2026-0808-11:53
started: 2026-0808-11:36
finished: 2026-0808-11:53
related:
  - plans/r0040-plan-from-orchestrator-to-orchestrator-property-coverage.md
  - docs/PropertiesVsTheorems.md
  - docs/PaperInventory.md
---

# §7 property coverage — does each property Gunter & Scott §7 asserts have a Lean statement?

Direction: **paper → development**. The properties were enumerated from the PDF
first (`scripts/pdf-section.sh`, `pdf-render.sh` at 200 dpi over physical pages
34, 38, 40, 42, 43 = printed 33, 37, 39, 41, 42), and only then matched against
declarations found with `scripts/lean-decls.py --list` over the twenty
§7-bearing modules (608 declarations,
`scripts/a5-s7-decls.sh`). No `.lean` file was edited; the one `sorry` in the
package (`Skeleton/Section6.lean:197`, §6's `thm18`) is untouched and none is in
§7.

## Headline

| # | Quantity | Value |
| -- | -------- | ----- |
| 1 | §7 paper properties enumerated | **61** — 33 conjuncts of the 12 numbered results, 28 unnumbered prose claims |
| 2 | `S+P` stated and proved | **22** |
| 3 | `S≠` stated, not the paper's statement | **7** |
| 4 | `S+H` stated, proof open | **14** |
| 5 | `P` prose only | **5** (+2 development-side refutation rows, §6 below) |
| 6 | `N` **not stated** | **13** |

**Every one of the 13 `N` rows is an unnumbered prose claim. Zero of the 33
numbered conjuncts is `N`.** §7's numbered results are stated in full, without
exception; the gap is entirely in the paragraphs between them.

**A conjunct stated only as a component of a conjunction is stated.**
`PRep.Lemma28` is one nine-fold `def … : Prop` and `LemThirty.Lemma30` a ten-fold
one, and `lemma28_of` / `lemma30_of` take one named hypothesis per conjunct, so
the kernel checks the arity. Lemma 30 is `0 of 10` **proved** and `10 of 10`
**stated**; Lemma 28 is `7 of 9` proved and `9 of 9` stated. Reading the low
proved-count as a coverage gap would be wrong: the correct label for the three
open conjuncts is `S+H`, not `N`.

## 1. Re-derived conjunct counts, against `PropertiesVsTheorems.md` §1

| # | Result | § | printed p | re-derived | doc §1 | moved |
| -- | ------ | - | --------: | ---------: | -----: | ----- |
| 1 | Lem 19 | 7.1 | 33 | 1 | 1 | — (but **filed under §6**, see below) |
| 2 | Lem 20 | 7.1 | 33 | 1 | 1 | — (same) |
| 3 | Thm 21 | 7.1 | 34 | 1 | 1 | — |
| 4 | Thm 22 | 7.1 | 34 | 1 | 1 | — |
| 5 | Lem 23 | 7.1 | 35 | 1 | 1 | — |
| 6 | Lem 24 | 7.2 | 37 | **2** | 1 | **+1** |
| 7 | Thm 25 | 7.2 | 37 | **3** | 1 | **+2** |
| 8 | Thm 26 | 7.2 | 39 | 1 | 1 | — |
| 9 | Thm 27 | 7.3 | 41 | 1 | 1 | — |
| 10 | Lem 28 | 7.3 | 41 | 9 | 9 | — |
| 11 | Thm 29 | 7.4 | 42 | 2 | 2 | — |
| 12 | Lem 30 | 7.4 | 42 | 10 | 10 | — |
| — | **§7 total** | — | — | **33** | 30 | **+3** |

Two counts moved, both read off the 200 dpi render of printed page 37:

* **Lemma 24 is 2, not 1.** "…then there are non-trivial domains `D` and `E` such
  that `E ≅ E × E` **and** `D ≅ D → E`." Two isomorphisms about two different
  objects; neither implies the other.
* **Theorem 25 is 3, not 1.** "…there is a non-trivial domain `D` such that
  `D ≅ D × D ≅ D → D` **and** `D` is the image of a closure on `U`." The chained
  `≅` is two conjuncts (`D ≅ D × D`, `D ≅ D → D`) and the closure clause is a
  third; `Universality.thm25`'s conclusion has exactly these three components
  plus `Nontrivial`.

Lemma 28's nine and Lemma 30's ten were **not** re-derived — the plan records the
operator lists as settled by three independent 600 dpi reads, and `PRep.lean`'s
docstring says not to re-derive them. The 200 dpi renders of printed pages 41 and
42 are consistent with both lists (`→, ⇸, ×, ⊗, +, ⊕, (·)⊥, (·)♯, (·)♭` for
Lemma 28; the same plus `(·)♮` for Lemma 30) and nothing was disturbed.

**Section misattribution in `PropertiesVsTheorems.md` §1, row 13.** That row reads
"§6 | Prop 15, Thm 18, Lem 19, Lem 20". **Lemmas 19 and 20 are in §7.1**, printed
page 33, between the definition of *finitary closure* and the definition of
*representable* — verified on the render of physical page 34. §6 ends with
Theorem 18 on printed page 32. The conjunct count is unaffected (1 each); the
section label is wrong, and it is why the plan's stream table gave agent4 two of
my results. The development already has this right:
`Skeleton/Section6b.lean` is titled "§6.2 **and §7.1**: Theorem 16 and Lemma 20".

**The paper never defines `V`.** Lemma 30 reads "p-representable over `V`" and
§7.4's closing recipe writes `Φ♮ : V → V♮`, but §7.4 introduces only `M(A)`, `⊢`
and `D⁺`; no sentence says what `V` is. It can only be the fixed point of
`D ↦ D⁺` that Theorem 29's second sentence presupposes. The development supplies
it as `Colimit.V` with `Colimit.iso_plus_V : V ≃o Plus V`. A second, smaller
defect in the same definition: §7.4 writes "given a domain `D`, we define `D⁺` to
be the domain of ideals over `⟨M(A), ⊢⟩`" — `A` is unbound and must be `K(D)`,
which is what `BifiniteUniversal.Plus D = IdealCompletion (MPair ↥(compacts D))`
reads it as.

## 2. The 33 numbered conjuncts

| # | Property (paper's sentence) | § / p | Label | Declaration | Evidence |
| -- | --------------------------- | ----- | ----- | ----------- | -------- |
| 1 | Lem 19: `D` a domain, `r ∘ r = r ⊒ id` ⟹ `im(r)` is a domain | 7.1 / 33 | `S+P` | `FinitaryProjectionPoset.IsClosure.domain_range` | algebraicity + countable basis of the range, both proved; `Skeleton.Section6.lem19` is only the cpo half and would be `S≠` on its own |
| 2 | Lem 20: `D` a domain ⟹ `Fc(D)` is a cpo | 7.1 / 33 | `S+P` | `Skeleton.Section6b.lem20` | plus the second conjunct that the cpo order is the pointwise one; `Recursive.closureCpo` repeats it over a bare cpo, which is what Thm 21 needs |
| 3 | Thm 21: `F` representable over a cpo `U` ⟹ ∃ `D`, `D ≅ F(D)` | 7.1 / 34 | `S+P` | `Recursive.thm21` | hypothesis is `[CompletePartialOrder U]` only, exactly as printed |
| 4 | Thm 22: `L` a countably based algebraic lattice ⟹ ∃ closure `r : P N → L` | 7.1 / 34 | `S+P` | `UniversalDomain.thm22` | with `thm22_of_isCompactlyGenerated` restating it in Mathlib's vocabulary |
| 5 | Lem 23: `→` is representable over `P N` | 7.1 / 35 | `S+P` | `UniversalDomain.lem23` | the paper's `R→(r,s) = →⁺ ∘ (s,r) ∘ →⁻`, all three obligations of `IsRepresentable₂` discharged |
| 6 | Lem 24a: ∃ non-trivial **domain** `E` with `E ≅ E × E` | 7.2 / 37 | `S≠` | `Universality.lem24` | conclusion is `Cpo`, not `Domain` — see below |
| 7 | Lem 24b: ∃ non-trivial **domain** `D` with `D ≅ D → E` | 7.2 / 37 | `S≠` | `Universality.lem24` | same |
| 8 | Thm 25a: `D ≅ D × D` | 7.2 / 37 | `S≠` | `Universality.thm25` | same |
| 9 | Thm 25b: `D ≅ D → D` | 7.2 / 37 | `S≠` | `Universality.thm25` | same |
| 10 | Thm 25c: `D` is the image of a closure on `U` | 7.2 / 37 | `S≠` | `Universality.thm25` | the clause itself is verbatim (`IsClosureOf D (cpoOf U)`); the object it is about is a `Cpo` |
| 11 | Thm 26: any signature `(s₁,…,s_n)` admits combinations `F₁,…,F_n` into which every continuous algebra on a retract of `D` embeds | 7.2 / 39 | `S≠` | `Combinator.thm26`, `thm26_subalgebra`, `thm26_retract` | carries `hs : ∀ i, 0 < s i`; the paper explicitly admits arity `0` ("signature `(2,0,0,0,0,0)`… `0` indicates a 0-ary operation", printed p. 38) |
| 12 | Thm 27: for any bounded complete domain `D` there is a projection `p : U → D` | 7.3 / 41 | `S+P` | `Atomless.thm27` | **unconditional**. `Dyadic.thm27` is the one that retains a hypothesis — `h : IsNormallyRepresented ↥(compacts D)` — and `Atomless.isNormallyRepresented_compacts` discharges it. Both deliver an embedding–projection pair, stronger than "a projection" |
| 13 | Lem 28, `→` | 7.3 / 41 | `S+P` | `Lemma28AtU.repArrowAtU` | at `Dyadic.U`, no hypothesis |
| 14 | Lem 28, `⇸` | 7.3 / 41 | `S+P` | `Lemma28AtU.repStrictArrowAtU` | needs `PRepFun.strictHomDomain`, new in r0037 |
| 15 | Lem 28, `×` | 7.3 / 41 | `S+P` | `PRepSum.repProdAtU` | |
| 16 | Lem 28, `⊗` | 7.3 / 41 | `S+P` | `Lemma28AtU.repSmashAtU` | |
| 17 | Lem 28, `+` | 7.3 / 41 | `S+P` | `PRepSum.repSepSumAtU` | |
| 18 | Lem 28, `⊕` | 7.3 / 41 | `S+P` | `PRepSum.repCoalSumAtU` | |
| 19 | Lem 28, `(·)⊥` | 7.3 / 41 | `S+P` | `PRepSum.repLiftAtU` | |
| 20 | Lem 28, `(·)♯` | 7.3 / 41 | `S+H` | conjunct 8 of `PRep.Lemma28`; open as `h_smyth` of `Lemma28AtU.lemma28AtU_of'` | operator defined (`PRep.smythOp`); no `sorry` — the arity 2 of `lemma28AtU_of'` is the measurement |
| 21 | Lem 28, `(·)♭` | 7.3 / 41 | `S+H` | conjunct 9 of `PRep.Lemma28`; open as `h_hoare` | same |
| 22 | Thm 29, sentence 1: `D` bifinite ⟹ `D⁺` bifinite | 7.4 / 42 | `S+P` | `BifiniteUniversal.thm29` | |
| 23 | Thm 29, sentence 2: `D ≅ D⁺`, `E` a bifinite **domain** ⟹ ∃ projection `p : D → E` | 7.4 / 42 | `S+H` | `LemThirty.Thm29SecondAtDomains`, reduced to the named `Prop` `LemThirty.Thm29Normal` | `exists_embeddingProjectionPair_of_thm29Normal` and `thm29SecondAtDomains_of_thm29Normal` are proved; the residue is `Thm29Normal` alone. `Colimit.Thm29Second` is the *stronger* form without `[Domain E]` — see §6 |
| 24 | Lem 30, `→` | 7.4 / 42 | `S+H` | conjunct 1 of `LemThirty.Lemma30`; also `Colimit.Lem30Arrow` | |
| 25 | Lem 30, `⇸` | 7.4 / 42 | `S+H` | conjunct 2 of `LemThirty.Lemma30` | |
| 26 | Lem 30, `×` | 7.4 / 42 | `S+H` | conjunct 3; **proved conditionally** by `LemThirty.rep_prod_V` / `rep_prod_V_of_thm29Normal` | |
| 27 | Lem 30, `⊗` | 7.4 / 42 | `S+H` | conjunct 4; pair from `retracts_smash` | |
| 28 | Lem 30, `+` | 7.4 / 42 | `S+H` | conjunct 5; pair from `retracts_sepSum` | |
| 29 | Lem 30, `⊕` | 7.4 / 42 | `S+H` | conjunct 6; pair from `retracts_coalSum` | |
| 30 | Lem 30, `(·)⊥` | 7.4 / 42 | `S+H` | conjunct 7; **proved conditionally** by `LemThirty.rep_lift_V` / `rep_lift_V_of_thm29Normal` | |
| 31 | Lem 30, `(·)♯` | 7.4 / 42 | `S+H` | conjunct 8; pair from `retracts_smyth` | |
| 32 | Lem 30, `(·)♭` | 7.4 / 42 | `S+H` | conjunct 9; pair from `retracts_hoare` | |
| 33 | Lem 30, `(·)♮` | 7.4 / 42 | `S+H` | conjunct 10 (`LemThirty.plotkinOp`); pair from `retracts_plotkin` | `lemma30_iff_lemma28_and_plotkin` turns "Lemma 28's nine plus `(·)♮`" from prose into a theorem |

**Why rows 6–10 are `S≠` and not `S+P`.** Lemma 24 and Theorem 25 conclude about
`Cpo`, not `Domain`: `Universality.lem24` returns `∃ D E : Cpo.{u}, …` and
`thm25` returns `∃ D : Cpo.{u}, …`, where the paper says "non-trivial **domains**
`D` and `E`" and "a non-trivial **domain** `D`". The module docstring
(`Universality.lean:70–81`) states the reason and it is a claim about the paper,
not about Lean: *the paper's own proof produces cpos* — "Hence there is a **cpo**
`D ≅ D → E`" — because it invokes Theorem 21, which returns `im(r)` for a closure
`r`, and nothing in the chain establishes algebraicity or countability of the
basis. Theorem 25's hypothesis is *weakened* in the same edit (a cpo `U`, not a
domain), which strengthens the theorem; the conclusion is weakened, which is what
makes the label `S≠`. No `P` row is added for this: it is a stated deviation with
a stated reason, and it is not a claim the development asserts and leaves
unchecked.

## 3. The 28 unnumbered prose claims of §7

| # | Claim | § / p | Label | Declaration / evidence |
| -- | ----- | ----- | ----- | ---------------------- |
| 1 | the full simple binary tree with limit points added is a solution of `T ≅ T + T` | 7 / 33 | **`N`** | greps §5 |
| 2 | a composition of representable operators is representable | 7.1 / 34 | **`N`** | greps §5 |
| 3 | `X ≅ X × I⊤` has `(I⊤)^N` as a solution, and `(I⊤)^N ≅ P N` | 7.1 / 34 | **`N`** | greps §5 |
| 4 | `P N` is a *universal domain* — a rich collection of domains as retracts | 7.1 / 35 | `S+P` | `Recursive.powersetCpo_isUniversalRetract` and `powersetCpo_isUniversal`, over `IsUniversalRetract` / `IsUniversal`; both of the paper's two phrasings are defined and `IsUniversal.of_retract` connects them |
| 5 | there is no representation for `F(X) = X + X` over `P N` (restated in §7.3, p. 40, as "`P N` cannot represent the sum operator `+`") | 7.1 / 35, 7.3 / 40 | `P` | asserted and relied on in `CombinatorRep.lean:46`, `Powerdomain/Universal.lean:82`, `PRep.lean:282`; it is the reason §7.3 introduces `U` at all, and no declaration states it |
| 6 | the product operator is representable over `P N` | 7.1 / 36 | `S+P` | `PowerdomainRep.isRepresentable_prod` |
| 7 | the constant operator `X ↦ L` is representable over `P N`, for `L` an algebraic lattice | 7.1 / 36 | **`N`** | greps §5 |
| 8 | `X ↦ D` is representable over a domain `U` **iff** `D` is a closure of `U` | 7.1 / 36 | `P` | `Universality.lean:283` quotes it and says it "is used below only in the direction it is needed, and only at two closures" (`idClosureImageIso`, and the closure representing `E`); the biconditional is nowhere stated |
| 9 | `I ≅ I → I`, so solving `D ≅ D → D` guarantees nothing interesting | 7.2 / 36 | `P` | asserted at `Universality.lean:11–16` and relied on at `RecursiveDomain.lean:379–382` ("What is **not** claimed: that `D` is nontrivial"); `PUnit` exists but no declaration states `PUnit ≃o ScottHom PUnit PUnit` |
| 10 | `D` will have `P N` itself represented by a closure on `U`; take `U = P N` | 7.2 / 37 | `S+P` | `Universality.thm25_powerset`, `thm25_isUniversal` |
| 11 | λ-equation 1: `(λx. E) = (λy. [y/x]E)` (α) | 7.2 / 37 | **`N`** | greps §5 — there is no λ-term syntax; `Comb` is variable-free by construction |
| 12 | λ-equation 2: `(λx. E)(E') = [E'/x]E` (β) | 7.2 / 37 | `S+P` | in its semantic form, `Combinator.LambdaModel.app_lam`, discharged by `LambdaModel.ofOrderIso` and inhabited by `Combinator.exists_lambdaModel_of_thm25`. As a *syntactic* equation with substitution it is not stated |
| 13 | λ-equation 3: `(λx. E(x)) = E` (η) | 7.2 / 37 | **`N`** | greps §5 — `LambdaModel` has `app_lam` but no `lam_app` field or lemma |
| 14 | λ-equation 4: `fst(pair(E)(E')) = E` | 7.2 / 38 | `S+P` | `Combinator.LambdaModel.fst_pair` |
| 15 | λ-equation 5: `snd(pair(E)(E')) = E'` | 7.2 / 38 | `S+P` | `Combinator.LambdaModel.snd_pair` |
| 16 | λ-equation 6: `pair(fst(E))(snd(E)) = E` (surjective pairing) | 7.2 / 38 | **`N`** | greps §5 |
| 17 | equations 3 and 6 are independent of the other four — there are models where `D → D` and `D × D` are closures on `D` but not isomorphic to it | 7.2 / 38 | **`N`** | greps §5 |
| 18 | `pair(x)(y) = (λz. pair(x(z))(y(z)))` is independent of the six, and a model for it exists | 7.2 / 38 | **`N`** | greps §5 |
| 19 | `(· + ·)⊤` is representable over `P N`, but the added top element is unmotivated | 7.3 / 40 | **`N`** | greps §5 |
| 20 | `B = U₀ ∪ {∅}` is a Boolean algebra; it is countable and atomless; hence the free one on countably many generators; hence every countable Boolean algebra embeds in it | 7.3 / 41 | **`N`** | greps §5. `Atomless.lean:31–55` says so explicitly: "What is proved here instead is the conclusion directly, by an explicit construction, and **it never mentions a Boolean algebra**" |
| 21 | `i : x ↦ ↑x` is a monotone injection preserving existing least upper bounds, and `u ⊆ A` is bounded just in case `⋂_{x∈u} ↑x ≠ ∅` | 7.3 / 41 | **`N`** | greps §5. The development proves the analogues for its own `ψ` (`Atomless.psi_le_psi`, `psi_injective`, `bddAbove_of_psiSet_inter_nonempty`, `psiSet_inter`), never for `i` |
| 22 | the paragraph's conclusion: `A` a countable bounded complete poset ⟹ `A` is order-isomorphic to a normal subposet `A' ◁ U₀` | 7.3 / 41 | `S+P` | `Atomless.isNormallyRepresented`, named as `Dyadic.IsNormallyRepresented` so the paragraph can be checked on its own |
| 23 | `X ≅ N⊥ + (X → X)` has a solution, represented over `U` by `p ↦ R+(R_{N⊥}(p), R→(p,p))` | 7.3 / 41 | **`N`** | greps §5 |
| 24 | the convex powerdomain `(·)♮` cannot be representable over `U`, because it does not preserve bounded completeness | 7.4 / 42 | `P` | asserted in five docstrings — `PRep.lean:38`, `PRep.lean:251`, `Colimit.lean:1021`, `BifiniteUniversal.lean:14`, `LemThirty.lean:167` — and load-bearing: it is the stated reason `(·)♮` is absent from `PRep.Lemma28`'s nine. No declaration states it |
| 25 | `I⁺` has exactly two elements, `a = (⊥,{⊥})` and `b = (⊥,∅)` | 7.4 / 42 | `S+P` | `BifiniteUniversal.mpair_punit_eq` |
| 26 | `I⁺⁺` has five elements and `I⁺⁺⁺` has twenty, up to the identification | 7.4 / 42 | `P` | computed by `scripts/mpair-stages.py` (1, 2, 5, 20 for the adopted order against 1, 2, 5, 21 for the Smyth rival) and recorded at `Colimit.lean:70–73`; nothing in Lean computes a cardinality of `Stg 2` or `Stg 3` |
| 27 | each stage is embedded in the next by `x ↦ (x, {x})` | 7.4 / 42 | `S≠` | `BifiniteUniversal.eta_le_eta_iff` proves `eta` is order-reflecting, hence an embedding — but `Colimit.stgEmb_ne_mk_eta` **kernel-checks** that the colimit *along* `eta` is not a fixed point of `M`, so the development's chain applies `M` to the previous connecting map instead. The sentence about one stage is proved; the chain it describes is refuted, under the kernel |
| 28 | `R♮(p) = Ψ♮ ∘ (p♮) ∘ Φ♮` represents the convex powerdomain | 7.4 / 42 | `S+H` | the conjugation half is generic and proved — `PRepresentable.isProjection_repOf`, `PRep.isFinitaryProjection_repOf`, `PRep.isPRepresentable_of_repFamily`; the `(·)♮` instance is Lemma 30's tenth conjunct with the pair from `LemThirty.retracts_plotkin`, open behind `Thm29Normal` |

Two §7 remarks are excluded as not being checkable assertions: "the technique can
be generalized and used for other classes as well [GJ90]" (7.4 / 42), and the
closing paragraph's methodological summary that most operators are handled by
their action on functions while `→` and `⇸` need a map like `Φ` (7 / 44).

**The "13 unnumbered prose claims" figure in `PaperInventory.md` row 3 is not an
enumeration of the paper's prose claims.** §7 alone has 28 at this granularity,
before §2–§6 are counted. Row 3 counts prose claims the development **proves**;
it cannot be used as a denominator for coverage, and `PropertiesVsTheorems.md`
§1 row 20 currently does use it that way.

## 4. Definitions of §7 (excluded from the property count, all present)

| # | Paper object | Lean |
| -- | ------------ | ---- |
| 1 | closure `r : D → E` with section `s` | `IsClosure`, `IsClosurePair` |
| 2 | finitary closure; `Fc(D)` | `IsFinitaryClosure`, `Fc`, `Recursive.ClosurePoset` |
| 3 | recursive domain equation and its solution | `Recursive.Solves`, `Recursive.IsSolvable` |
| 4 | representable over a cpo `U` (the `Fc` square) | `Recursive.IsRepresentable`, `IsRepresentable₂` |
| 5 | universal domain | `Recursive.IsUniversal` (image-of-a-closure) and `IsUniversalRetract` (retract); both of the paper's two sentences |
| 6 | `P N` | `Set ℕ`, `Recursive.powersetCpo` |
| 7 | p-representable over `U` (the `Fp` square) | `BifiniteUniversal.IsPRepresentable`, `IsPRepresentable₂` |
| 8 | `U₀`, the finite unions of half-open dyadic intervals under `⊇`; `U` its ideals | `Dyadic.U₀`, `Dyadic.U` |
| 9 | `M(A)`, `⊢`, `D⁺` | `BifiniteUniversal.MPair`, `MPair.PaperLE`, `Plus` |
| 10 | `V` (**used but never defined in the paper**) | `Colimit.V`, with `iso_plus_V : V ≃o Plus V` |

## 5. The 13 `N` rows, with the greps that justify each

Every grep is `grep -rn … ScottDomains/ScottDomains --include=*.lean`, run by
`scripts/a5-s7-prose-greps.sh`; the transcript is reproducible by re-running it.

| # | Claim | grep 1 | grep 2 | grep 3 | result |
| -- | ----- | ------ | ------ | ------ | ------ |
| 1 | binary tree solves `T ≅ T + T` | `IsSolvable\|Solves ` | `IsSolvable.*sepSum` | `binaryTree` | 10 hits on grep 1 — the two definitions and every use, and the only two solvability theorems in the development are `Recursive.recursiveDomain_funSpace` and `PowerdomainRep.recursiveDomain_prod`; 0 on greps 2 and 3. `T + T` occurs once in the whole development, as quoted paper text at `RecursiveDomain.lean:13` |
| 2 | composition of representable operators | `IsRepresentable.comp` | `isRepresentable_comp` | `[Rr]epresentable.*compos` | 0, 0, 0 |
| 3 | `X ≅ X × I⊤`, `(I⊤)^N ≅ P N` | `twoPoint\|TwoPoint\|Sierpinski` | `Set ℕ ≃o` | `ℕ → Prop` | 0, 0, 2 (both `P : ℕ → Prop` binders in `Atomless.lean`). Note the second half is *definitionally* true in Lean (`Set ℕ` **is** `ℕ → Prop`), which makes its absence a choice rather than a difficulty |
| 7 | constant operator `X ↦ L` over `P N` | `constOp` | `isRepresentable_const` | `constant operator` | 0, 0, 1 — and that one hit (`Universality.lean:283`) is the *other* claim, row 8 |
| 11 | λ-equation 1 (α) | `alpha\|beta_\|eta_conv\|_beta\|_eta\b` | `LamTerm\|Term\b` | `subst` | 0 relevant; `Comb` is `S \| K \| fstC \| sndC \| ap` — no variables, so α-conversion has no subject |
| 13 | λ-equation 3 (η) | `lam_app` | `eta_law` | `_eta\b` | 0, 0, hits only `mpairMap_eta` / `mem_upper_eta` in `Colimit`/`BifiniteUniversal`, which are §7.4's `x ↦ (x,{x})` |
| 16 | λ-equation 6 (surjective pairing) | `pair_fst_snd` | `surjective pairing` | `lam_app` | 0, 0, 0. `LambdaModel` has `fst_pair` and `snd_pair`, the two projection laws, and no converse |
| 17 | equations 3 and 6 independent | `independen` | `pointwise pair` | `LambdaModel` | 13 hits on grep 1, none about λ-equations; 0; 20 hits, no independence result |
| 18 | pointwise pairing equation | `pointwise pair` | `independen` | `LambdaModel` | 0; as above; as above |
| 19 | `(· + ·)⊤` representable over `P N` | `WithTop` | `sumTop\|topSum` | `unmotivated\|gets in the way` | 2 (both `import Mathlib.Order.Hom.WithTopBot`), 0, 0 |
| 20 | `B` a countable atomless Boolean algebra, universal for countable Boolean algebras | `[Bb]ooleanAlgebra` | `IsAtomless` | `Vaught` | 0 declarations; the only hits are prose at `Dyadic.lean:423,429` and `Atomless.lean:33,36`, both of which say the route is **not** taken |
| 21 | `i : x ↦ ↑x` monotone injective lub-preserving; `u` bounded iff `⋂ ↑x ≠ ∅` | `upperClosure` | `Ici` | `principalFilter` | 0, 0, 0. `↑x = {y ∈ A \| x ⊑ y}` appears twice, both inside quoted paper text (`Dyadic.lean:402`, `Atomless.lean:20`) |
| 23 | `X ≅ N⊥ + (X → X)` has a solution | `N⊥` | `WithBot ℕ` | `LazyNat\|natOp\|NatBot` | 1 (`Powerdomain/Smyth.lean:222`, about `(N⊥)♭` in a different context), 0, 0 |

Row 3's second half and rows 11/13/16 are the cheapest of these to close; row 20
is the most expensive and the development has already decided against it on
recorded grounds.

## 6. `P` rows: claims asserted in prose and never put under the kernel

Five are paper properties (rows 5, 8, 9, 24, 26 of §3). Two more are
**development-side refutations** — claims the development makes *about* a paper
result, load-bearing for how that result is stated, and not kernel-checked:

| # | Claim | Where | Why it matters |
| -- | ----- | ----- | -------------- |
| 1 | Theorem 26 is **false** for a signature admitting arity `0` | `Combinator.lean:60–72`, and the file says so: "by the following argument, which is stated here and is *not* Lean-checked" | it is the entire justification for `hs : ∀ i, 0 < s i`, which is why row 11 of §2 is `S≠`. The argument: `Fᵢ` is one fixed element of `D`, two one-point retracts with different constants must both embed onto it, and `fst(ψ(x)) = x` then forces them equal |
| 2 | `Colimit.Thm29Second` is **stronger** than the printed sentence and **false** without `[Domain E]` | `LemThirty.lean:506–512` | `countable_compacts_of_reflects` *is* kernel-checked; the step from it to "an uncountable flat cpo is bifinite, so no such `f` exists" is not. It is the justification for `Thm29SecondAtDomains` restoring the paper's word "domain", and **five** of the ten retraction-pair lemmas still take the stronger form (`retracts_smash`, `retracts_sepSum`, `retracts_coalSum`, `retracts_fun_of_boundedComplete`, `retracts_strictFun_of_boundedComplete`) against five that take the paper's (`retracts_lift`, `retracts_prod`, `retracts_smyth`, `retracts_hoare`, `retracts_plotkin`) |

Both are cheap to close and both have precedents in this development
(`lem9_3_printed_false`, `FinitaryProjectionEmbedding`'s Theorem 16 refutation)
for turning exactly this kind of argument into a kernel-checked negation.

## 7. Two stale docstring claims found in `PRepresentable.lean`

Reported, not fixed — no `.lean` file is edited this round.

1. **`PRepresentable.lean:39–43`** says: "Lemma 28 (`→, ⇸, ×, ⊗, +, ⊕, ()⊥, ()♯,
   ()♭` representable over §7.3's `U`) is the `Fc` notion; Lemma 30 … is the `Fp`
   notion." This is false about the development's own code: `PRep.Lemma28` is
   built from `IsPRepresentable₂` / `IsPRepresentable`, the **`Fp`** notion, and
   `PRep.lean:73` records the correction. `PaperInventory.md` row for Lemma 28
   states that this docstring claim *was* corrected; the correction did not reach
   this file.
2. **`PRepresentable.lean:62–67`** says: "**Lemma 30 itself is not proved, for any
   of its ten operators.** … `V` does not exist in this development … not the
   ω-colimit that solves `V ≅ V⁺`." `Colimit.V` exists with `domain_V`,
   `isBifinite_V` and `iso_plus_V` (r0036). The first sentence is still true; the
   reason given for it is not.

Both are exactly the defect class r0038 named — a file asserting something false
about itself — and neither is visible to `lake build`.

## 8. What did not change

No `.lean` file was edited. The `sorry` count over `ScottDomains/` is **1**
(`Skeleton/Section6.lean:197`, §6's Theorem 18), unchanged, and none is in §7.
The numbered-result count is unchanged. Two scripts were added,
`scripts/a5-s7-decls.sh` and `scripts/a5-s7-prose-greps.sh`, both read-only over
the sources.
