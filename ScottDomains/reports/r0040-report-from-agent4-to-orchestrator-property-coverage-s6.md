---
round: r0040
from: agent4
to: orchestrator
subject: property-coverage-s6
date: 2026-0808-11:53
started: 2026-0808-11:35
finished: 2026-0808-11:53
related:
  - plans/r0040-plan-from-orchestrator-to-orchestrator-property-coverage.md
  - docs/PropertiesVsTheorems.md
  - docs/PaperInventory.md
---

# §6 property coverage: does every property §6 asserts have a Lean statement?

Direction: **paper → development**. The properties below were enumerated from the
rendered PDF *before* any Lean file was opened, per the plan.

## Source and page mapping

`ScottDomains/papers/Gunter Scott 1990.pdf`. Physical page = printed page + 1.
§6 runs printed pages **29–32** (physical 30–33). Lemma 19 and Lemma 20 are
**not in §6**: they are in **§7.1**, printed page 33 (physical 34). Both
`PropertiesVsTheorems.md` §1 row 13 and `PaperInventory.md` place them in §6.
That is a sectioning error, and it is the second one this round has found (the
orchestrator relayed agent3's finding that Theorem 14 is §6.1, not §4.5).

Lemma 17's ten-operator list was read off a 600 dpi crop of physical page 33
(`scripts/pdf-crop.sh … 33 600 400 2380 3800 320`), not off `pdftotext`. The
rendered list is

> **Lemma 17** If `D` and `E` are bifinite domains, then so are the cpo's
> `D → E`, `D ◦→ E`, `D × E`, `D ⊗ E`, `D + E`, `D ⊕ E`, `D⊥`, `D♮`, `D♯` and
> `D♭`.

Ten operators, confirmed. `D ◦→ E` is the **strict** function space — the paper
fixes that notation at printed page 5 ("A function `f : D → E` is said to be
strict if `f(⊥) = ⊥`. We will usually write `f : D ◦→ E` to indicate that `f` is
strict… the set of strict continuous functions `D ◦→ E` is also a cpo"), checked
against the extraction rather than inherited from an earlier round's table.

## Scope boundary

Theorem 14 sits physically in §6.1 but is agent3's row; it is not re-audited
here. Everything else in §6.1 — the two prose facts about finitary projections,
the Plotkin-order definition, the three facts, and the three Figure 3 claims —
is covered below, so nothing in §6.1 falls between the two streams.

## Rule adopted for the `P` label

A **verbatim block quotation of the paper** inside a docstring is *not* the
development asserting the claim; otherwise every quoted numbered result would be
`P` and the label would carry no information. `P` requires the development to
state the claim in **its own prose**. This rule is applied consistently below and
moves two rows from `P` to `N`.

---

## 1. The six numbered results (16 conjuncts)

| # | Property (paper's sentence) | § / printed p. | Label | Declaration | Evidence |
| -- | --------------------------- | -------------- | ----- | ----------- | -------- |
| 1 | **Prop 15.** A bounded complete domain is bifinite. | 6.2 / 31 | `S+P` | `ScottDomains.prop15` | `Skeleton/Section6.lean:142`, `[Domain α] [BoundedComplete α] : IsBifinite α`. Follows the paper's own proof with `N = lubClosure u`. See §4 below on `IsBifinite` vs. the paper's definition. |
| 2 | **Thm 16, conjunct 1.** `D` bifinite ⟹ `Fp(D)` is an algebraic lattice. | 6.2 / 32 | `S+P` | `ScottDomains.thm16` | `Skeleton/Section6b.lean:80`. Existential in the `CompleteLattice` structure (because `IsBifinite` is a `def`, not a class) with a middle conjunct pinning the lattice order to the pointwise order — without which the existential would be satisfied by any complete lattice at all. Witnesses `Fp.completeLattice`, `Fp.isCompactlyGenerated`. |
| 3 | **Thm 16, conjunct 2.** The inclusion `i : Fp(D) ↪ (D → D)` is an embedding. | 6.2 / 32 | `S≠` **+ refuted** | `Section62.thm16_positive`; refutation `FpEmbedding.TwoMub.not_isEmbeddingProjectionPair` | See §2 below — the row that needs the most explanation. |
| 4 | **Lem 17, `D → E`.** | 6.2 / 32 | `S≠` | `ClosureProperties.lem17_fun` | `Skeleton/Lemma17.lean:403`. Carries `[BoundedComplete β]`, which the paper does not require. See §3. |
| 5 | **Lem 17, `D ◦→ E`.** | 6.2 / 32 | `S≠` | `ClosureProperties.lem17_strictFun` | `ClosureProperties/StrictFunction.lean:317`. Same extra `[BoundedComplete β]`. See §3. |
| 6 | **Lem 17, `D × E`.** | 6.2 / 32 | `S+P` | `ScottDomains.lem17_prod` | `Skeleton/Lemma17.lean:101`, hypotheses `[Domain α] [Domain β]` + two `IsBifinite`. |
| 7 | **Lem 17, `D ⊗ E`.** | 6.2 / 32 | `S+P` | `ScottDomains.lem17_smash` | `Skeleton/Sum.lean:920`. |
| 8 | **Lem 17, `D + E`.** | 6.2 / 32 | `S+P` | `ClosureProperties.lem17_separated` | `ClosureProperties/SeparatedSum.lean:160`. `+` is the separated sum `D⊥ ⊕ E⊥`, distinct from `⊕`. |
| 9 | **Lem 17, `D ⊕ E`.** | 6.2 / 32 | `S+P` | `ScottDomains.lem17_sum` | `Skeleton/Sum.lean:561`. |
| 10 | **Lem 17, `D⊥`.** | 6.2 / 32 | `S+P` | `ScottDomains.lem17_lift` | `Skeleton/Lemma17.lean:204`. Unary, so stated at `α` alone. |
| 11 | **Lem 17, `D♮`.** | 6.2 / 32 | `S+P` | `ClosureProperties.lem17_plotkin` | `ClosureProperties/Powerdomain.lean:328`, `[Domain D] (h : IsBifinite D) : IsBifinite (Plotkin.Powerdomain D)`. |
| 12 | **Lem 17, `D♯`.** | 6.2 / 32 | `S+P` | `ClosureProperties.lem17_smyth` | `ClosureProperties/Powerdomain.lean:266`. `Smyth.Powerdomain` is `D♯`, per §5.2's quoted definition in `Powerdomain/Smyth.lean:23`. |
| 13 | **Lem 17, `D♭`.** | 6.2 / 32 | `S+P` | `ClosureProperties.lem17_hoare` | `ClosureProperties/Powerdomain.lean:208`. |
| 14 | **Thm 18.** If `D` and `D → D` are domains, then `D` is bifinite. | 6.2 / 32 | `S+H` | `ScottDomains.thm18`; open steps `JungNets.Thm137`, `JungFinite.FixedPointOfCompactDeflationIsCompact` | See §5. |
| 15 | **Lem 19.** `D` a domain, `r : D → D` with `r ∘ r = r ⊒ id` ⟹ `im(r)` is a domain. | 7.1 / 33 | `S+P` | `ScottDomains.IsClosure.domain_range` | See §6 — the reduced-strength `lem19` is **not** the row's evidence. |
| 16 | **Lem 20.** `D` a domain ⟹ `Fc(D)` is a cpo. | 7.1 / 33 | `S+P` | `ScottDomains.lem20` | `Skeleton/Section6b.lean:94`. Existential in the `CompletePartialOrder`, witness `Fc.completePartialOrder`, with a conjunct pinning the order to the pointwise one. |

**All ten Lemma 17 conjuncts are additionally checked as a single conjunction**
by `ClosureProperties.lemma17` (`ClosureProperties.lean:91`), so the count of ten
is kernel-checked rather than prose.

---

## 2. Theorem 16's second conjunct, for a reader who knows neither text

The paper's Theorem 16 is one sentence with two conjuncts. The first is proved.
**The second is false, and the development proves it false.**

*What the conjunct says.* `Fp(D)` is the set of finitary projections on `D`, a
subset of the function space `D → D`. "Embedding" is fixed by the paper in §3.1:
`g : D → E` is an embedding when there is a continuous `f : E → D` with
`f ∘ g = id` and `g ∘ f ⊑ id` — an *embedding–projection pair*. So the conjunct
asserts a continuous retraction `s : (D → D) → Fp(D)` of the inclusion, sending
each continuous `f` to a finitary projection below it. The paper's own sketch
names `s` explicitly (`f ↦ p_{N_f}`, "the remaining steps required to verify that
`f ↦ N_f` is a projection are straight-forward"), so this is the intended reading;
the alternative *order*-embedding reading is true by `Fp.le_def`'s `Iff.rfl` and
would leave the sketch nothing to prove.

*Why it is false.* `Fp.le_iff_fpBasis_subset_stableCompacts`
(`FinitaryProjectionEmbedding.lean:241`) is the exact criterion: for `p ∈ Fp(D)`
with basis `N = im(p) ∩ K(D)`, `p ⊑ f` **iff** `N ⊆ S_f`, where
`S_f = {x ∈ K(D) | x ⊑ f(x)}`. So a section exists exactly when the normal
subposets **contained in** `S_f` have a greatest member. The paper's sketch builds
the least normal set **containing** `S_f` — the opposite inclusion. The two agree
only when `S_f` is itself normal, which happens exactly when `f` is already a
finitary projection. No choice of `N_f` repairs it.

*The witness.* `TwoMub` is the five-element poset `{⊥, a, b, m₁, m₂}` with `a, b`
incomparable and `m₁, m₂` the two incomparable minimal upper bounds of `{a, b}`.
It is finite, hence a bifinite domain, and it is the smallest bifinite poset that
is not bounded complete. For the constant map `f = λx. m₁`, the projections below
`f` have two incomparable maximal elements and no greatest one.
`TwoMub.not_exists_monotone_projection` (line 497) refutes even a *monotone* `s`,
and `TwoMub.not_isEmbeddingProjectionPair` (line 511) phrases it in
`ScottHom.IsEmbeddingProjectionPair`. `thm16_first_conjunct` (line 360)
instantiates `thm16` at the same `TwoMub`, so the refutation isolates the second
conjunct at a `D` satisfying the hypothesis and the first conjunct.

*The repaired form.* `Section62.thm16_positive` (`Section62.lean:289`) proves the
conjunct under the named hypothesis `HasGreatestStableNormal α` — "for every
continuous `f`, the normal subposets of `K(D)` inside `S_f` have a greatest
member" — and its statement is the literal negation of
`not_exists_monotone_projection`, so the two together are a dichotomy.
`hasGreatestStableNormal_of_boundedComplete` puts every bounded complete domain on
the true side, and `thm16_positive_isEmbeddingProjectionPair` (line 420) upgrades
`s` to Scott continuous there.

**Ruling: `S≠`.** The paper's statement is not stated as such (it cannot be — it
is false); what is stated is a repaired form under an added hypothesis, together
with a kernel-checked refutation of the printed form. This is not `S+P`.

---

## 3. Lemma 17's `[BoundedComplete β]` — ruling

Measured hypotheses, conjunct by conjunct:

| # | Conjunct | Hypotheses beyond `IsBifinite` |
| -- | -------- | ------------------------------ |
| 1 | `→` (`lem17_fun`) | `[Domain α] [Domain β] [BoundedComplete β]` |
| 2 | `◦→` (`lem17_strictFun`) | `[Domain α] [Domain β] [BoundedComplete β]` |
| 3–7 | `×`, `⊗`, `+`, `⊕`, `()⊥` | `[Domain α] [Domain β]` only |
| 8–10 | `♮`, `♯`, `♭` | `[Domain α]` only |

**Ruling: rows 4 and 5 are `S≠`; rows 6–13 are `S+P`.**

The argument. `[Domain _]` on the operands is not an addition — the paper's
hypothesis is "bifinite **domains**", and `IsBifinite` in this development is the
basis condition alone (`IsPlotkinOrder (compacts α)`), so `[Domain α]` is the
other half of the paper's own word. `[BoundedComplete β]` is different in kind.
The paper's Lemma 17 does not state it, the paper's argument for the `→` conjunct
does not use it, and **§6 exists precisely to drop it**: Theorem 7 needed bounded
completeness of `E` to make `D → E` a domain, and §6's stated purpose is the class
on which the operators close without it. A theorem that reintroduces the
hypothesis §6 was written to remove does not state §6's claim for that conjunct.

The development's own docstring (`ClosureProperties.lean:54–58`) concedes the
point in the same words: "not by the paper's argument for them either… removing
this hypothesis is a real open item, not a formality." What the docstring does
*not* say, and what is measured here: the **combined** theorem
`ClosureProperties.lemma17` carries `[BoundedComplete β]` in its signature, so
all ten conjuncts as delivered by that one declaration inherit it. The eight
unaffected conjuncts are `S+P` only through their individual declarations, which
do not.

---

## 4. `IsBifinite` is the characterization, not the paper's definition

The paper's Definition (printed 29) is: `M` = the finitary projections with finite
image; `D` is **bifinite** if `M` is countable, directed and `⊔M = id`. The
development's `IsBifinite α` is `IsPlotkinOrder (compacts α)` — Theorem 14's
*clause 2*, minus "`D` is a domain", which is carried as the instance `[Domain α]`.

This is not a mismatch, because **Theorem 14 is proved**:
`Skeleton.Recovered.thm14 : IsBifiniteViaProjections α ↔ Domain α ∧ IsBifinite α`
(`Skeleton/Recovered.lean:265`, via `SFP.thm14_forward` and `SFP.thm14_converse`),
with `IsBifiniteViaProjections` (line 208) transcribing the paper's own sentence.
Every `S+P` row above that concludes `IsBifinite` under `[Domain _]` therefore
also delivers the paper's definitional form, by one application of `thm14`.
Recorded here so the orchestrator's spot-check does not have to rediscover it.

---

## 5. Theorem 18 — `S+H`, all three names

* **The statement**: `ScottDomains.thm18` (`Skeleton/Section6.lean:196`),
  `[Domain α] [Domain (ScottHom α α)] : IsBifinite α`. Its proof is `sorry` at
  line 197. Measured: this is the **only** `sorry` in the whole development —
  `grep -rn "^ *sorry|:= sorry|by sorry"` over `ScottDomains/` returns exactly one
  line, and the most recent build log (`logs/compile-20260808-105508.orchestrator.log`)
  reports `sorry decls: 1`.
* **The reduction**: `JungFinite.thm18_of_propertyM` (`JungFinite.lean:697`)
  proves the same conclusion from two hypotheses, `hcor` and `hm`.
  - `hcor : JungFinite.FixedPointOfCompactDeflationIsCompact α`
    (`JungFinite.lean:611`) — Jung's Corollary 1.36: a compact deflation's fixed
    points are compact. Not proved; carried as an explicit hypothesis, no `sorry`.
  - `hm` is property m at every finite set, and
    `JungNets.forall_hasCompleteMub_of_thm137` (`JungNets.lean:336`) supplies it
    from `JungNets.Thm137 α` (`JungNets.lean:308`) — Jung's Theorem 1.37, "a dcpo
    with continuous function space is bicomplete". Not proved; explicit hypothesis,
    no `sorry`.

**One gap worth reporting.** No declaration composes the two into
`Thm137 α → FixedPointOfCompactDeflationIsCompact α → IsBifinite α`. The
composition is one application modulo an argument reorder (`hm`'s two hypotheses
are `hvc, hvfin`; `forall_hasCompleteMub_of_thm137` produces them as `hv, hvA`),
but the "Theorem 18 modulo two named propositions" claim is presently a fact about
two declarations read together, not a kernel-checked one. Cheap to close.

---

## 6. Lemma 19 — ruling on the reduced-strength form

`Skeleton/Section6.lean:253` holds

    theorem lem19 (r : ScottHom α α) (_hr : IsClosure r) :
        ∃ _ : CompletePartialOrder ↥(Set.range ⇑r), True

which is weaker than the paper's Lemma 19 in **both** directions: the conclusion
is a **cpo**, not a domain (no algebraicity, no countable basis), and the
hypothesis `[Domain α]` — which the paper states — is absent, because cpo-ness of
the image needs nothing about `D`.

`ScottDomains.IsClosure.domain_range` (`FinitaryProjectionPoset.lean:282`) is the
paper's statement:

    theorem IsClosure.domain_range [Domain α] (hr : IsClosure r) :
        @Domain _ (IsClosure.rangeCompletePartialOrder hr)

built from `IsClosure.isAlgebraic_range` (line 238) and
`IsClosure.countable_compacts_range` (line 270), the latter via
`IsClosure.compacts_range_subset` — which is the paper's own one-line proof
sketch, `{r(k) | k ∈ K(D)}` as the basis.

**Ruling: Lemma 19 is `S+P`, and the declaration is `IsClosure.domain_range`, not
`lem19`.** r0038's agent3 flagged this across an area boundary and was right: the
`Skeleton` file's `lem19` is a strictly weaker duplicate. It is not a coverage gap
— the full-strength statement exists and is proved — but any reader who takes
`lem19` as Lemma 19 is reading a weaker theorem. Note also that Lemma 20 *cannot*
be stated without the full-strength form: `Fc(D)` is defined by "`im(r)` is a
domain", so `Fc.completePartialOrder` needs `domain_range` to place a supremum of
closures back inside `Fc(D)`.

---

## 7. The unnumbered prose claims of §6 (and §7.1's Lemma 19/20 neighbourhood)

Definitions are excluded, per the plan; they are listed separately in §8.
Bibliographic sentences (Plotkin [Plo76] "SFP-objects", "bifinite" due to Paul
Taylor, "strongly algebraic" [Smy83a, Gun86], "profinite" [Gun87], "the theorem is
due to Smyth", "[Gun86] for bounded complete domains") are not properties and are
not counted.

| # | Claim | printed p. | Label | Declaration / evidence |
| -- | ----- | ---------- | ----- | ---------------------- |
| p1 | Of the operators discussed so far, **only** the convex powerdomain `(·)♮` fails to take bounded complete domains to bounded complete domains. | 29 | `P` | Asserted in the development's own prose at `Powerdomain/BoundedComplete.lean:28–31`, `Dyadic.lean:78`, `Colimit.lean:1020`. Lemma 13 supplies the positive half for `♯`/`♭` (agent3's rows); the negative half is nowhere under the kernel. |
| p2 | `(T × T)♮` is not bounded complete: `u′, v′` are minimal upper bounds for `{u, v}` under `⊢♮`, so no least upper bound exists. | 29 | **`N`** | Three greps in §9. |
| p3 | `p : D → D` a finitary projection with `im(p)` finite ⟹ `im(p) ⊆ K(D)`. | 30 | `S+P` | `SFP.range_subset_compacts_of_finite` (`SFP.lean:160`). Proved for `IsProjection`, weaker than "finitary" — a strengthening. |
| p4 | With `M` directed and `⊔M = id`, `D` is a domain with `⋃{im(p) | p ∈ M}` as its basis. | 30 | `S+P` | `SFP.thm14_forward` (`SFP.lean:259`), conclusion `Domain α ∧ IsBifinite α`. Caveat: the basis identification `K(D) ⊆ ⋃{im(p)}` appears only as unnamed `have` steps (`hfix`, `hKcount`) inside that proof, not as a declaration. |
| p5 | **Fact 1.** Every finite subset of a Plotkin order has a complete set of minimal upper bounds. | 30 | `S+P` | `MinimalUpperBounds.isPlotkinOrder_iff_mubClosure` (line 369), forward direction, first conjunct; the work is `hasCompleteMub_of_isNormalIn` (line 329). |
| p6 | Figure 3a's configuration is ruled out — its closed-circle pair has no complete set of minimal upper bounds. | 30–31 | `P` | Described in the development's own prose at `MinimalUpperBounds.lean:35–37` and in `exists_of_not_isPlotkinOrder`'s docstring (line 404), and at `ContinuousConstruction.lean:70`. The drawn poset is never built, so no claim about it is kernel-checked. |
| p7 | **Fact 2.** Every finite subset has a *finite* complete set of minimal upper bounds. | 30 | `S+P` | `IsPlotkinOrder.minimalUpperBounds_finite` (`MinimalUpperBounds.lean:427`). |
| p8 | Figure 3b's configuration is ruled out — complete set of mubs, but infinite. | 30–31 | `P` | Same evidence as p6; `ContinuousConstruction.lean:83`. |
| p9a | If `u ⊆ N ◁ A` then `U(u) ⊆ N`, hence `Uⁿ(u) ⊆ N` for each `n`. | 31 | `S+P` | `mubClosure_subset_of_isNormalIn` (`MinimalUpperBounds.lean:345`), by induction on `n`. |
| p9b | If `N` is finite there is an `n` with `Uⁿ(u) = Uⁿ⁺¹(u)`. | 31 | `S≠` | Closest declaration `JungFinite.mubDiff_nonempty` (`JungFinite.lean:460`). It differs twice: its hypothesis is "every stage `Uⁿ(u)` is finite", not the paper's "`Uⁿ(u) ⊆ N` with `N` finite"; and its conclusion is the contrapositive per-difference nonemptiness, not the existence of a stabilizing index. The development reaches fact 3 by the shorter route (p9a plus finiteness of `N`) and never takes this step. |
| p10 | **Fact 3.** For each finite `u ⊆ A`, `U^∞(u) = ⋃ₙ Uⁿ(u)` is finite. | 31 | `S+P` | `isPlotkinOrder_iff_mubClosure`, forward direction, second conjunct. |
| p11 | Figure 3c's configuration is ruled out — `U^∞(u)` is infinite there. | 31 | `P` | Same evidence as p6/p8; `MinimalUpperBounds.lean:407–409`. |
| p12 | Finite complete sets of minimal upper bounds for finite subsets are **not sufficient** to characterize the Plotkin orders. | 31 | **`N`** | Three greps in §9. `isPlotkinOrder_iff_mubClosure` proves facts 1+3 *are* sufficient; the non-implication from 1+2 alone needs a witness, and none is built. |
| p13 | (Thm 16 sketch) For continuous `f`, there is a **least** `N_f` with `S_f ⊆ N_f ◁ K(D)`. | 32 | `S+P` | `normalClosure` (`FinitaryProjectionPoset.lean:509`) with `subset_normalClosure`, `normalClosure_subset`, `normalClosure_isNormalIn` (leastness and normality, the latter over a Plotkin order via `isNormalIn_sInter`), and `normalClosure_finite`. |
| p14 | (Thm 16 sketch) If `f` is a finitary projection then `N_f = im(f) ∩ K(D)` and `f = p_{N_f}`. | 32 | `S+P` | `stableCompacts_val` (`FinitaryProjectionEmbedding.lean:250`) gives `S_f = fpBasis p`; `normalHom_fpBasis` (`FinitaryProjectionPoset.lean:567`) gives `f = p_{N_f}`. The sketch's round-trip half is correct and checked; it is the *other* half that fails (§2). |
| p15a | (Lem 17 sketch, `→`) `Θ(q,p)(f) = q ∘ f ∘ p` is a finitary projection on `D → E`, with finite image when `p` and `q` have finite images. | 32 | `S+P` | `compHom` (`Skeleton/Lemma17.lean:344`), `scottContinuous_compFun` (328), `isProjection_compHom` (353), `finite_range_compHom` (365). |
| p15b | (Lem 17 sketch, `→`) `⊔M = id` for `M = {Θ(q,p) | p, q finitary with finite image}`. | 32 | **`N`** | Three greps in §9. The development proves `lem17_fun` by the Plotkin-order route on the basis and never forms this `M`. |
| p16 | (Lem 17 sketch, `♮`) `M = {p♮ | p ∈ Fp(D), im(p) finite}` is directed with `⊔M = id`, and its members are finitary projections with finite images. | 32 | **`N`** | Three greps in §9. There is **no action of a map on any powerdomain** in the development, so `p♮` does not exist as a term; `lem17_plotkin` argues on the basis instead. |
| p17 | (Lem 19 proof) `{r(x) | x ∈ K(D)}` forms a basis for `im(r)`. | 33 | `S+P` | `IsClosure.isAlgebraic_range` (`FinitaryProjectionPoset.lean:238`) and `IsClosure.compacts_range_subset` (258). |

Two sentences are the paper's own **announcements** of numbered results and are
deliberately **not counted** as separate properties, to avoid double counting:

* "They are the *largest* class of domains which are closed under the operators
  listed in the Lemma. In fact, there is the following:" — the "in fact" makes
  Theorem 18 the precise form of this sentence. Row 14's `S+H` covers it. (For the
  record, no declaration states maximality in any form: `grep -rn "largest|maximality|cartesian closed"`
  over `ScottDomains/` returns only bibliographic titles and one unrelated hit at
  `Universality.lean:489`.)
* "In the event that `D` is a domain, the requirement that `im(r)` be a domain is
  unnecessary because we have the following:" — the announcement of Lemma 19,
  row 15.

**Prose-claim count for my range: 17 claims, 19 labelled rows.** The seventeen
are p1–p17 as the paper states them; p9 and p15 are each split into two rows
because their two halves get different labels.

---

## 8. Definitions in range (not counted, all present)

| # | Paper's definition | printed p. | Lean |
| -- | ------------------ | ---------- | ---- |
| 1 | bifinite (`M` countable, directed, `⊔M = id`) | 29 | `Skeleton.Recovered.IsBifiniteViaProjections`, with `finiteImageProjections` for `M` |
| 2 | Plotkin order | 30 | `ScottDomains.IsPlotkinOrder` (`Bifinite.lean:38`) |
| 3 | minimal upper bound; complete set of minimal upper bounds | 30 | `minimalUpperBounds`, `HasCompleteMub` (`MinimalUpperBounds.lean`) |
| 4 | `U(u)`, `Uⁿ(u)`, `U^∞(u)` | 31 | `mubStep`, `mubIter`, `mubClosure` |
| 5 | closure `r : D → E` | 33 | `ScottDomains.IsClosure` (`Skeleton/Section6.lean:52`) |
| 6 | finitary closure; `E` is a closure of `D`; `Fc(D)` | 33 | `IsFinitaryClosure`, `Fc` (`FinitaryProjectionPoset.lean:104, 111`) |

---

## 9. The `N` rows, with three greps each

**p2 — `(T × T)♮` is not bounded complete.**

1. `grep -rn "not bounded complete\|not_boundedComplete\|notBoundedComplete" ScottDomains/` — five hits, all prose (`Powerdomain/BoundedComplete.lean:29,60`, `ContinuousConstruction.lean:6`, `Section62.lean:196`, `FinitaryProjectionEmbedding.lean:264`). The `not_boundedComplete_hoare/_smyth/_plotkin` triple named at line 60 was **retired** in r0032 and concerned `P N`, not `T × T`.
2. `grep -rn "T × T\|TxT\|convex powerdomain" ScottDomains/` — ten hits, every one a docstring; no term of type `T × T` and no statement about `(T × T)♮`.
3. `grep -rln "Bool × Bool\|prodBool\|TwoTwo\|flatBool" ScottDomains/` — one file, `JungSFP.lean`, and a follow-up `grep -n` there returns nothing (the hit was the regex `TT\b` matching inside a word). No two-by-two flat witness type exists.

Also checked: `grep -rn "BoundedComplete\|boundedComplete" Powerdomain/Plotkin.lean` — **zero** hits. The convex powerdomain module says nothing about bounded completeness at all.

**p12 — finite complete sets of mubs are not sufficient.**

1. `grep -rn "not sufficient\|not a sufficient\|insufficient" ScottDomains/` — three hits; the only relevant one is `MinimalUpperBounds.lean:23`, inside a **verbatim block quotation of the paper**, which under §0's rule is not the development asserting it.
2. `grep -rn "¬ IsPlotkinOrder\|Not (IsPlotkinOrder" ScottDomains/` — one hit, `exists_of_not_isPlotkinOrder` (`MinimalUpperBounds.lean:413`), which is the Figure 3 dichotomy (a *consequence* of failing the Plotkin condition), not a witness poset satisfying facts 1+2 and failing fact 3.
3. `grep -rn "Figure 3\|Fig3\|fig3" ScottDomains/` — 24 hits, all docstrings. No concrete poset is constructed for any of 3a, 3b, 3c.

**p15b — `⊔M = id` for `M = {Θ(q,p)}`.**

1. `grep -rn "IsLUB.*ScottHom.id\|IsLUB.*idHom\|sSup.*ScottHom.id" ScottDomains/` — the only `IsLUB … ScottHom.id` statements are about `finiteImageProjections α`, the **full** family on a single cpo (`SFP.lean:263, 454, 475`; `Skeleton/Recovered.lean:211`), never about a family of `compHom`s on `D → E`.
2. `grep -rn "compHom\|compFun" ScottDomains/` — ~90 hits across seven files; `isProjection_compHom`, `finite_range_compHom`, `compHom_mono`, `isLUB_compHom_of_isLUB` (a *pointwise-in-`f`* continuity statement, not `⊔M = id`). No declaration forms the set `{compHom p q | …}`.
3. `grep -rn "Theta\|theta\|Θ" ScottDomains/` — eleven hits; ten are §7.2's unrelated `bigTheta` in `Combinator.lean`, one is the `Θ` in `Skeleton/Lemma17.lean:243`'s docstring, which says in the development's own words that the `⊔M = id` route "is not needed" because `IsBifinite` is *defined* as the Plotkin condition.

**p16 — `p♮` and its `M`.**

1. `grep -rn "plotkinMap\|powerdomainMap\|Powerdomain.map\|map_powerdomain\|p♮\|liftProjection" ScottDomains/` — five hits, all docstrings quoting the paper (`ClosureProperties/Powerdomain.lean:17,33,327`; `PRepresentable.lean:53`; `LemThirty.lean:20`). No definition of `p♮`.
2. `grep -rn "IsFinitaryProjection.*Powerdomain\|Fp (.*Powerdomain\|ScottHom (.*Powerdomain" ScottDomains/` — **zero** hits. No projection on any powerdomain is ever formed.
3. `grep -rn "IsLUB.*ScottHom.id\|sSup.*ScottHom.id" ScottDomains/` — as above, nothing over a powerdomain carrier.

`ClosureProperties/Powerdomain.lean:21–24` states the substitution in the
development's own prose: "The paper's argument is carried out here on the **basis**
rather than on the function space." The conclusion (`lem17_plotkin`) is `S+P`;
the *sketch step* p16 is not stated.

---

## 10. Per-label totals

Sixteen numbered conjuncts and nineteen prose rows (seventeen prose claims, two
of them split), thirty-five labelled rows in all.

| # | Label | Numbered (16) | Prose (19) | Total (35) |
| -- | ----- | ------------: | ---------: | ---------: |
| 1 | `S+P` | 12 | 10 | **22** |
| 2 | `S+H` | 1 | 0 | **1** |
| 3 | `S≠` | 3 | 1 | **4** |
| 4 | `P` | 0 | 4 | **4** |
| 5 | `N` | 0 | 4 | **4** |

**Every numbered conjunct of §6 is stated in some form. There is no `N` among the
sixteen.** All four `N` rows are prose, and three of the four (p15b, p16, and half
of p9b's neighbourhood) are *proof-sketch steps the development deliberately does
not take*, because it works from Theorem 14's characterization instead of the
paper's definition. Only two `N` rows are claims the paper makes in its own voice:

* **p2** — `(T × T)♮` is not bounded complete. This is §6's opening motivation and
  the reason the section exists. It is cheap to state: `T × T` is a four-element
  finite poset and the four sets `u, v, u′, v′` are printed in full on page 29.
* **p12** — finite complete sets of minimal upper bounds do not characterize the
  Plotkin orders. This needs the Figure 3c poset, which no round has built.

The four `P` rows are p1 (the "only the convex powerdomain" sentence) and the
three Figure 3 configuration claims, p6/p8/p11 — the same figures r0039 worked on.

---

## 11. Re-derived counts against `docs/PropertiesVsTheorems.md` §1

| # | Result | My count from the PDF | `PropertiesVsTheorems.md` §1 | Moved? |
| -- | ------ | --------------------: | ---------------------------: | ------ |
| 1 | Prop 15 | 1 | 1 (inside row 13's 4) | no |
| 2 | Thm 16 | 2 | 2 (row 14) | no |
| 3 | Lem 17 | **10** | 10 (row 15) | no — re-confirmed at 600 dpi |
| 4 | Thm 18 | 1 | 1 (inside row 13) | no |
| 5 | Lem 19 | 1 | 1 (inside row 13) | no |
| 6 | Lem 20 | 1 | 1 (inside row 13) | no |
| — | **numbered total, my range** | **16** | **16** | no |

**No numbered conjunct count moved.** Two corrections to the same table:

1. **Row 13's section is wrong.** It lists "Prop 15, Thm 18, Lem 19, Lem 20" under
   § **6**. Lemma 19 and Lemma 20 are in § **7.1**, printed page 33. `PaperInventory.md`
   carries the same error.
2. **The prose-claim figure is far too low.** Row 20 records **12** unnumbered
   prose claims for the *whole paper* (`PaperInventory.md` row 3 revises it to 13).
   §6 plus §7.1's Lemma 19/20 neighbourhood alone yields **17 claims**. Combined with
   agent3's 17 in §5, the paper-wide figure is out by an order of magnitude and the
   99/100 property total should not be quoted until it is re-derived section by
   section.

---

## 12. Measurement discipline

No `.lean` file was edited. `git status --short` is empty in this worktree. The
last build on record (`ScottDomains/logs/compile-20260808-105508.orchestrator.log`)
is 1229 jobs, exit status 0, `lean diagnostics: 0`, `lake errors: 0`,
`sorry decls: 1`, `other warnings: 0`. That is the state at the end of this round
as at the start.
