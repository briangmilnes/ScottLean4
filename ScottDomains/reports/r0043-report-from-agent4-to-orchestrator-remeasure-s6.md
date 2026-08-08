---
round: r0043
from: agent4
to: orchestrator
subject: remeasure-s6
date: 2026-0808-16:39
started: 2026-0808-16:31
finished: 2026-0808-16:39
related:
  - plans/r0043-plan-from-orchestrator-to-orchestrator-remeasure-unstated.md
  - reports/r0040-report-from-agent4-to-orchestrator-property-coverage-s6.md
---

# §6 re-measurement: the four `N` rows, re-checked against the tree

r0040 labelled thirty-five rows in §6 (plus §7.1's Lemma 19/20 neighbourhood) and
found four `N`. This round re-checks **those four only**. The thirty-one rows that
were not `N` were not re-surveyed; one improvement noticed in passing is recorded
in §6, and no regression was seen.

## The result in one table

| # | r0040 row | Paper's sentence | printed p. | r0040 | now | Evidence |
| -- | -------- | ---------------- | ---------- | ----- | --- | -------- |
| 1 | p2 | `(T × T)♮` is not bounded complete; `u′, v′` are minimal upper bounds for `{u, v}` under `⊢♮` | 29 | `N` | **`S+P`** | `ScottDomains.Flat.not_boundedComplete_plotkin_TT`, `FlatSection6.lean:316` |
| 2 | p12 | Finite complete sets of minimal upper bounds for finite subsets are **not sufficient** to characterize the Plotkin orders | 31 | `N` | **`N`** | three greps, §3 |
| 3 | p15b | (Lem 17 sketch, `→`) `⊔M = id` for `M = {Θ(q,p)}` | 32 | `N` | **`N`** | three greps, §4 |
| 4 | p16 | (Lem 17 sketch, `♮`) `M = {p♮ | p ∈ Fp(D), im(p) finite}` is directed with `⊔M = id`, and its members are finitary projections with finite images | 32 | `N` | **`S≠`** | `PowerdomainMap.isProjection_plotkin`, `PowerdomainMap.lean:493` — the sentence's subordinate clause only; §5 |

**Two of four moved out of `N`; one of those is `S+P`. Two remain `N`.**

---

## 1. Row 1 (p2) — the ruling, in full

### What the paper says, read from the PDF this round

`pdftotext -f 30 -l 30` on `papers/Gunter Scott 1990.pdf` (physical 30 = printed
29). The extraction, ligatures unrepaired:

> Of the operators that we have discussed so far, only the convex powerdomain
> `()♮` does not take bounded complete domains to bounded complete domains. To
> see this in a simple example, consider the finite poset `T × T` and the
> following elements of `Pf(T × T)`:
>
>     u  = {⟨⊥, true⟩, ⟨⊥, false⟩}
>     v  = {⟨true, ⊥⟩, ⟨false, ⊥⟩}
>     u′ = {⟨true, true⟩, ⟨false, false⟩}
>     v′ = {⟨true, false⟩, ⟨false, true⟩}
>
> It is not hard to see that `u′` and `v′` are minimal upper bounds for `{u, v}`
> with respect to the ordering `⊢♮`. Hence no least upper bound for `{u, u′}`
> exists and `(T × T)♮` is therefore not bounded complete.

### The declaration

`ScottDomains.Flat.not_boundedComplete_plotkin_TT` (`FlatSection6.lean:316`):

    theorem not_boundedComplete_plotkin_TT : ¬ BoundedComplete (Plotkin.Powerdomain TT)

The carriers are the paper's own, checked rather than assumed:

* `TT := Truth × Truth` and `Truth := Flat Bool` (`Flat.lean:329`), a three-element
  flat cpo — `truth_forall_eq` (line 348) proves `a = ⊥ ∨ a = up true ∨ a = up false`.
  So `TT` is the paper's `T × T`.
* `Plotkin.Powerdomain D := IdealCompletion (Plotkin.FinCompacts D)`
  (`Powerdomain/Plotkin.lean:256`), the ideal completion of the Egli–Milner
  pre-order on **nonempty** finite subsets of `K(D)` — the paper's `D♮`.
* `BoundedComplete` (`Domain.lean:168`) is the class whose consequence is
  `exists_isLUB_of_bddAbove` (line 181), and that is exactly how line 319 spends it.
* `setU`, `setV`, `setU'`, `setV'` (lines 94–106) are the four printed sets, each
  built by `Plotkin.FinCompacts.pair` from `kp a b`, the compactness of the pair
  supplied by `isCompactElement_prod_iff`.

Supporting the row, and stated separately because the paper asserts them:
`setU'_minimal` (212), `setV'_minimal` (238) — `u′` and `v′` are minimal upper
bounds of `{u, v}` — and `not_setU'_le_setV'` (267), their incomparability, which
is what makes them *two*.

### Judgement 1: the printed `{u, u′}` is a typo for `{u, v}`

Confirmed independently of agent1, and the development supplies the refutation of
the printed reading rather than merely asserting it: `setU_le_setU'`
(`FlatSection6.lean:113`) is `u ⊑ u′`. A pair `{u, u′}` with `u ⊑ u′` has `u′` as
its least upper bound, so the printed sentence is false as printed. The preceding
sentence fixes the intended pair, `{u, v}`, and `not_exists_isLUB` (292) is stated
for `{↓u, ↓v}`. This is the paper's third printed defect this project has measured.

### Judgement 2: the paper's argument, and whether it transfers

agent1 recorded that the paper's argument — two minimal upper bounds, hence no
least one — "does not transfer" from the pre-order to the ideal completion. That
is too strong, and the file itself shows why. The precise position:

* **In the pre-order the paper's inference is valid.** If `l` were a least upper
  bound of `{u, v}`, then `l ⊑ u′` and `l` is an upper bound, so minimality of
  `u′` gives `u′ ⊑ l`; likewise `v′ ⊑ l ⊑ v′`; so `u′` and `v′` are equivalent,
  contradicting `not_setU'_le_setV'`.
* **One step is left implicit in passing to `(T × T)♮`.** Bounded completeness is
  a property of the ideal completion, where a least upper bound of `{↓u, ↓v}` is
  an ideal `I`, not a finite set. The missing step is that `I` is directed and so
  contains a single `w` above both `u` and `v` — equivalently, that a join of two
  compact elements is itself compact and hence principal. `not_exists_isLUB` (292)
  takes exactly that step, `I.directed setU hu setV hv` at line 309.
* **Both arguments are formalized.** Having produced `w` with `u, v ⊑ w ⊑ u′` and
  `w ⊑ v′`, the file finishes with `no_common_refinement` (192), which needs no
  minimality: one member of `w` has both coordinates defined (`exists_up_of_mem`),
  equal from `w ⊑ u′` and unequal from `w ⊑ v′`. The paper's own finish would
  compose in one line from `setU'_minimal`, `setV'_minimal` and
  `not_setU'_le_setV'`, all three of which are present and proved.

**Ruling: `S+P`.** The label measures whether the paper's *claim* is stated and
kernel-checked, not whether the proof follows the paper's *route*. The claim is
stated verbatim at the paper's own witness and proved; the paper's supporting
minimality claim is stated and proved beside it; and the paper's route is present
in ingredients, wanting only a one-line composition. Nothing about the row is
weaker than the paper, and the implicit ideal-completion step is supplied rather
than assumed — a strengthening.

---

## 2. Row 1's neighbour, p1, is no longer prose-only

Not one of my four, so not relabelled here, but the orchestrator should know the
adjacent row moved. r0040 labelled p1 — "only the convex powerdomain `(·)♮` fails
to take bounded complete domains to bounded complete domains" — as `P`, asserted
in the development's prose with "the negative half nowhere under the kernel."
`FlatSection6.convex_does_not_preserve_boundedComplete` (line 325) is now that
negative half:

    Domain TT ∧ BoundedComplete TT ∧ ¬ BoundedComplete (Plotkin.Powerdomain TT)

with the two positive instances `instDomainTT := PowerdomainRep.domain_prod` and
`instBoundedCompleteTT := lem10_prod`. Paired with Lemma 13 for `♯` and `♭`
(agent3's rows), the "only" is now kernel-checked at both ends. I do not assign
p1 a new label — it is outside this round's scope and outside my `N` list — but
it is a candidate for `S+P` whenever it is next measured.

---

## 3. Row 2 (p12) stays `N` — three greps

The claim needs a poset satisfying facts 1 and 2 (every finite subset has a
*finite* complete set of minimal upper bounds) and failing fact 3 (`U^∞(u)`
infinite) — the Figure 3c configuration.

1. `grep -rn "not sufficient\|not a sufficient\|insufficient\|do not characterize\|does not characterize"` over
   `ScottDomains/ScottDomains/` — three hits. `MinimalUpperBounds.lean:23` is
   inside a verbatim block quotation of the paper, which under r0040's rule is not
   the development asserting the claim. `CombinatorRep.lean:74` and
   `CoalescedSum.lean:247` are unrelated uses of the phrase.
2. `grep -rn "¬ IsPlotkinOrder\|Not (IsPlotkinOrder\|not_isPlotkinOrder\|IsPlotkinOrder.*→ False"` — one
   hit, `MinimalUpperBounds.lean:413`'s `exists_of_not_isPlotkinOrder`, the Figure 3
   dichotomy. It is a consequence of failing the Plotkin condition, not a witness
   poset. Unchanged from r0040.
3. `grep -rn "Figure 3\|Fig3\|fig3\|Figure3"` — 24 hits across five files
   (`MinimalUpperBounds` 6, `ContinuousConstruction` 6, `Section62` 7,
   `Skeleton/Section6` 4, `FinitaryProjectionEmbedding` 1), every one a docstring.
   No concrete poset is constructed for 3a, 3b or 3c.

**Did the flat cpo work supply one?** No.
`grep -rn "IsPlotkinOrder\|mubClosure\|HasCompleteMub"` over `Flat.lean`,
`FlatOmega.lean` and `FlatPowerdomain.lean` returns **zero** hits — the flat
modules carry no Plotkin-order content at all. Nor could they: a flat poset is
trivially a Plotkin order, since distinct non-bottom elements are unbounded.

**One place worth the orchestrator's attention.** `Section62.lean:162` lists as
step 4 of the Theorem 18 route "property M ⟹ `U^∞(A)` finite (Figure 3c), Jung
Lemma 2.2", marked "ingredients present; two steps proved below". Read naively
that is the *converse* of p12: it would make facts 1+2 imply fact 3 and refute the
paper's sentence. It does not, and no contradiction stands: what is proved
(`apply_eq_self_of_mem_mubIter` at line 460, `apply_eq_self_of_mem_mubClosure` at
477) is only that a deflation fixing `u` fixes the whole mub-closure, and
`PropertyM.isBifinite_of_mubClosure_finite` (`PropertyM.lean:969`) takes
mub-closure finiteness as an explicit **hypothesis**. Neither the implication nor
its refutation is stated.

---

## 4. Row 3 (p15b) stays `N` — three greps

1. `grep -rn "compHom\|compFun"` — eight files. In `Skeleton/Lemma17.lean` the
   operator itself is present and proved: `compFun` (317), `compHom` (344),
   `isProjection_compHom` (353), `finite_range_compHom` (365) — that is p15a,
   already `S+P` in r0040 and unchanged. **No declaration forms the set
   `{compHom p q | p, q finitary with finite image}`**, and no `IsLUB` or
   `DirectedOn` statement in the file mentions `compHom`; the `IsLUB`/`DirectedOn`
   hits at lines 41–170 are about products and lifts, and line 279's is inside the
   proof of `exists_greatest_of_finite_directedOn`.
2. `grep -rn "IsLUB.*ScottHom.id\|IsLUB.*idHom\|sSup.*ScottHom.id\|IsLUB.*(id\b"` — twelve
   hits in six files. Six are genuine `IsLUB … id` statements, and every one is over
   a family on a **single** cpo, never over a family of `compHom`s on `D → E`:
   `SFP.lean:263, 454, 475` and `Skeleton/Recovered.lean:211` are
   `finiteImageProjections α`, `JungCor136.lean:307` is `extSet e`,
   `JungBicomplete.lean:707` is `wayBelowSet id`. The other six are a docstring
   table row (`SFP.lean:37`, `Skeleton/Recovered.lean:205`) and four
   `sSup (insert ScottHom.id …)` terms building `Fc`-suprema
   (`RecursiveDomain.lean:289, 300`, `FinitaryProjectionPoset.lean:351, 361`).
3. `grep -rn "Theta\|Θ"` — ten hits, **all** in `Combinator.lean` (§7.2's
   unrelated `bigTheta`). The `Θ` r0040 found in `Skeleton/Lemma17.lean:243`'s
   docstring is gone: that docstring now writes the operator as `(q, p)(f) = q ∘ f ∘ p`
   and still says, in the development's own prose, that "with `IsBifinite`
   *defined* as the Plotkin condition on the basis, the correspondence is not
   needed."

**This is a deliberate route, not a gap.** The last sentence is the development
declaring that it does not take this step, having reached `lem17_fun` from
Theorem 14's characterization instead. Under r0040's rule a docstring is not the
development asserting a claim — and here it asserts the *opposite*, that the claim
is unnecessary — so the row is not even `P`.

---

## 5. Row 4 (p16) moves `N → S≠` — `p♮` now exists

r0040's finding was categorical: "there is **no action of a map on any
powerdomain** in the development, so `p♮` does not exist as a term." That is no
longer true. `PowerdomainMap.lean` (r0041) constructs it.

### What exists now

| # | Declaration | Line | Statement |
| -- | ---------- | ---: | --------- |
| 1 | `PowerdomainMap.plotkin` | 460 | `f♮ : D♮ → E♮`, a `def`, as `map f = ext({\|·\|} ∘ f)` |
| 2 | `PowerdomainMap.thm_map_plotkin` | 464 | §5.3's sentence: `∃!` homomorphism making the naturality square commute |
| 3 | `PowerdomainMap.plotkin_id` | 483 | `(id)♮ = id` |
| 4 | `PowerdomainMap.plotkin_comp` | 487 | `(g ∘ f)♮ = g♮ ∘ f♮` |
| 5 | `PowerdomainMap.isProjection_plotkin` | 493 | `p` a projection ⟹ `p♮` a `ScottHom.IsProjection` on `Plotkin.Powerdomain D` |

Row 5 is the one p16 bears on. It is proved from the two functor laws with no
appeal to compacts: `map_comp` plus `p ∘ p = p` gives idempotence, `map_le_map`
plus `map_id` gives `p♮ ⊑ id`.

### What p16 asserts, conjunct by conjunct

| # | Conjunct | Stated? |
| -- | -------- | ------- |
| 1 | the members of `M` are **projections** | **yes** — `isProjection_plotkin` |
| 2 | the members of `M` have **finite image** | no |
| 3 | `M` is **directed** | no |
| 4 | `⊔M = id` | no |

Conjuncts 2–4 measured by two greps.
`grep -n "Set.Finite (Set.range\|finite_range\|Finite.*range.*plotkin\|IsFinitaryProjection"` over
`PowerdomainMap.lean`, `PowerdomainMapRep.lean` and `ClosureProperties/Powerdomain.lean`
returns **zero** hits — nothing about the finiteness of `im(p♮)`.
`grep -rn "ScottHom (Plotkin.Powerdomain\|Fp (Plotkin.Powerdomain\|finiteImageProjections (Plotkin"`
returns the single hit at `PowerdomainMap.lean:497`, which is `isProjection_plotkin`'s
own type ascription; no set of projections over a powerdomain carrier is ever
formed, so neither directedness nor `⊔M = id` can be stated of one.

**Ruling: `S≠`, the same shape r0040 gave p9b.** The closest declaration exists and
is kernel-checked, and it differs from the paper's sentence by proving its
subordinate clause and omitting its principal one. The row's central content —
`M` directed with `⊔M = id` — is still not stated, and the orchestrator should not
read this row as coverage of the sketch.

**Why the sketch is still not needed.** `lem17_plotkin`
(`ClosureProperties/Powerdomain.lean:328`) proves `IsBifinite (Plotkin.Powerdomain D)`
from the basis, and `Skeleton.Recovered.thm14` (line 265) converts that to
`IsBifiniteViaProjections (Plotkin.Powerdomain D)` — which is precisely "the
finite-image projections on `D♮` are countable, directed, with `⊔ = id`"
(`finiteImageProjections`, line 199; the definition at line 208). So the paper's
*conclusion about `D♮`* is reachable in one application. What the paper's sketch
adds, and what remains unstated, is that the particular family `{p♮ | p ∈ Fp(D),
im(p) finite}` is such a family. r0040's judgement that this is a deliberately
skipped proof-sketch step, not a coverage gap, therefore still holds — for p15b
and for p16 alike.

---

## 6. One improvement in a non-`N` row

r0040 row 14, **Theorem 18**, was `S+H`: `ScottDomains.thm18`
(`Skeleton/Section6.lean:196`) was `sorry`, with the content carried by
`JungFinite.thm18_of_propertyM` under two open hypotheses. It is now proved
outright at `Skeleton/Section6.lean:218`:

    theorem thm18 [Domain α] [Domain (ScottHom α α)] : IsBifinite α :=
      PropertyM.thm18_of_cor136 JungCor136.fixedPointOfCompactDeflationIsCompact

That is `S+H → S+P`, and it also closes the r0040 §5 gap — no declaration then
composed the two named propositions into the conclusion — by removing one of them
entirely. **No regression was observed in any of the thirty-one non-`N` rows I
happened to touch.**

---

## 7. Counts, and the invariance check

No `.lean` file was edited this round. `git status --short` was empty at the start.

| # | Metric | r0040 | now | source |
| -- | ----- | ----: | --: | ------ |
| 1 | modules | 72 | **100** | `scripts/counts.sh` |
| 2 | lines | 27892 | **37300** | `scripts/counts.sh` |
| 3 | theorem-ish declarations | 1298 | **1773** | `scripts/counts.sh` |
| 4 | `sorry` | 1 | **0** | `scripts/counts.sh`; 0 in 0 files |
| 5 | jobs / errors / warnings | 1229 / 0 / 0 | **1339 / 0 / 0** | `logs/compile-20260808-145359.orchestrator.log` |

The `sorry` count is confirmed twice: `counts.sh` reports `0 in 0 file(s)`, and
`grep -rn "sorry"` over `ScottDomains/ScottDomains/` returns 38 lines across 30
files, every one inside a docstring or comment discussing the absence of `sorry`
or the axiom `sorryAx`. Not one is a `sorry` term. The numbered-result
count is unchanged at 25 of 29 — this round states nothing new and retracts nothing.

## 8. Per-label movement, my four rows

| # | Label | r0040 | now |
| -- | ---- | ----: | --: |
| 1 | `S+P` | 0 | **1** (p2) |
| 2 | `S≠` | 0 | **1** (p16) |
| 3 | `N` | 4 | **2** (p12, p15b) |

Of my four previously-`N` rows, **two are now stated** — one fully and provably
(p2, `not_boundedComplete_plotkin_TT`), one only in its subordinate clause (p16,
`isProjection_plotkin`) — and **two remain `N`**. Both survivors are proof-sketch
steps or a counterexample the development has consistently chosen not to build:
p15b because Theorem 14's characterization makes it unnecessary, p12 because no
round has constructed a Figure 3c poset.
