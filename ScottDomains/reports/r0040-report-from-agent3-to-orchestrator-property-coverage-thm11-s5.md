---
round: r0040
from: agent3
to: orchestrator
subject: property-coverage-thm11-s5
date: 2026-0808-11:45
started: 2026-0808-11:33
finished: 2026-0808-11:45
related:
  - plans/r0040-plan-from-orchestrator-to-orchestrator-property-coverage.md
  - docs/PropertiesVsTheorems.md
  - docs/PaperInventory.md
---

# r0040 — property coverage for Theorem 11, Theorem 12, Lemma 13, Theorem 14 and §5

**29 properties measured: 19 `S+P`, 1 `P`, 9 `N`, 0 `S≠`, 0 `S+H`.**

Twelve are conjuncts of the four numbered results, all `S+P`. Seventeen are
unnumbered prose claims of §5.2–§5.3, of which seven are `S+P`, one is `P` and
nine are `N`. `PaperInventory.md`'s prose-claim table (row 3, thirteen entries)
contains **no §5 entry at all**, so all seventeen prose rows below are new.

## 0. Method and the source pages

The properties were enumerated from the PDF before any Lean was read. Pages 26,
27, 28, 29, 30 and 31 of `ScottDomains/papers/Gunter Scott 1990.pdf` (printed
folios 25–30; printed = physical − 1) were rendered at 170 dpi with
`scripts/a3-render-range.sh` and read as images, because `pdftotext` renders
`♮`/`♯`/`♭` as `\`/`]`/`[` and drops the algebra operation entirely. Every glyph
claim below is off the rendered page, not off the extraction.

## 1. Where these results actually live

`docs/PropertiesVsTheorems.md` §1 places rows 9–12 (Thm 11, Thm 12, Lem 13, Thm
14) in **§4**, and `PaperInventory.md` rows 517–520 place all four in **§4.5**.
Measured against the rendered pages:

| # | Result | Section | Printed page |
| -- | ------ | ------- | -----------: |
| 1 | Theorem 11 | **§5.2** Formal definitions | 25 |
| 2 | Theorem 12 | **§5.3** Universal and closure properties | 28 |
| 3 | Lemma 13 | **§5.3** | 29 |
| 4 | Theorem 14 | **§6.1** Plotkin orders | 30 |

§4.5 (printed pp. 21–22) contains Lemma 8, Lemma 9 and Lemma 10 and nothing
else. `Powerdomain/BoundedComplete.lean`'s module docstring also cites Lemma 13
as "§4.5", and the r0040 plan's stream table says agent3 owns "§4.5 from
Theorem 11 onward, and all of §5" — Theorem 11 is not in §4.5 and Theorem 14 is
not in §5. Six wrong section attributions, none of which changes a count.

## 2. Numbered conjuncts — one row per property

| # | Property (paper's sentence) | § / p. | Label | Declaration | Evidence |
| -- | --------------------------- | ------ | ----- | ----------- | -------- |
| 1 | Thm 11.1 — for a countable pre-order `⟨A,⊢⟩` with `⊥` such that `x ⊢ ⊥` for every `x`, the poset `D` of ideals over `A` under set inclusion **is a domain** | 5.2 / 25 | `S+P` | `ScottDomains.IdealCompletion.thm11` (first conjunct) | `IdealCompletion.lean:457`; `Domain (IdealCompletion A) ∧ …` at `[Preorder A] [OrderBot A] [Countable A]`. `le_iff_subset` (`:131`) confirms the order is inclusion; `instDomain` (`:443`) is the witness |
| 2 | Thm 11.2 — `K(D)` **is the set of principal ideals** over `A` | 5.2 / 25 | `S+P` | `IdealCompletion.thm11` (second conjunct), from `compacts_eq_range_principal` | `IdealCompletion.lean:416`, proved from `isCompactElement_principal` and `exists_eq_principal_of_isCompactElement` |
| 3 | Thm 12.1 — under `T♮`, for continuous `f : D → E` there **exists** a homomorphism `ext(f) : D♮ → E` with `ext(f) ∘ {\|·\|} = f` | 5.3 / 28 | `S+P` | `ContinuousAlgebra.thm12_plotkin` | `ContinuousAlgebra.lean:1184`; `∃! h : Plotkin.Powerdomain D → E, IsHom h ∧ ∀ x, h (unit x) = f x` under `[IsSemilattice E]` = `T♮` |
| 4 | Thm 12.2 — that homomorphism is **unique** | 5.3 / 28 | `S+P` | `thm12_plotkin` (the `∃!`) | same declaration; uniqueness is the second component of `ExistsUnique` |
| 5 | Thm 12.3 — existence for `D♯` under `T♯` | 5.3 / 28 (prose after the proof) | `S+P` | `ContinuousAlgebra.thm12_smyth` | `:1120`, under `[IsUpper E]`; `IsUpper extends IsSemilattice` (`:166`) so `T♯ = T♮ + 4♯` is faithful |
| 6 | Thm 12.4 — uniqueness for `D♯` | 5.3 / 28 | `S+P` | `thm12_smyth` | same |
| 7 | Thm 12.5 — existence for `D♭` under `T♭` | 5.3 / 28 (prose after the proof) | `S+P` | `ContinuousAlgebra.thm12_hoare` | `:1079`, under `[IsLower E]`; `IsLower extends IsSemilattice` (`:172`) |
| 8 | Thm 12.6 — uniqueness for `D♭` | 5.3 / 28 | `S+P` | `thm12_hoare` | same |
| 9 | Lem 13.1 — `D` bounded complete ⟹ **`D♯`** bounded complete | 5.3 / 29 | `S+P` | `PowerdomainBC.lem13_smyth`, with `instBoundedCompleteSmyth` | `Powerdomain/BoundedComplete.lean:324` and `:332`; `BddAbove S → ∃ I, IsLUB S I`, plus the `OrderBot` from `IdealCompletion` — together the paper's own definition of bounded complete |
| 10 | Lem 13.2 — `D` bounded complete ⟹ **`D♭`** bounded complete | 5.3 / 29 | `S+P` | `PowerdomainBC.lem13_hoare`, with `instBoundedCompleteHoare` | `:195` and `:206`. `[BoundedComplete α]` is retained but unused — a strengthening, not a change of statement |
| 11 | Thm 14.1 — `D` bifinite ⟹ `D` is a domain and `K(D)` is a Plotkin order | 6.1 / 30 | `S+P` | `Recovered.thm14`, forward | `Skeleton/Recovered.lean:265`, `IsBifiniteViaProjections α ↔ Domain α ∧ IsBifinite α`, via `SFP.thm14_forward` (`SFP.lean:259`) |
| 12 | Thm 14.2 — converse | 6.1 / 30 | `S+P` | `Recovered.thm14`, backward | via `SFP.thm14_converse` (`SFP.lean:472`) |

### Theorem 14 is the paper's statement, not a repaired form

The plan asked whether `thm14` states the paper's *two* characterizations. It
does. The left side is `IsBifiniteViaProjections α` — the paper's own definition
verbatim, `(finiteImageProjections α).Countable ∧ DirectedOn (· ≤ ·) … ∧ IsLUB …
ScottHom.id` (`Recovered.lean:208`), where `finiteImageProjections` is
`{p | IsFinitaryProjection p ∧ (Set.range ⇑p).Finite}`, the paper's `M`. The
right side is `Domain α ∧ IsBifinite α` with `Domain extends IsAlgebraic` plus
countable basis (`Domain.lean:128`) and `IsBifinite α := IsPlotkinOrder (compacts
α)` (`Bifinite.lean:62`), and `IsPlotkinOrder A := ∀ u finite ⊆ A, ∃ N finite,
N ◁ A ∧ u ⊆ N` (`:38`) — the paper's Plotkin-order definition verbatim. No
hypothesis is added and no conclusion is weakened. **`S+P`, not `S≠`.**

### Lemma 13's missing third conjunct, confirmed against the paper

Read off the rendering of physical page 30: *"Two of the powerdomains preserve
the property of bounded completeness: **Lemma 13** If `D` is a bounded complete
domain then so are `D♯` and `D♭`."* The convex powerdomain is not named. The
paper does not merely omit it — §6's opening sentence (physical page 30,
printed 29) asserts the **negation**: *"only the convex powerdomain `(·)♮` does
not take bounded complete domains to bounded complete domains"*, with the
`T × T` counterexample `u, v, u′, v′` and the conclusion *"no least upper bound
for `{u, u′}` exists and `(T × T)♮` is therefore not bounded complete."*

So the development's docstring claim (`Powerdomain/BoundedComplete.lean:28–33`)
is correct as to Lemma 13. But **that negation is itself a paper property and is
`P` — prose only**: `grep` for `not bounded complete`, `notBoundedComplete`,
`not_boundedComplete`, `Bool × Bool`, `T × T` over `ScottDomains/` finds no
declaration about `(T × T)♮`; the three r0031 refutations named in the docstring
were retired in r0032 and were about a different defect (`idealSup`'s guard), not
about the convex powerdomain. This row sits at the **§6 opening, agent4's
range**, so it is reported here as a cross-reference and is *not* counted in my
totals — but it must not fall between the two streams.

## 3. Unnumbered prose claims of §5 — one row per property

| # | Property (paper's sentence) | § / p. | Label | Declaration | Evidence |
| -- | --------------------------- | ------ | ----- | ----------- | -------- |
| 13 | `↓x = {y ∈ A \| x ⊢ y}` **is an ideal**, the principal ideal generated by `x` | 5.2 / 25 | `S+P` | `IdealCompletion.principal` | `IdealCompletion.lean:200`; the definition lands in `IdealCompletion A`, whose inhabitants are ideals, so idealhood is a typing judgment the kernel checks. `IdealCompletion.isIdeal` (`:142`) reads it back as `Order.IsIdeal` |
| 14 | "In short, an ideal is a subset which is **directed and downward closed**" — the paper's clause 1 (every finite `u ⊆ s` has an upper bound in `s`) together with clause 2 amounts to that | 5.2 / 25 | **`P`** | none | `IdealCompletion.lean:34` asserts *"`Order.Ideal A` is **exactly** the paper's definition"* in the module docstring. What is formalized is Mathlib's `IsLowerSet ∧ Nonempty ∧ DirectedOn`, i.e. the paper's **gloss**; the printed clause 1 quantifies over arbitrary finite subsets, and no declaration proves finite-subset-directedness equivalent to nonempty-plus-binary-directedness. `IdealCompletion.lower` (`:134`) and `.directed` (`:139`) carry docstrings naming "clause 2" and "clause 1", which is the claim, not the proof |
| 15 | `⊢♭` "is usually only a **pre-order and not a poset**" | 5.2 / 26 | `S+P` | `Hoare.Pf.not_isPartialOrder` | `Powerdomain/Hoare.lean:194`, `∃ u v : Pf ℕ, u ≤ v ∧ v ≤ u ∧ u ≠ v`. The **witness differs**: the paper's is `u` against `u ∪ {⊥}` in `P*f(N⊥)`, Lean's is `{0,1}` against `{1}` in `Pf ℕ`. The property — antisymmetry fails — is the same and is proved. (Companions: `Smyth.exists_le_le_ne`, `Plotkin.exists_le_le_ne_of_lt_lt`) |
| 16 | `(N⊥)♭` **is isomorphic to `P N`**, all subsets of `N` under subset inclusion | 5.2 / 26 | **`N`** | — | greps in §5 below |
| 17 | `(N⊥)♯` **is isomorphic to `{N} ∪ P*f(N)`** ordered by superset inclusion | 5.2 / 26 | **`N`** | — | greps in §5 |
| 18 | For `u, v ∈ P*f(N⊥)`: `u ⊢♮ v` iff (1) `⊥ ∈ v` and `u ⊇ v`, or (2) `u = v` | 5.2 / 26 | **`N`** | — | greps in §5 |
| 19 | `(N⊥)♮` corresponds to the finite non-empty subsets of `N` unioned with the arbitrary subsets of `N⊥` containing `⊥` | 5.2 / 26 | **`N`** | — | greps in §5 |
| 20 | `s ⊔ t = {w \| u ∪ v ⊢♮ w for some u ∈ s, v ∈ t}` **is an ideal** | 5.3 / 27 | `S+P` | `ContinuousAlgebra.isIdeal_opSet` | `ContinuousAlgebra.lean:697`, `Order.IsIdeal (opSet s t)`, with `opSet` (`:690`) transcribing the displayed set |
| 21 | `⊔ : D♮ × D♮ → D♮` **is continuous**, and "similar facts apply … for `D♯` and `D♭`" | 5.3 / 27 | `S+P` | `ContinuousAlgebra.instBinopIdealCompletion` (field `scottContinuous_op`) | `:711`. Stated generically over any `[FinSets K A]`, so the one instance discharges all three powerdomains; continuity is **joint**, `ScottContinuous fun p : E × E => op p.1 p.2` (`:111`), which is the paper's literal reading |
| 22 | `{\|x\|} = {u ∈ P*f(K(D)) \| {x₀} ⊢♮ u for some compact x₀ ⊑ x}` **forms an ideal** | 5.3 / 27 | `S+P` | `ContinuousAlgebra.isIdeal_unitSet` | `:826`, with `unitSet` (`:821`) transcribing the displayed set; algebraicity of `D` is what discharges directedness |
| 23 | `{\|·\|} : D → D♮` **is a continuous function**, and similarly for `♯` and `♭` | 5.3 / 27 | `S+P` | `ContinuousAlgebra.scottContinuous_unit` | `:859`, generic in `[FinSets ↥(compacts D) A]` so all three are covered |
| 24 | "it may be the case that `s` is a *subset* of `t` without it being the case that `s ⊆ t`" (with *element* := `{\|x\|} ⊔ s = s` and *subset* := `s ⊔ t = t`) | 5.3 / 27 | **`N`** | — | greps in §5 |
| 25 | In `(N⊥)♯`: `{\|1, ⊥\|} = ⊥ = {\|⊥\|}` — the upper powerdomain identifies `P₁` with the everywhere-divergent `Q` | 5.3 / 27 | **`N`** | — | greps in §5 |
| 26 | In `(N⊥)♭`: `{\|1, ⊥\|} = {\|1\|}` and `{\|1, ⊥\|} ≠ ⊥` | 5.3 / 27 | **`N`** | — | greps in §5 |
| 27 | In `(N⊥)♮`: `{\|1, ⊥\|}`, `{\|1\|}` and `{\|⊥\|}` are all **distinct** | 5.3 / 27 | **`N`** | — | greps in §5 |
| 28 | "for any domain `D`, each of the algebras `D♮`, `D♯` and `D♭` **satisfies `T♮`**" | 5.3 / 28 | `S+P` | `ContinuousAlgebra.instIsSemilatticeIdealCompletion` | `:749`, one generic instance over `[FinSets K A]` giving `op_assoc`, `op_comm`, `op_idem`; its docstring quotes the paper's sentence and the kernel checks it for all three carriers |
| 29 | For continuous `f : D → E` there is a **unique homomorphism `f♮`** completing the naturality square, namely `f♮ = ext({\|·\|} ∘ f)`; "of course, there are functions `f♯` and `f♭` with similar definitions" | 5.3 / 28–29 | **`N`** | — | greps in §5 |

## 4. Constructions in my range (definitions, excluded from the property count)

`PropertiesVsTheorems.md` excludes definitions as objects rather than assertions.
Recorded here because the plan named them, and all five exist:

| # | Paper object | Lean | Faithfulness |
| -- | ------------ | ---- | ------------ |
| 1 | pre-order; ideal over a pre-order; the **ideal completion** | `IdealCompletion A := Order.Ideal A` (`IdealCompletion.lean:96`) | order is inclusion (`le_iff_subset`); the paper's `⊢` is Mathlib's `≥`, documented at `:24–30` |
| 2 | `⊢♯` on `P*f(A)`: `(∀x ∈ u)(∃y ∈ v). x ⊒ y` | `Smyth.finsetLE`, `Smyth.Basis.le_def` (`Powerdomain/Smyth.lean:172`) | orientation flip derived in the docstring at `:31–45`; `u ≤ v ↔ ∀ b ∈ v, ∃ a ∈ u, a ≤ b` |
| 3 | `⊢♭` on `P*f(A)`: `(∀y ∈ v)(∃x ∈ u). x ⊒ y` | `Hoare.Pf.le_def` (`Powerdomain/Hoare.lean:147`) | `u ≤ v ↔ ∀ x ∈ u, ∃ y ∈ v, x ≤ y`, matching §5.1's lower-powerdomain sentence exactly |
| 4 | `⊢♮ := ⊢♯ ∧ ⊢♭` | `Plotkin.FinCompacts.le_def` (`Powerdomain/Plotkin.lean:159`) | the literal conjunction. **One narrowing:** the paper defines `⊢♮` on `P*f(A)` for an arbitrary poset `A`; `FinCompacts` is defined only over `↥(compacts D)`. The other two are stated at a general `[Preorder α]` |
| 5 | `D♮`, `D♯`, `D♭` as ideals over `⟨P*f(K(D)), ⊢·⟩` | `Plotkin.Powerdomain`, `Smyth.Powerdomain`, `Hoare.Powerdomain` | each with its own Theorem 11 instance: `Hoare.thm11_hoare` (`:231`), `Smyth.powerdomain_isDomain` (`:281`), `Plotkin.isDomain` (`:300`) |

`P*f(S)` is `{u : Finset A // u.Nonempty}` in each carrier; the paper's `Pf⁻(S)`
(all finite subsets, `∅` included) is used only to make the point that `∅` is a
Smyth *top* and a Hoare *bottom*, which `Smyth.finsetLE_empty` and
`not_finsetLE_empty` (`:119`, `:126`) do state.

## 5. The nine `N` rows, with their greps

`N` carries the burden of proof. Every grep was run over
`/home/milnes/projects/ScottLean4-agent3/ScottDomains/ScottDomains/`, recursively.

### N-group A — the `N⊥` worked examples: rows 16, 17, 18, 19, 25, 26, 27

The flat domain of naturals is **never constructed**, so nothing in the
development can state any of these seven.

| # | Grep | Hits |
| -- | ---- | ---- |
| 1 | `WithBot ℕ\|WithBot Nat\|flatNat\|Nat⊥\|N⊥` | **1** — `Powerdomain/Smyth.lean:222`, a docstring cross-reference *"…the same observation for `⊢♭` in its computation of `(N⊥)♭`"*. No declaration |
| 2 | `Option ℕ\|WithBot\b.*ℕ\|natFlat\|FlatNat\|liftNat\|Lift ℕ` | **0** |
| 3 | `hoareIso\|smythIso\|plotkinIso\|powerdomain_eq\|example_\|Example` | **0** |
| 4 | `isomorphic\|≃o` restricted to `Powerdomain/` and `Powerset.lean` | **2**, both `Powerdomain/Universal.lean` (`:154`, `:357`) about ranges of retracts — unrelated |
| 5 | `superset` | hits in `Dyadic`, `Atomless`, `CombinatorRep`, `PRep`, `JungNets` — all §7's `U₀`, none about `(N⊥)♯` |
| 6 | `nonTrivial\|nontrivial\|trivial ideal` in `Powerdomain/` and `ContinuousAlgebra.lean` | **2**, both unrelated docstring prose (`Smyth.lean:125`, `:289`) |

### N-group B — the "element"/"subset" relations: row 24

| # | Grep | Hits |
| -- | ---- | ---- |
| 1 | `IsElement\|isElement\|memPD\|IsSubsetPD\|subsetOf\|"element"\|"subset"` | **0** |
| 2 | `nondeterminis\|non-determinis\|diverge\|divergent` | **3**, all unrelated (`Audit/Skeleton.lean:20`, `CombinatorRep.lean:51`, a `[Gun87]` citation at `BifiniteUniversal.lean:40`) |
| 3 | `unit_bot\|unit_pair\|singleton_bot\|bot_ne\|ne_bot\|distinct` in `Powerdomain/` and `ContinuousAlgebra.lean` | hits are `Smyth.singleton_bot_finsetLE`/`bot_eq_singleton_bot` (the `OrderBot` construction) and `PowerdomainBC.sSup_hoareWitness_ne_bot` (the r0032 nondegeneracy check). None is `{\|x\|} ⊔ s = s` or `s ⊔ t = t` |

### N-group C — the functorial action `f♮` / `f♯` / `f♭`: row 29

| # | Grep | Hits |
| -- | ---- | ---- |
| 1 | `fSharp\|fFlat\|fNatural\|powerdomainMap\|mapPowerdomain\|Powerdomain.map\|hoareMap\|smythMap\|plotkinMap` | **0** |
| 2 | `extHom\|Functor\|functorial\|naturality\|f♮\|f♯\|f♭` | hits only at `Colimit.lean:140` (`section Functor`, the stage functor `M` on posets), `Dyadic.lean:443`, `PRepFun.lean:98`/`:655` and `CombinatorRep.lean:506`/`:535`/`:543` — every one of the last four is a note recording an **absent** functorial action |
| 3 | `ext(` | **2 files**: `ContinuousAlgebra.lean` (Theorem 12's `ext (f : D → E) : IdealCompletion A → E`, an extension of `f` along `{\|·\|}`, *not* a map `D♮ → E♮`) and `JungFinite.lean` (unrelated) |

Two independent modules already record the same absence for their own purposes:
`PRepFun.lean:98` — *"`grep` over every module finds no functorial action"* — and
`PaperInventory.md` row 554, *"the development defines **no action of a map on
either powerdomain**, so there is no `r ↦ r♯`"*. That is Lemma 28's blocker, and
row 29 is its source: §5.3's `f♮` is where the paper supplies the action, and it
was never formalized.

## 6. Re-derived conjunct counts against `docs/PropertiesVsTheorems.md` §1

| # | Result | §1 count | Re-derived | Moved? | Note |
| -- | ------ | -------: | ---------: | ------ | ---- |
| 1 | Thm 11 | 2 | **2** | no | but §1's *note* is **wrong** — see below |
| 2 | Thm 12 | 6 | **6** | no | note correct; refined below |
| 3 | Lem 13 | 2 | **2** | no | note correct |
| 4 | Thm 14 | 2 | **2** | no | note correct |
| — | numbered total, my range | 12 | **12** | no | |
| — | prose claims, my range | 0 listed | **17** | **+17** | `PaperInventory.md` row 3's thirteen-entry table has no §5 entry |

**No numbered conjunct count moved.** Two notes are wrong and one is imprecise:

1. **Theorem 11's note, "the theorem and its converse", is wrong.** The paper's
   Theorem 11 has no converse. Its two conjuncts are *"`D` is a domain"* and
   *"`K(D)` is the set of principal ideals over `A`"* — a single sentence with a
   conjunctive conclusion. The count 2 is right for the wrong reason.
   `IdealCompletion.thm11_converse` (`:589`) — every domain is order-isomorphic
   to the ideal completion of `K(D)` — is a development-added theorem the paper
   does not state at Theorem 11. It should not be counted as one of the two, and
   `PaperInventory.md` row 517's headline *"(all domains so arise)"* is likewise
   an addition, not a conjunct.

2. **Theorem 12's six are not six printed in the theorem.** Only two — existence
   and uniqueness at `D♮`/`T♮` — are in the theorem's italic statement. The other
   four arrive in the sentence *after* the proof: *"Theorem 12 still holds when
   `D♮` and `T♮` are replaced by `D♯` and `T♯` respectively, or by `D♭` and `T♭`
   respectively."* The base theory is `T♮`, read off the rendered page 29 (the
   extraction gives `T \`). All six are stated in Lean and all six are proved.

3. **Sections.** §1's `§` column reads 4 for all four results. Measured: 5.2,
   5.3, 5.3, 6.1 (table in §1 above).

## 7. Hypothesis deviations recorded (none large enough to be `S≠`)

| # | Property | Paper | Lean | Direction |
| -- | -------- | ----- | ---- | --------- |
| 1 | Thm 12 (all six) | "Let `D` be a **domain**" | `[CompletePartialOrder D] [IsAlgebraic D]` — countability of `K(D)` never used | Lean is **stronger** (weaker hypothesis); the paper's statement is an instance |
| 2 | Lem 13.2 (`D♭`) | "`D` is a bounded complete domain" | `[BoundedComplete α]` is present but not consumed — `hoare_exists_isLUB_pair` gives joins for **every** pair | Lean is **stronger**; the hypothesis is retained deliberately so the statement is the paper's |
| 3 | Thm 11 | "there is an element `⊥ ∈ A` such that `x ⊢ ⊥`" | `[OrderBot A]` | equivalent — the least element named rather than asserted to exist |
| 4 | Row 15 (`⊢♭` not a poset) | witness `u` vs `u ∪ {⊥}` in `P*f(N⊥)` | witness `{0,1}` vs `{1}` in `Pf ℕ` | same property, different witness |

## 8. Measurement discipline

No `.lean` file was read-modified: `git status` shows one modified file,
`scripts/a3-render-range.sh`, and the modification is the executable bit. The
development holds **1 `sorry`**, at `Skeleton/Section6.lean:197`, measured by
`grep` over `ScottDomains/ScottDomains/` — unchanged, since nothing was edited.
No build was run and none was needed.

## 9. Totals

| # | Label | Count |
| -- | ----- | ----: |
| 1 | `S+P` | **19** |
| 2 | `S+H` | 0 |
| 3 | `S≠` | 0 |
| 4 | `P` | **1** |
| 5 | `N` | **9** |
| — | **total** | **29** |

`P` row: 14 (the ideal definition's finite-subset clause).

`N` rows: 16, 17, 18, 19 (the three `N⊥` powerdomain computations and the `⊢♮`
characterization); 24 (*subset* without `⊆`); 25, 26, 27 (the three
non-determinism identities); 29 (the functorial action `f♮`/`f♯`/`f♭`).

Eight of the nine `N` rows are worked examples over one carrier the development
does not have — the flat naturals `N⊥`. Building it is one `WithBot ℕ` and its
`Domain` instance; rows 16–19 and 25–27 then become statable in a single module.
Row 29 is different in kind: it is a missing **operation**, and it is the same
gap `PaperInventory.md` row 554 records as the obstruction to Lemma 28's `()♯`
and `()♭` conjuncts.
