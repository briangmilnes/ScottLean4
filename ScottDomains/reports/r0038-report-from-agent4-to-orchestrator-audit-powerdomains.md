---
round: r0038
from: agent4
to: orchestrator
subject: audit-powerdomains
date: 2026-0808-09:54
started: 2026-0808-09:39
finished: 2026-0808-09:54
related:
  - plans/r0038-plan-from-orchestrator-to-orchestrator-theorem-audit.md
  - docs/PropertiesVsTheorems.md
  - ScottDomains/Audit/Powerdomains.lean
---

# r0038 — `Audit.Powerdomains`: 201 declarations classified

Modules: `IdealCompletion`, `Powerdomain/{Hoare,Smyth,Plotkin,BoundedComplete,Universal}`,
`ContinuousAlgebra`.

## 1. What was measured, and the two counting rules

`scripts/module-counts.sh` reports **197** theorem-ish declarations across the
seven modules (44 + 9 + 16 + 24 + 22 + 20 + 62). That number uses `counts.sh`'s
rule — a line beginning with `theorem` or `lemma`, optionally preceded by one
attribute group — which **misses `protected theorem`**. `IdealCompletion.lean`
has four of those (`lower`, `nonempty`, `directed`, `isIdeal`), so this report
carries **201 rows**: the 197, plus those four, marked `[prot]`.

Three measurement instruments were used, and the second and third are new:

| # | Instrument | What it answered |
| -- | --------- | ---------------- |
| 1 | `scripts/unused-theorems.sh` | 22 of the 130 project-wide never-mentioned names fall in these seven modules |
| 2 | `scripts/pd-audit-cites.sh` (new) | per-declaration mention count and the file:line of each mention |
| 3 | `lake env lean` on two scratch probe files | the **elaborated** signatures, and `rfl`-checks of the duplicate pairs |

Instrument 1's stated under-reporting bit is the reason for 2 and 3, and it bit
five times in this area. `Hoare.isCompactElement_iff` reads as 23 mentions and
has **zero** — every hit was `IsProjection.isCompactElement_iff`
(`FinitaryProjection.lean`) or `Dyadic.isCompactElement_iff` masking it under
final-component matching. `Plotkin.isCompactElement_iff`, all three `le_def`s,
all four `ext`s and `Plotkin.FinCompacts.finite` (413 apparent mentions) collide
the same way. Every count in the tables below is the qualified-name count, not
the masked one.

Instrument 3 mattered more. Reading a declaration's source is not reading its
signature, because Lean's `variable` inclusion decides which instance binders
survive. Measured:

    ScottDomains.Hoare.Powerdomain   : (D : Type u) → [CompletePartialOrder D] → Type u
    ScottDomains.Smyth.Powerdomain   : (D : Type u) → [CompletePartialOrder D] → Type u
    ScottDomains.Plotkin.Powerdomain : (D : Type u) → [CompletePartialOrder D] → Type u

`Hoare.Powerdomain` is declared under `variable (D) [CompletePartialOrder D] [Domain D]`,
and `instBoundedCompleteHoare`'s docstring states as fact that `[Domain α]` is
present there "only because `Hoare.Powerdomain` takes it." It does not take it.
That single measurement produced all three `W` findings in §4.

## 2. Label totals

| # | Label | Count | Share of 201 |
| -- | ----- | ----: | -----------: |
| 1 | `P` — states a paper property | 11 | 5.5% |
| 2 | `S` — support, something cites it | 121 | 60.2% |
| 3 | `A` — projection / `simp` / `ext` API | 42 | 20.9% |
| 4 | `U` — uncited, not a paper property, not API | 20 | 10.0% |
| 5 | `D` — duplicate | 5 | 2.5% |
| 6 | `W` — over-strength hypothesis | 2 | 1.0% |
| — | **total** | **201** | |

Per module:

| # | Module | Rows | P | S | A | U | D | W |
| -- | ----- | ---: | -: | -: | -: | -: | -: | -: |
| 1 | `IdealCompletion.lean` | 48 | 2 | 30 | 14 | 2 | 0 | 0 |
| 2 | `Powerdomain/Hoare.lean` | 9 | 1 | 1 | 5 | 1 | 1 | 0 |
| 3 | `Powerdomain/Smyth.lean` | 16 | 1 | 5 | 4 | 5 | 1 | 0 |
| 4 | `Powerdomain/Plotkin.lean` | 24 | 1 | 8 | 8 | 5 | 2 | 0 |
| 5 | `Powerdomain/BoundedComplete.lean` | 22 | 0 | 18 | 0 | 2 | 0 | 2 |
| 6 | `Powerdomain/Universal.lean` | 20 | 1 | 16 | 2 | 1 | 0 | 0 |
| 7 | `ContinuousAlgebra.lean` | 62 | 5 | 43 | 9 | 4 | 1 | 0 |

**The `U` rate is 20 of 201, 10.0%** — above r0020's 3%. §5 breaks it into two
populations that call for opposite actions, and only 8 of the 20 are the
speculative API r0020 commented out. On that reading the comparable rate is
**8 of 201, 4.0%**.

### How the labels were assigned when two applied

Three rules, stated because they move numbers:

1. **`A` beats `S`.** A declaration tagged `@[simp]` or `@[ext]`, or one that is
   a bare field/coercion projection, is `A` regardless of how many named citers
   it has. Otherwise a named citer makes it `S`.
2. **`W` beats `P`.** `lem13_hoare` and `lem13_smyth` state Lemma 13's two
   conjuncts and are labelled `W`, not `P`, because the actionable finding is the
   unconsumed hypothesis. This follows r0034's precedent, where `thm12` — also a
   paper result — was a `W` finding and was fixed by weakening, not deleting.
   **Neither is a deletion candidate.**
3. **`D` beats `U`.** A declaration that is `rfl`-equal to another and uncited is
   `D`, since naming the other one is stronger evidence than "nothing cites it."

## 3. The full table

`cites` counts mentions in proof terms only; mentions inside docstrings and
inside the trailing axiom-audit comments are excluded and noted where they are
the only ones.

### 3.1 `IdealCompletion.lean` — 48 rows

| # | Declaration | Label | Evidence |
| -- | ---------- | ----- | -------- |
| 1 | `toIdeal_ofIdeal` | A | `@[simp]`, `rfl`; type-synonym round trip; 0 citers |
| 2 | `ofIdeal_toIdeal` | A | `@[simp]`, `rfl`; 0 citers |
| 3 | `mem_toIdeal` | A | `@[simp]`, `Iff.rfl`; 0 citers |
| 4 | `mem_ofIdeal` | A | `@[simp]`, `Iff.rfl`; 0 citers |
| 5 | `ext` | A | `@[ext]`; fires unnamed under the `ext` tactic (`ContinuousAlgebra.lean:740,751,768`) |
| 6 | `le_iff_subset` | U | `Iff.rfl`, no attribute, 0 citers |
| 7 | `lower` `[prot]` | A | interface transfer from `Order.Ideal.lower`; dot-notation citers `IdealCompletion:207,234,309`, `ContinuousAlgebra:773` |
| 8 | `nonempty` `[prot]` | A | interface transfer; `IdealCompletion:395`, `ContinuousAlgebra:699,700,794` |
| 9 | `directed` `[prot]` | A | interface transfer; `IdealCompletion:290,363,398,432`, `ContinuousAlgebra:703,704,771` |
| 10 | `isIdeal` `[prot]` | A | interface transfer; `IdealCompletion:288,314` |
| 11 | `mem_genIdeal` | U | `Iff.rfl`, no attribute, 0 citers |
| 12 | `subset_genIdeal` | S | `isLUB_idealSup_of_isIdeal_genIdeal` (265), `sUnion_subset_genIdeal` (177) |
| 13 | `genIdeal_subset` | S | `genIdeal_eq_sUnion_of_isIdeal` (188), `genIdeal_empty` (307) |
| 14 | `sUnion_subset_genIdeal` | S | `genIdeal_eq_sUnion_of_isIdeal` (187) |
| 15 | `genIdeal_eq_sUnion_of_isIdeal` | S | `coe_idealSup_of_isIdeal` (277, 278) |
| 16 | `mem_principal` | A | `@[simp]`; `ClosureProperties/Powerdomain:87,88`, `IdealCompletion:618` |
| 17 | `mem_principal_self` | S | `ContinuousAlgebra:559,741`, `IdealCompletion:387` |
| 18 | `principal_le_iff` | A | `@[simp]`; `.mp`/`.mpr` at `IdealCompletion:388,403,404,437`, `ContinuousAlgebra:537,538`, `BoundedComplete:479` |
| 19 | `principal_mono` | S | `ClosureProperties/Powerdomain:85,90–92`, `Smyth:263`, `BoundedComplete:441,442` |
| 20 | `bot_mem` | S | `IdealCompletion:234,309,361`, `ClosureProperties/StrictFunction:232` |
| 21 | `bot_eq_principal` | A | `@[simp]`; `Colimit:995` |
| 22 | `sSup_eq_idealSup` | S | `mem_sSup_iff` (295), `instCompletePartialOrder` (331) |
| 23 | `coe_idealSup_of_isIdeal_genIdeal` | S | 264, 267, 278, 322 |
| 24 | `isLUB_idealSup_of_isIdeal_genIdeal` | S | `boundedComplete` (377), `BoundedComplete:154` |
| 25 | `coe_idealSup_of_isIdeal` | S | `mem_sSup_iff` (295) |
| 26 | `isIdeal_sUnion` | S | `mem_sSup_iff` (295) |
| 27 | `mem_sSup_iff` | S | `ContinuousAlgebra:580,729,730`, `IdealCompletion:333,334` |
| 28 | `genIdeal_empty` | S | `isIdeal_genIdeal_empty` (313), `idealSup_empty` (322) |
| 29 | `isIdeal_genIdeal_empty` | S | `idealSup_empty` (322) |
| 30 | `idealSup_empty` | S | `instCompletePartialOrder` (331) |
| 31 | `isIdeal_genIdeal` | S | `boundedComplete` (377) |
| 32 | `boundedComplete` | S | `Dyadic:293,358,359`, `BoundedComplete:208,334` |
| 33 | `isCompactElement_principal` | S | 412, 433, 438; `ClosureProperties/Powerdomain:80` |
| 34 | `exists_eq_principal_of_isCompactElement` | S | 411, 616 |
| 35 | `isCompactElement_iff_exists_eq_principal` | S | 418, 428, 429; `Hoare:245`; `Plotkin:294`; `ClosureProperties/Powerdomain:82,104` |
| 36 | `compacts_eq_range_principal` | S | 445, 459; `Smyth:275`; `Plotkin:289`; `Colimit`, `BifiniteUniversal` |
| 37 | `thm11` | **P** | Theorem 11 §5.2, forward half — countable pre-order with least element ⇒ ideals form a domain, `K(D)` = principal ideals |
| 38 | `isIdeal_compactsBelow` | S | `idealOfElem` (494) |
| 39 | `mem_idealOfElem` | A | `@[simp]`; `idealOfElem_elemOfIdeal` (534) |
| 40 | `directedOn_val_image` | S | `isLUB_elemOfIdeal` (514), `idealOfElem_elemOfIdeal` (538) |
| 41 | `isLUB_elemOfIdeal` | S | 539, 542 |
| 42 | `val_image_idealOfElem` | S | `elemOfIdeal_idealOfElem` (527) |
| 43 | `elemOfIdeal_idealOfElem` | S | `orderIsoIdealCompletionCompacts` (558) |
| 44 | `idealOfElem_elemOfIdeal` | S | 559 |
| 45 | `idealOfElem_le_iff` | S | 560 |
| 46 | `orderIsoIdealCompletionCompacts_apply` | A | `@[simp]`; 0 citers (`LemThirty` uses the `def`, not this equation) |
| 47 | `OrderIso.map_sSup_of_directedOn` | S | `thm11_converse` (594), `Colimit:950,954` |
| 48 | `thm11_converse` | **P** | Theorem 11 §5.2, converse half — every domain is the ideal completion of `K(D)`, by an isomorphism of cpos |

### 3.2 `Powerdomain/Hoare.lean` — 9 rows

| # | Declaration | Label | Evidence |
| -- | ---------- | ----- | -------- |
| 1 | `Pf.toFinset_ofFinset` | A | `@[simp]`; `ContinuousAlgebra:1062` |
| 2 | `Pf.toFinset_nonempty` | A | projection (`u.2`); `ClosureProperties/Powerdomain:189`, `BoundedComplete:176`, `Hoare:165`, `ContinuousAlgebra:1047,1051` |
| 3 | `Pf.mem_def` | A | `@[simp]`; `ClosureProperties/Powerdomain:175,191,194,199,220`, `ContinuousAlgebra:1062` |
| 4 | `Pf.ext` | A | `@[ext]`; `ClosureProperties/Powerdomain:177`, `ContinuousAlgebra:1046` |
| 5 | `Pf.le_def` | S | `thm12_hoare`'s discharge (`ContinuousAlgebra:1084`), `Hoare:164,196,197` |
| 6 | `Pf.mem_bot` | A | `@[simp]`; `BoundedComplete:411` |
| 7 | `Pf.not_isPartialOrder` | U | 0 proof citers; nondegeneracy witness that `⊑♭` is not antisymmetric — **keep** |
| 8 | `thm11_hoare` | **P** | §5.2 prose claim: `D♭` is the domain of ideals over `⟨Pf(K(D)), ⊢♭⟩`, `K(D♭)` = principal ideals |
| 9 | `isCompactElement_iff` | **D** | `rfl`-equal to `IdealCompletion.isCompactElement_iff_exists_eq_principal` at `A := Hoare.Pf ↥(compacts D)` — kernel-checked, `Audit/Powerdomains.lean` pair 1; 0 citers |

### 3.3 `Powerdomain/Smyth.lean` — 16 rows

| # | Declaration | Label | Evidence |
| -- | ---------- | ----- | -------- |
| 1 | `finsetLE_refl` | S | `Basis.instPreorder` (169) |
| 2 | `finsetLE_trans` | S | `Basis.instPreorder` (170) |
| 3 | `finsetLE_empty` | U | mentioned only in the module docstring (61, 124); 0 proof citers; witness that `∅` is a **top** for `⊑♯` — **keep** |
| 4 | `not_finsetLE_empty` | U | docstring only (62); 0 proof citers; the other half of the same witness — **keep** |
| 5 | `singleton_bot_finsetLE` | S | `Basis.instOrderBot` (184) |
| 6 | `Basis.ext` | A | `@[ext]`; `toFinset_injective` (162) |
| 7 | `Basis.toFinset_injective` | A | projection; `instCountable` (195), `ContinuousAlgebra:1092` |
| 8 | `Basis.le_def` | S | `thm12_smyth`'s discharge (`ContinuousAlgebra:1125`) |
| 9 | `Basis.bot_toFinset` | A | `@[simp]`; 0 citers |
| 10 | `Basis.bot_eq_singleton_bot` | U | docstring only (64); 0 proof citers; `rfl` restatement of `instOrderBot`'s `bot` field |
| 11 | `Basis.singleton_toFinset` | A | `@[simp]`; 212, 215, 232, 238 |
| 12 | `Basis.singleton_le_singleton` | S | `ContinuousAlgebra:1107` (`instFinSetsSmyth.singleton_mono`), `Smyth:263` |
| 13 | `Basis.exists_le_le_ne` | U | docstring only (166); 0 proof citers; nondegeneracy witness that `⊑♯` is not antisymmetric — **keep** |
| 14 | `unit_mono` | U | 0 citers. `Smyth.unit` (the η of `D♯`) exists only to carry this lemma, and is itself uncited. Superseded by `ContinuousAlgebra.unit`, which is the unit Theorem 12 uses and which is defined generically for all three powerdomains — **speculative API** |
| 15 | `compacts_eq_range_principal` | **D** | `rfl`-equal to `IdealCompletion.compacts_eq_range_principal` at `A := Smyth.Basis D` — kernel-checked, pair 4; one citer, `powerdomain_isDomain` (285) |
| 16 | `powerdomain_isDomain` | **P** | §5.2 prose claim: `D♯` is a domain, `K(D♯)` = principal ideals |

### 3.4 `Powerdomain/Plotkin.lean` — 24 rows

| # | Declaration | Label | Evidence |
| -- | ---------- | ----- | -------- |
| 1 | `FinCompacts.finite` | A | projection (`u.2.1`); `ContinuousAlgebra:1134,1150`, `Plotkin:227` |
| 2 | `FinCompacts.nonempty` | A | projection (`u.2.2`); `Plotkin:227`, `ContinuousAlgebra:1142,1151` |
| 3 | `FinCompacts.mem_carrier` | A | `@[simp]`; `ClosureProperties/Powerdomain:299` |
| 4 | `FinCompacts.ext` | A | `@[ext]`; `ClosureProperties/Powerdomain:298` |
| 5 | `FinCompacts.mem_single` | A | `@[simp]`; `Plotkin:207,229`, `ContinuousAlgebra:1171,1173,1174` |
| 6 | `FinCompacts.mem_pair` | A | `@[simp]`; `Plotkin:178,183–185,192,198,206` |
| 7 | `FinCompacts.mem_triple` | A | `@[simp]`; `Plotkin:179,180,182,187,193` |
| 8 | `FinCompacts.le_def` | U | 0 citers anywhere. The Hoare and Smyth counterparts are each consumed by their `thm12_*` discharge; the Plotkin discharge (`ContinuousAlgebra:1190,1193`) uses `huv.1`/`huv.2` directly and never names this |
| 9 | `FinCompacts.le_hoare` | U | 0 citers, no attribute; `h.1` of the Egli–Milner conjunction |
| 10 | `FinCompacts.le_smyth` | U | 0 citers, no attribute; `h.2` |
| 11 | `FinCompacts.exists_le_le_ne_of_lt_lt` | S | `not_antisymm_natPowerset` (349) |
| 12 | `FinCompacts.not_single_le_pair` | S | `not_single_le_pair_natPowerset` (361) |
| 13 | `FinCompacts.bot_eq_single` | A | `@[simp]`; 0 citers |
| 14 | `principal_le_principal` | S | `principal_eq_principal_iff` (278, 280) |
| 15 | `principal_eq_principal_iff` | S | `exists_ne_principal_eq` (356) |
| 16 | `compacts_eq_range_principal` | **D** | `rfl`-equal to `IdealCompletion.compacts_eq_range_principal` at `A := Plotkin.FinCompacts D` — kernel-checked, pair 3; 0 citers |
| 17 | `isCompactElement_iff` | **D** | `rfl`-equal to `IdealCompletion.isCompactElement_iff_exists_eq_principal` at the same `A` — kernel-checked, pair 2; 0 citers |
| 18 | `isDomain` | **P** | §5.2 prose claim: `D♮` is a domain, `K(D♮)` = principal ideals |
| 19 | `cEmpty_lt_cZero` | S | `not_antisymm_natPowerset` (349) |
| 20 | `cZero_lt_cZeroOne` | S | 349 |
| 21 | `not_cZero_le_cOne` | S | `not_single_le_pair_natPowerset` (361) |
| 22 | `not_antisymm_natPowerset` | S | `exists_ne_principal_eq` (355) |
| 23 | `exists_ne_principal_eq` | U | 0 citers; witness that the ideal completion performs the convex quotient — **keep** |
| 24 | `not_single_le_pair_natPowerset` | U | 0 citers; witness that union is not a join for Egli–Milner — **keep** |

### 3.5 `Powerdomain/BoundedComplete.lean` — 22 rows

| # | Declaration | Label | Evidence |
| -- | ---------- | ----- | -------- |
| 1 | `mem_sUnion_coe_iff` | S | 453, 456, 458 |
| 2 | `exists_isLUB_of_bddAbove_idealCompletion` | S | `lem13_hoare` (197), `lem13_smyth` (326) |
| 3 | `hoare_exists_isLUB_pair` | S | `lem13_hoare` (197), `instBoundedCompleteHoare` (208) |
| 4 | `lem13_hoare` | **W** | Lemma 13's `D♭` conjunct §4.5. Carries `[Domain α]` **and** `[BoundedComplete α]`; **neither is consumed** — kernel-checked in `Audit/Powerdomains.lean`. Its docstring records the second, not the first. **Weaken, do not delete** |
| 5 | `le_joinCompact_left` | S | `smyth_exists_isLUB_pair` (310) |
| 6 | `le_joinCompact_right` | S | 313 |
| 7 | `joinCompact_le` | S | 303 |
| 8 | `mem_smythJoin` | S | 302, 309, 312 |
| 9 | `smyth_exists_isLUB_pair` | S | `lem13_smyth` (326), `instBoundedCompleteSmyth` (334) |
| 10 | `lem13_smyth` | **W** | Lemma 13's `D♯` conjunct §4.5. Carries `[Domain α]`, **not consumed** — kernel-checked. Its docstring asserts `[Domain α]` "is what makes `Basis α` a countable pre-order"; `Smyth.Powerdomain`'s measured signature takes only `[CompletePartialOrder α]`. `[BoundedComplete α]` **is** consumed. **Weaken, do not delete** |
| 11 | `k0_le_k01` | S | `bddAbove_hoareWitness` (441) |
| 12 | `k1_le_k01` | S | 442 |
| 13 | `not_k0_le_k1` | S | `not_upperBound_of_le_hoarePt` (434) |
| 14 | `not_k1_le_k0` | S | 431 |
| 15 | `not_k0_le_bot` | S | `not_hoarePt_k0_le_bot` (411) |
| 16 | `hoarePt_le_hoarePt` | S | 441, 442 |
| 17 | `not_hoarePt_k0_le_bot` | S | `sSup_hoareWitness_ne_bot` (479) |
| 18 | `not_upperBound_of_le_hoarePt` | S | 460, 461 |
| 19 | `bddAbove_hoareWitness` | S | `isLUB_sSup_hoareWitness` (469) |
| 20 | `not_isIdeal_sUnion_hoareWitness` | U | 0 citers; the record of the pre-r0032 defect — **keep**, it is the evidence the repair was needed |
| 21 | `isLUB_sSup_hoareWitness` | S | `sSup_hoareWitness_ne_bot` (477) |
| 22 | `sSup_hoareWitness_ne_bot` | U | 0 citers; the record that the repaired `sSup` does not return `⊥` — **keep** |

`instBoundedCompleteHoare` and `instBoundedCompleteSmyth` are `instance`s, not
`theorem`/`lemma`, so they are outside the 197 and have no row. The first
carries an unconsumed `[Domain α]`; see §4.

### 3.6 `Powerdomain/Universal.lean` — 20 rows

| # | Declaration | Label | Evidence |
| -- | ---------- | ----- | -------- |
| 1 | `repOf_apply` | A | `@[simp]`; 0 citers |
| 2 | `isClosure_repOf` | S | `isRepresentable_prod` (397), `CombinatorRep:125,160,178` |
| 3 | `fn_mem_range_of_mem_range_repOf` | S | `repRangeOrderIso` (156) |
| 4 | `gr_mem_range_repOf` | S | 157 |
| 5 | `gr_fn_of_mem_range_repOf` | S | 158 |
| 6 | `scottContinuous_repOf` | S | `isRepresentable_prod` (398), `CombinatorRep:113` |
| 7 | `compacts_prod` | S | `domain_prod` (243), `isAlgebraic_prod`'s route (236) |
| 8 | `compactsBelow_prod` | S | `isAlgebraic_prod` (224, 232) |
| 9 | `isAlgebraic_prod` | S | `domain_prod` (241), `PRepFun:881,927` |
| 10 | `domain_prod` | S | `isRepresentable_prod` (394), `LemThirty:326,328,351` |
| 11 | `isLUB_sSup_prod_set` | S | `isRepresentable_prod` (395) |
| 12 | `prodMap_apply` | A | `@[simp]`; 0 citers |
| 13 | `isClosure_prodMap` | S | 397, 398; `CombinatorRep:283` |
| 14 | `prodMap_mono` | S | 399; `CombinatorRep:286` |
| 15 | `isLUB_prodMap_of_isLUB` | S | 399; `CombinatorRep:292` |
| 16 | `fst_mem_range_of_mem_range_prodMap` | S | `prodRangeOrderIso` (359) |
| 17 | `snd_mem_range_of_mem_range_prodMap` | S | 360 |
| 18 | `mk_mem_range_prodMap` | S | 361 |
| 19 | `isRepresentable_prod` | **P** | §7.1, the paragraph after Lemma 23 — "*We leave for the reader the demonstration that this makes sense and `R×` represents the product operator*". Consumed by `Universality:480` (`thm25 (Set ℕ) isRepresentable_prod lem23`) |
| 20 | `recursiveDomain_prod` | U | 0 citers. `Universality:479–480` already derives `Iso D (prodCpo D D)` through `thm25`, so this is an end-to-end shape check, not a step — **keep as a check, or fold into an `example`** |

### 3.7 `ContinuousAlgebra.lean` — 62 rows

| # | Declaration | Label | Evidence |
| -- | ---------- | ----- | -------- |
| 1 | `scottContinuous_op` | S | `op_mono` (126), `isLUB_op_image` (152) |
| 2 | `op_mono` | S | 128, 130, 203, 210, 495, 920 |
| 3 | `op_mono_left` | U | 0 citers, no attribute; one-line corollary of `op_mono` — **speculative API** |
| 4 | `op_mono_right` | U | 0 citers, no attribute — **speculative API** |
| 5 | `isLUB_op_image` | S | `isHom_ext` (921) |
| 6 | `op_le_right` | S | `fold_le_of_mem` (393) |
| 7 | `le_op` | S | `le_fold_of_forall` (401) |
| 8 | `right_le_op` | S | `le_fold_of_mem` (368) |
| 9 | `op_le` | S | `fold_le_of_forall` (376) |
| 10 | `ofAlg_toAlg` | A | `@[simp]`, `rfl`; 0 citers |
| 11 | `toAlg_ofAlg` | A | `@[simp]`, `rfl`; 0 citers |
| 12 | `algOrder_le_def` | U | `Iff.rfl`, no attribute, 0 citers |
| 13 | `ofAlg_sup` | A | `@[simp]`, `rfl`; 0 citers |
| 14 | `fold_proof_irrel` | U | mentioned only in `fold`'s own docstring (284); 0 proof citers. Records that `fold` does not depend on the `Finset.Nonempty` proof — **keep as documentation, or fold into an `example`** |
| 15 | `fold_congr` | S | 489, 493, 883, 888 |
| 16 | `fold_singleton` | A | `@[simp]`; 889, 973 |
| 17 | `fold_union` | S | 488, 492, 882 |
| 18 | `fold_image` | S | `fold_le_fold_of_convex` (488, 492) |
| 19 | `fold_le_fold` | S | 496, 497 |
| 20 | `fold_cons` | S | 365, 375, 390, 400, 954, 981 |
| 21 | `le_fold_of_mem` | S | `fold_le_fold_of_hoare` (437) |
| 22 | `fold_le_of_forall` | S | 435 |
| 23 | `fold_le_of_mem` | S | `fold_le_fold_of_smyth` (452) |
| 24 | `le_fold_of_forall` | S | 450 |
| 25 | `fold_le_fold_of_hoare` | S | `thm12_hoare` (1083) |
| 26 | `fold_le_fold_of_smyth` | S | `thm12_smyth` (1124) |
| 27 | `fold_le_fold_of_convex` | S | `thm12_plotkin` (1188) |
| 28 | `directedOn_principal_image` | S | `eq_idealExtend` (598) |
| 29 | `isLUB_principal_image` | S | 598 |
| 30 | `directedOn_image_of_monotone` | S | 552, 922 |
| 31 | `isLUB_idealExtend` | S | 558, 563, 564, 575, 913–915, 934 |
| 32 | `idealExtend_principal` | A | `@[simp]`; sole named citer is `ext_principal` (899), itself row 53's `D` |
| 33 | `monotone_idealExtend` | S | `scottContinuous_idealExtend` (577) |
| 34 | `scottContinuous_idealExtend` | S | `scottContinuous_ext` (904) |
| 35 | `eq_idealExtend` | S | `thm12` (1002) |
| 36 | `toFinset_union` | A | `@[simp]`; 883, 979 |
| 37 | `union_self` | S | `instIsSemilatticeIdealCompletion` (773, 775) |
| 38 | `union_comm'` | S | 754, 756 |
| 39 | `union_assoc'` | S | 762, 766 |
| 40 | `ofFinset_toFinset` | S | `principal_eq_fold_unit` (982) |
| 41 | `isIdeal_opSet` | S | `instBinopIdealCompletion` (712, 719, 720) |
| 42 | `mem_op` | A | `@[simp]`, `Iff.rfl`; 0 citers |
| 43 | `principal_op_principal` | S | `principal_eq_fold_unit` (981) |
| 44 | `isUpper_of_union_le` | S | `instIsUpperSmyth` (1115) |
| 45 | `isLower_of_le_union` | S | `instIsLowerHoare` (1070) |
| 46 | `isIdeal_unitSet` | S | `unit` (837) |
| 47 | `mem_unit` | A | `@[simp]`, `Iff.rfl`; 0 citers |
| 48 | `unit_coe_compact` | S | `principal_eq_fold_unit` (973, 981) |
| 49 | `monotone_unit` | S | `scottContinuous_unit` (863) |
| 50 | `scottContinuous_unit` | **P** | §5.3's diagram — `{|·|} : D → D♮` is the continuous left leg. 0 proof citers, terminal by design (`thm12`'s uniqueness quantifies over continuity of `h`, not of `unit`) |
| 51 | `foldGen_union` | S | `isHom_ext` (919, 926) |
| 52 | `foldGen_singleton` | A | `@[simp]`; `ext_unit` (936, 940) |
| 53 | `ext_principal` | **D** | `rfl`-equal to `idealExtend_principal` at `g := foldGen f` — kernel-checked, pair 5; 0 citers |
| 54 | `scottContinuous_ext` | S | `isHom_ext` (912) |
| 55 | `isHom_ext` | S | `thm12` (1000) |
| 56 | `ext_unit` | S | `thm12` (1000) |
| 57 | `IsHom.map_fold` | S | `thm12` (1005) |
| 58 | `principal_eq_fold_unit` | S | `thm12` (1005) |
| 59 | `thm12` | **P** | Theorem 12 §5.3, generic in the carrier — `∃!` homomorphism completing the diagram |
| 60 | `thm12_hoare` | **P** | Theorem 12 at `D♭` under `T♭` — the paper's "*still holds when `D♮` and `T♮` are replaced by … `D♭` and `T♭`*" |
| 61 | `thm12_smyth` | **P** | Theorem 12 at `D♯` under `T♯` |
| 62 | `thm12_plotkin` | **P** | Theorem 12 proper — `D♮` under `T♮` |

## 4. The `W` list — three over-strength hypotheses, all kernel-checked

The orchestrator's brief asked whether `ContinuousAlgebra` "still *states* the
stronger form anywhere" of r0034's finding that `[IsAlgebraic D]` is the whole
hypothesis of Theorem 12 and countability of `K(D)` is never used. **It does
not.** Measured signatures:

    thm12         : … [IsAlgebraic D] … [FinSets ↥(compacts D) A] …
    thm12_hoare   : … [IsAlgebraic D] … [IsLower E] …
    thm12_smyth   : … [IsAlgebraic D] … [IsUpper E] …
    thm12_plotkin : … [IsAlgebraic D] … [IsSemilattice E] …

No `[Domain D]` occurs in any of the four. r0034's `W` finding was applied in
full, and `ContinuousAlgebra.lean` contributes **zero** `W` rows despite being
the module the brief flagged as the likeliest source. Its 62 theorems for
Theorem 12's 6 properties break down as 5 `P`, 43 `S`, 9 `A`, 4 `U`, 1 `D` — the
`S` mass is the fold (`Finset.sup'` in the algebraic order, 13 lemmas), the
ideal-completion universal property (8), and the three `fold_le_fold_of_*`
monotonicity results that are the one non-generic input each theory supplies.
That is support for a proof, not surplus.

The three over-strength findings are all in `BoundedComplete.lean`, and all trace
to one false premise about `Hoare.Powerdomain`'s signature.

| # | Declaration | Kind | Unconsumed hypothesis | Weaker statement that serves | Consumer |
| -- | ---------- | ---- | --------------------- | ---------------------------- | -------- |
| 1 | `lem13_hoare` | theorem (`W` row) | `[Domain α]` **and** `[BoundedComplete α]` | drop both: `∀ α [CompletePartialOrder α] (S : Set (Hoare.Powerdomain α)), BddAbove S → ∃ I, IsLUB S I` | none in the development; it is a terminal paper statement |
| 2 | `lem13_smyth` | theorem (`W` row) | `[Domain α]` | drop it; keep `[BoundedComplete α]`, which `smyth_exists_isLUB_pair` genuinely spends | none; terminal |
| 3 | `instBoundedCompleteHoare` | `instance` (not in the 197) | `[Domain α]` | `∀ α [CompletePartialOrder α], BoundedComplete (Hoare.Powerdomain α)` | `isLUB_sSup_hoareWitness` (`BoundedComplete:469`), by typeclass resolution |

Each row is discharged by an `example` in
`ScottDomains/Audit/Powerdomains.lean` that re-runs the declaration's own proof
term at the weakened signature. All three elaborate.

Row 3 is the one that changes behaviour rather than only wording. As an
`instance`, `[Domain α]` restricts when `BoundedComplete (Hoare.Powerdomain α)`
is found at all: any goal about `D♭` over a cpo that is algebraic but not known
countable will fail to resolve it. `instBoundedCompleteSmyth` already omits
`[Domain α]`, so the two sibling instances disagree on a hypothesis neither
needs.

Recommended action: delete `[Domain α]` from all three, and `[BoundedComplete α]`
from `lem13_hoare` — or, if the paper's wording is to be preserved on the two
`lem13_*`, add the honest note to `lem13_smyth`'s docstring that `[Domain α]`
is unconsumed, matching what `lem13_hoare`'s docstring already does for
`[BoundedComplete α]`. Correct `instBoundedCompleteHoare`'s docstring either way:
its stated reason is measurably false.

## 5. The `U` list — 20 rows, two populations

The 20 `U` rows split cleanly, and the two halves take opposite actions.

### 5.1 Nondegeneracy witnesses — 12 rows, keep

Each proves that a definition is not the degenerate thing it could be mistaken
for. None is cited, and none should be: a witness is terminal by construction.
r0020's population table has no slot for these, which is why the raw `U` rate
over-reads.

| # | Declaration | Module | What it rules out |
| -- | ---------- | ------ | ----------------- |
| 1 | `Hoare.Pf.not_isPartialOrder` | Hoare | `⊑♭` collapsing to `⊆`, which would make Theorem 11's pre-order generality unnecessary |
| 2 | `Smyth.finsetLE_empty` | Smyth | `∅` being a bottom for `⊑♯` — it is a **top** |
| 3 | `Smyth.not_finsetLE_empty` | Smyth | the other half of the same |
| 4 | `Smyth.Basis.exists_le_le_ne` | Smyth | `⊑♯` being antisymmetric |
| 5 | `Smyth.Basis.bot_eq_singleton_bot` | Smyth | the bottom being anything but `{⊥}` |
| 6 | `Plotkin.exists_ne_principal_eq` | Plotkin | the convex quotient having to be taken by hand — the ideal completion already does it |
| 7 | `Plotkin.not_single_le_pair_natPowerset` | Plotkin | union being a join for Egli–Milner |
| 8 | `PowerdomainBC.not_isIdeal_sUnion_hoareWitness` | BoundedComplete | the pre-r0032 `idealSup` guard having held on the r0031 witness |
| 9 | `PowerdomainBC.sSup_hoareWitness_ne_bot` | BoundedComplete | the repaired `sSup` returning the old `⊥` |
| 10 | `PowerdomainRep.recursiveDomain_prod` | Universal | `isRepresentable_prod` having the wrong shape for `thm21` |
| 11 | `ContinuousAlgebra.fold_proof_irrel` | ContinuousAlgebra | `fold` depending on the nonemptiness proof |
| 12 | `IdealCompletion.le_iff_subset` | IdealCompletion | (weakest of the twelve — it records that the order on ideals is inclusion, which the `SetLike`-derived `PartialOrder` makes `Iff.rfl`) |

Rows 1–11 are load-bearing evidence in the r0020 sense and should be kept. Row 12
is borderline and could equally sit in §5.2. If the orchestrator wants a single
number, the defensible reading is that rows 1–11 are **keep** and everything else
`U` is reviewable.

Rows 10 and 11 could be demoted to `example`s, which would remove them from the
theorem count without losing the check — the same move the area already makes 15
times for its instance-resolution and nondegeneracy checks (`IdealCompletion` 3,
`Hoare` 3, `Smyth` 2, `Plotkin` 2, `ContinuousAlgebra` 5), none of which appear
in the 197.

### 5.2 Speculative API — 8 rows, review

Written for a caller that never appeared. This is r0020's population 3 exactly,
and the r0020 action was to comment out in place with a note.

| # | Declaration | Module | Note |
| -- | ---------- | ------ | ---- |
| 1 | `IdealCompletion.mem_genIdeal` | IdealCompletion | `Iff.rfl`; no attribute. `genIdeal`'s three real lemmas (`subset_genIdeal`, `genIdeal_subset`, `genIdeal_eq_sUnion_of_isIdeal`) carry every use |
| 2 | `Smyth.unit_mono` | Smyth | **the sharpest of the eight.** `Smyth.unit` — the η of `D♯` — is defined solely to state this lemma, and both are uncited. `ContinuousAlgebra.unit` is the unit Theorem 12 actually uses, and it is generic over all three powerdomains. This is a superseded, single-powerdomain η |
| 3 | `Plotkin.FinCompacts.le_def` | Plotkin | the only one of the three `le_def`s with no consumer; the Plotkin discharge in `thm12_plotkin` uses `huv.1`/`huv.2` directly |
| 4 | `Plotkin.FinCompacts.le_hoare` | Plotkin | `h.1`; the same projection the discharge inlines |
| 5 | `Plotkin.FinCompacts.le_smyth` | Plotkin | `h.2` |
| 6 | `ContinuousAlgebra.op_mono_left` | ContinuousAlgebra | `op_mono h le_rfl`; every call site uses `op_mono` directly |
| 7 | `ContinuousAlgebra.op_mono_right` | ContinuousAlgebra | `op_mono le_rfl h` |
| 8 | `ContinuousAlgebra.algOrder_le_def` | ContinuousAlgebra | `Iff.rfl`; the algebraic order is only ever used through `SemilatticeSup (AlgOrder E)` |

Rows 3–5 are one finding: `FinCompacts.le` has three unfolding lemmas and zero
consumers of any of them, while the Hoare and Smyth `le_def`s are each consumed
exactly once. **8 of 201 is 4.0%**, against r0020's 3% over ~199 — the same order
of magnitude, on a body that has since grown by a factor of six.

## 6. The `D` list — 5 pairs, all `rfl`-checked

All five are recorded as theorems in `ScottDomains/ScottDomains/Audit/Powerdomains.lean`,
the one `.lean` addition the plan permits. Each is closed by `rfl`: the two proof
terms are definitionally equal, which forces the two types equal.

| # | Duplicate | Already stated by | Citers of the duplicate | Action |
| -- | -------- | ----------------- | ----------------------- | ------ |
| 1 | `Hoare.isCompactElement_iff` | `IdealCompletion.isCompactElement_iff_exists_eq_principal` at `A := Hoare.Pf ↥(compacts D)` | none | remove; the general lemma is already imported wherever this is |
| 2 | `Plotkin.isCompactElement_iff` | the same at `A := Plotkin.FinCompacts D` | none | remove |
| 3 | `Plotkin.compacts_eq_range_principal` | `IdealCompletion.compacts_eq_range_principal` at `A := Plotkin.FinCompacts D` | none | remove |
| 4 | `Smyth.compacts_eq_range_principal` | the same at `A := Smyth.Basis D` | one — `Smyth.powerdomain_isDomain` | inline: make `powerdomain_isDomain` be `IdealCompletion.thm11 (Basis D)`, which is exactly what `Hoare.thm11_hoare` and `Plotkin.isDomain` already are |
| 5 | `ContinuousAlgebra.ext_principal` | `ContinuousAlgebra.idealExtend_principal` at `g := foldGen f` | none | remove; note that this leaves `idealExtend_principal` (`@[simp]`) with no named citer |

Rows 1–4 are one structural finding. Theorem 11's second conjunct is stated at
each of the three orderings, and the three modules route it three different ways:

    Hoare   : thm11_hoare        = IdealCompletion.thm11 (Pf ↥(compacts D))
    Plotkin : isDomain           = IdealCompletion.thm11 (FinCompacts D)
    Smyth   : powerdomain_isDomain = ⟨inferInstance, compacts_eq_range_principal⟩

Hoare and Plotkin each carry an extra uncited restatement anyway
(`isCompactElement_iff`, and Plotkin a second one). Collapsing all three onto
`IdealCompletion.thm11` removes four declarations and leaves the three `P` rows
identical in form — which is what the parallel-implementation design intends.

**Parallel structure that is not duplication**, checked and cleared: the three
`le_def`s state three different relations (Hoare, Smyth, Egli–Milner); the four
`ext` lemmas are on four different carriers; the three antisymmetry-failure
witnesses are about three different relations and cannot share a proof; and the
three `FinSets` instances in `ContinuousAlgebra` §7 present three genuinely
different carriers (a `Finset` subtype, a `structure`, a `Set` subtype).
`ContinuousAlgebra`'s `FinSets` class is the general form that already absorbs
what would otherwise be three copies of the `⋓` construction, Theorem 12 and its
proof — 22 declarations stated once instead of 66. That is the opposite of the
duplication the round is looking for.

## 7. A cross-area `D` the orchestrator must resolve at tier 2

I hold one half and cannot label the other. `Powerdomain/Universal.lean`'s
module docstring states it plainly:

> Everything in this section is `UniversalDomain.lean`'s `repFun`,
> `isClosure_repFun`, `scottContinuous_repClosure` and `repRangeOrderIso` with
> `ScottHom U U` generalized to an arbitrary cpo `V` and `compHom r s`
> generalized to an arbitrary closure `C : V → V`. The proofs are unchanged; only
> the types are wider. … `UniversalDomain.lean` is not edited: `lem23` keeps its
> own specialized copies.

Seven declarations are duplicated across the boundary between my area and
agent5's:

| # | `Powerdomain/Universal.lean` (generic, mine) | `UniversalDomain.lean` (specialized, agent5) | Kind |
| -- | ------------------------------------------ | -------------------------------------------- | ---- |
| 1 | `repOf` | `repFun` (473) | `def` |
| 2 | `isClosure_repOf` | `isClosure_repFun` (491) | theorem |
| 3 | `scottContinuous_repOf` | `scottContinuous_repClosure` (547) | theorem |
| 4 | `fn_mem_range_of_mem_range_repOf` | `fn_mem_range_compHom` (594) | theorem |
| 5 | `gr_mem_range_repOf` | `gr_mem_range_repFun` (602) | theorem |
| 6 | `gr_fn_of_mem_range_repOf` | `gr_fn_of_mem_range` (611) | theorem |
| 7 | `repRangeOrderIso` | `repRangeOrderIso` (618) | `def` |

Row 7 is the case `unused-theorems.sh`'s header warns about: **the same final
name is declared in two namespaces**, so each masks the other's citation count.
My generic versions are cited from `CombinatorRep.lean` and are `S` rows above;
the specialized copies exist only to serve `lem23`, and whether they are `D` is
agent5's measurement, not mine. Instantiating the generic ones at `V := ScottHom U U`
would retire five theorems and two `def`s.

## 8. Two things checked because the brief asked, with the answer

1. **Does anything dead survive the `idealSup` repair in `IdealCompletion`?**
   No. `not_boundedComplete_{hoare,smyth,plotkin}` and
   `not_boundedComplete_of_not_directed_pair` occur in `reports/`, `docs/`,
   `plans/` and one r0032 build log, and in **zero** `.lean` sources. The one
   `.lean` mention is `BoundedComplete.lean:60`, a docstring recording the
   retirement. What replaced them — `not_isIdeal_sUnion_hoareWitness`,
   `isLUB_sSup_hoareWitness`, `sSup_hoareWitness_ne_bot` and their nine
   supporting lemmas — is present, and the three-lemma structure is exactly what
   the repair needs: the old guard still fails on the witness, the new `sSup`
   returns a least upper bound, and that value is not `⊥`. Two of the twelve are
   `U` (terminal witnesses); ten are `S`.

2. **Is `ContinuousAlgebra` the best place to find `U` and `W`?** Measured, no.
   Its rate is 4 `U` and 0 `W` out of 62, **6.5% `U`**, below the area average of
   10.0%. `Powerdomain/Smyth.lean` is the worst at 5 `U` of 16 (**31%**) and
   `Powerdomain/Plotkin.lean` next at 5 of 24 (**21%**). The 62-for-6 ratio the
   brief flagged is explained by the `FinSets` abstraction: one carrier-generic
   Theorem 12 plus three cheap instances, rather than three copies.

## 9. Invariants

Measured after the one permitted `.lean` addition, by `scripts/compile.sh -r r0038`
(log `ScottDomains/logs/compile-20260808-095338.agent4.log`) and `scripts/counts.sh`:

| # | Quantity | Before | After | Note |
| -- | ------- | -----: | ----: | ---- |
| 1 | build | 0 errors | 0 errors | 1224 jobs, `Audit.Powerdomains` built in 1.2 s |
| 2 | `sorry` | 1 in 1 file | 1 in 1 file | `Skeleton/Section6.lean:197` |
| 3 | numbered results | 22 of 29 | 22 of 29 | no result touched |
| 4 | theorems | 1308 | 1313 | +5, the five `D` equivalences |
| 5 | modules | 72 | 73 | +1, `Audit/Powerdomains.lean` |
| 6 | existing `.lean` files modified | — | **0** | `git status`: two untracked additions plus one log |

No existing declaration was edited, renamed, retagged or deleted.
