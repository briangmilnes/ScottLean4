---
round: r0038
from: agent5
to: orchestrator
subject: audit-section-seven
date: 2026-0808-10:12
started: 2026-0808-09:31
finished: 2026-0808-10:12
related:
  - plans/r0038-plan-from-orchestrator-to-orchestrator-theorem-audit.md
  - docs/PropertiesVsTheorems.md
  - ScottDomains/Audit/SectionSeven.lean
---

# r0038 — Audit of `Audit.SectionSeven`: the §7 representability stack

Twelve modules — `UniversalDomain`, `Universality`, `RecursiveDomain`,
`Combinator`, `CombinatorRep`, `Dyadic`, `Atomless`, `PRepresentable`, `PRep`,
`PRepFun`, `PRepSum`, `Lemma28AtU` — 7,820 lines, **400 theorems**.

## 0. Headline measurements

| # | Measurement | Value |
| -- | ---------- | ----- |
| 1 | theorems counted by `module-counts.sh` | 403 |
| 2 | of those, docstring lines miscounted as declarations | 3 |
| 3 | **real theorems audited** | **400** |
| 4 | `@[simp]`-tagged rows | 54 |
| 5 | of those, tags that **never fire anywhere in the development** | **43 (80%)** |
| 6 | rows serving neither a paper property nor a proof of one (`U` + `D` + `W`) | **27, 6.75%** |
| 7 | `A` rows that are additionally cited nowhere and never fire — r0020's "speculative API" | **18, 4.5%** |
| 8 | rows 6 and 7 together, disjoint | **45, 11.25%** |
| 9 | duplicate pairs, kernel-confirmed by `rfl` | 5 |
| 10 | build after the audit | exit 0, 1224 jobs, `sorry` 1 — unchanged |

Rows 6 and 7 are disjoint by construction: `A` was assigned to every `@[simp]`
row and `U`/`D` to none of them, so row 7 counts declarations that the label
column calls API and the measurement calls dead. **For the tier-2 consolidation,
row 8 is the number to carry, not row 6** — 11.25% of this area serves nothing,
against r0020's 3%, and the excess is almost entirely the inert `@[simp]` tags.

Row 6 against r0020's 3% is the number the round asked for: this area runs at
a little over twice r0020's rate, and the excess is concentrated in one module
(`CombinatorRep`, 8 of its 28 rows) and in one systematic defect (43 inert
`@[simp]` tags).

## 1. Three counting artifacts — `counts.sh` over-reports by 3

`counts.sh` and `module-counts.sh` count a line beginning `theorem ` or `lemma `
as a declaration. Three docstring **continuation** lines in this area begin that
way and are counted as theorems:

| # | File:line | The line |
| -- | -------- | -------- |
| 1 | `Combinator.lean:129` | `lemma that makes each "λ inside a fixed point" below cost nothing. -/` |
| 2 | `CombinatorRep.lean:265` | `theorem at `U = P N`, with the pair supplied by Theorem 22. -/` |
| 3 | `PRepFun.lean:449` | `theorem rather than an `instance`, so that it fires only where it is named. -/` |

These are the only three in the whole package (`grep -rnE '^(@\[[^]]*\] )?(theorem|lemma) .*-/$'`
over `ScottDomains/ScottDomains/` returns exactly these). So the development's
headline **1308 is 1305**, and this area's 403 is 400. The fix is a one-word
reflow of each docstring, not a change to the counting rule.

## 2. Per-label totals

| # | Label | Meaning | Count | Share |
| -- | ----- | ------- | ----- | ----- |
| 1 | `P` | states a paper property | 18 | 4.5% |
| 2 | `S` | support, something cites it | 301 | 75.3% |
| 3 | `A` | projection / `simp` API | 54 | 13.5% |
| 4 | `U` | uncited, not a paper property, not API | 21 | 5.3% |
| 5 | `D` | duplicate | 6 | 1.5% |
| 6 | `W` | proved at a strength nothing consumes | 0 | 0% |
| — | | **total** | **400** | |

Per module:

| # | Module | Thms | P | S | A | U | D | W |
| -- | ----- | ---- | - | - | - | - | - | - |
| 1 | `UniversalDomain` | 21 | 2 | 18 | 0 | 1 | 0 | 0 |
| 2 | `Universality` | 22 | 3 | 18 | 0 | 1 | 0 | 0 |
| 3 | `RecursiveDomain` | 14 | 3 | 10 | 1 | 0 | 0 | 0 |
| 4 | `Combinator` | 41 | 2 | 11 | 25 | 3 | 0 | 0 |
| 5 | `CombinatorRep` | 28 | 0 | 18 | 2 | 5 | 3 | 0 |
| 6 | `Dyadic` | 59 | 0 | 47 | 6 | 6 | 0 | 0 |
| 7 | `Atomless` | 56 | 1 | 48 | 6 | 1 | 0 | 0 |
| 8 | `PRepresentable` | 3 | 0 | 1 | 1 | 1 | 0 | 0 |
| 9 | `PRep` | 39 | 0 | 37 | 0 | 2 | 0 | 0 |
| 10 | `PRepFun` | 51 | 0 | 46 | 4 | 0 | 1 | 0 |
| 11 | `PRepSum` | 62 | 4 | 47 | 9 | 0 | 2 | 0 |
| 12 | `Lemma28AtU` | 4 | 3 | 0 | 0 | 1 | 0 | 0 |
| — | **total** | **400** | **18** | **301** | **54** | **21** | **6** | **0** |

`A` was assigned to exactly the 54 `@[simp]`-tagged rows and to nothing else, so
the `A` column and the `simp` column of `module-counts.sh` agree row for row.

### Why `W` is zero

r0032 and r0034 found results proved at strictly stronger hypotheses than
declared. That pattern does not occur here, and the reason is measurable: this
area's four largest modules were written after the `[Domain U]` / `[BoundedComplete U]`
split was already understood, and each records where its hypothesis is spent
(`PRepFun.rep_smash` carries `[Domain U]` alone and says why; `PRep.rep_lift` and
`rep_prod` the same). The nearest miss runs the **other** way:
`Dyadic.thm27` carries `[BoundedComplete D]` that its own proof never uses — it
is `thm27_of_isNormallyRepresented` plus a redundant hypothesis — which makes it
weaker than the theorem beside it rather than stronger. It is uncited, so it is
labelled `U` (row 59 of `Dyadic` below), not `W`.

## 3. The `@[simp]` measurement — 43 of 54 tags are inert

This is the largest single finding, and it is the r0020 pattern at fifteen times
r0020's scale (r0020 found three non-firing tags).

**Method**, and why it edits nothing. The round forbids editing any `.lean`
file, so the experiment runs on copies in the scratch tree, elaborated with
`lake env lean` against the already-built `.olean`s:

- `scripts/a5-simp-firing.sh` copies a module with the leading attribute group
  deleted from its `@[simp] theorem` lines and elaborates the copy, with a
  control run on an unmodified copy first. This answers "does the tag do work
  **inside** the declaring module".
- `scripts/a5-simp-downstream.sh` splices `attribute [-simp] <name>` after the
  imports of each module in the declaring module's **full reverse-dependency
  closure** and elaborates that. Running it over the whole closure answers the
  question for the whole development.

| # | Module | Tags | Fire in-module? | Reverse closure probed | Verdict |
| -- | ----- | ---- | --------------- | ---------------------- | ------- |
| 1 | `Combinator` | 25 | no | ∅ — nothing imports it | **none fires, anywhere** |
| 2 | `Dyadic` | 6 | no | `Atomless`, `PRep`, `PRepFun`, `PRepSum`, `LemThirty`, `Lemma28AtU` | **none fires, anywhere** |
| 3 | `Atomless` | 6 | no | `PRepSum`, `Lemma28AtU` | **none fires, anywhere** |
| 4 | `PRepFun` | 4 | no | `Lemma28AtU` | **none fires, anywhere** |
| 5 | `PRepresentable` | 1 | no | `PRep`, `Colimit`, `PRepFun`, `PRepSum`, `LemThirty`, `Lemma28AtU` | **none fires, anywhere** |
| 6 | `RecursiveDomain` | 1 | no | `Powerdomain/Universal`, `CombinatorRep`, `Universality`, `PRepresentable`, `Combinator`, `PRep`, `Colimit`, `PRepFun`, `PRepSum`, `LemThirty`, `Lemma28AtU` | **none fires, anywhere** |
| 7 | `PRepSum` | 9 | **yes** — 12 errors on removal | — | all 9 load-bearing |
| 8 | `CombinatorRep` | 2 | **yes** — 4 errors on removal | — | both load-bearing |
| — | **total** | **54** | | | **43 inert, 11 firing** |

`Combinator` is the clean case and the plan's own question: it holds 25 tags for
Theorem 26's one property, **nothing imports the module**, and a copy with all 25
attribute groups deleted elaborates with exit 0. So none of those 25 tags has
ever fired, and the module's `simp` density — the highest in the development at
25 of 41 theorems — buys nothing at all.

The 43 inert tags split into two populations, and only the second is dead code:

| # | Population | Count | Action |
| -- | --------- | ----- | ------ |
| 1 | the lemma **is** used, by name, in a `rw`/`simp only` list; only the tag is inert | 25 | drop the `@[simp]`, keep the lemma |
| 2 | the lemma is used nowhere **and** the tag never fires | 18 | r0020's treatment: comment out in place with a note |

Population 2 is the r0020 defect exactly, and it is 18 rows, 4.5% of the area:

| # | Declaration | Module:line |
| -- | ---------- | ----------- |
| 1 | `prodMkHom_apply` | `Combinator:123` |
| 2 | `evalHom_apply` | `Combinator:147` |
| 3 | `postHom_apply` | `Combinator:163` |
| 4 | `preHom_apply` | `Combinator:171` |
| 5 | `postHomHom_apply` | `Combinator:180` |
| 6 | `appU_apply` | `Combinator:262` |
| 7 | `apHom_apply` | `Combinator:268` |
| 8 | `pairHomH_apply` | `Combinator:443` |
| 9 | `U₀.toSet_mk` | `Dyadic:255` |
| 10 | `embHom_apply` | `Dyadic:538` |
| 11 | `projHom_apply` | `Dyadic:602` |
| 12 | `st_zero` | `Atomless:321` |
| 13 | `FpImage_carrier` | `PRepresentable:90` |
| 14 | `pairComp_apply` | `RecursiveDomain:144` |
| 15 | `strictArrowFamily_val` | `PRepFun:506` |
| 16 | `smashEmbed_bot` | `PRepFun:687` |
| 17 | `smashEmbed_coe` | `PRepFun:689` |
| 18 | `smashMap_apply` | `PRepFun:1034` |

Eight of the eighteen are `Combinator`'s bundled-map projections — the toolkit
`_apply` equations written in r0034 for a `simp` set that no proof in the file
ever invokes, since every proof there is `rw`/`exact`.

## 4. The `U` rows — 21

| # | Declaration | Module:line | Why it is here | Recommended |
| -- | ---------- | ----------- | -------------- | ----------- |
| 1 | `thm22_of_isCompactlyGenerated` | `UniversalDomain:218` | Theorem 22 restated in Mathlib's `IsCompactlyGenerated` vocabulary; nothing calls it | keep — it is the bridge a Mathlib user needs; note the fact |
| 2 | `solves_iff_iso` | `Universality:229` | `Iff.rfl` bridging `Recursive.Solves` and `Universality.Iso`; docstring-only | keep, terminal by design |
| 3 | `elem_of_hom₁` | `Combinator:243` | justifies "operations as elements of `D`"; its own docstring says nothing consumes it | keep as evidence, comment the fact |
| 4 | `elem_of_hom₂` | `Combinator:249` | same | same |
| 5 | `thm26_subalgebra` | `Combinator:574` | the subset variant; the paper's hypothesis is *retract*, which `thm26_retract` states | comment out — `thm26_retract` is the paper's sentence |
| 6 | `directedOn_fst_val` | `CombinatorRep:196` | extracted directedness lemma, cited nowhere — see §6 | **keep and generalize**; 28 inline copies exist |
| 7 | `directedOn_snd_val` | `CombinatorRep:204` | same | same |
| 8 | `rep_arrow` | `CombinatorRep:266` | Lemma 28's `→` at the closure reading; superseded by `PRepFun.rep_arrow` | comment out with a note |
| 9 | `rep_prod` | `CombinatorRep:297` | superseded by `PRep.rep_prod` | comment out with a note |
| 10 | `rep_lift` | `CombinatorRep:492` | superseded by `PRep.rep_lift` | comment out with a note |
| 11 | `mem_principal_iff` | `Dyadic:366` | `K(U)` API, cited nowhere | comment out |
| 12 | `compacts_U` | `Dyadic:374` | Theorem 11's second conjunct at `U₀`; cited nowhere | keep, terminal by design |
| 13 | `isCompactElement_iff` | `Dyadic:378` | re-export of `IdealCompletion.isCompactElement_iff_exists_eq_principal` | comment out |
| 14 | `thm11_at_U` | `Dyadic:384` | literally `IdealCompletion.thm11 U₀`; cited nowhere | keep, terminal by design |
| 15 | `emb_mono` | `Dyadic:472` | `Monotone (emb φ)`; every call site uses `emb_le_emb` instead | comment out |
| 16 | `thm27` | `Dyadic:652` | `thm27_of_isNormallyRepresented` plus an unused `[BoundedComplete D]`; the live Theorem 27 is `Atomless.thm27` | keep only if the "where the paragraph was cut" note is what is wanted; otherwise comment out |
| 17 | `psiSet_subset_S` | `Atomless:360` | one-line projection, cited nowhere | comment out |
| 18 | `eq_id_of_mem_Fp_of_mem_Fc` | `PRepresentable:119` | the `Fp ∩ Fc = {id}` measurement; docstring-only | **keep** — it is the evidence that `Fp` and `Fc` are different notions |
| 19 | `smythOp_eq` | `PRep:229` | `rfl` check that `smythOp` agrees with `Smyth.Powerdomain` | **keep** — it is the measurement retiring the "not defined on `Cpo`" claim |
| 20 | `hoareOp_eq` | `PRep:233` | same for Hoare | same |
| 21 | `lemma28AtU_of'` | `Lemma28AtU:87` | the round deliverable; arity 2 is the progress measurement | **keep**, terminal by design |

Of the 21, **11 are recommended for r0020-style comment-out** (rows 5, 8, 9, 10,
11, 13, 15, 17 and, conditionally, 16 — plus rows 3 and 4 if the evidence note is
moved into the docstring). Ten are terminal-by-design or load-bearing evidence
and should stay. So the actionable count in this area is 11 of 400, **2.75%** —
just under r0020's 3%.

## 5. The `D` rows — 6, all five pairs kernel-confirmed

Every `D` claim below is checked by a theorem in
`ScottDomains/Audit/SectionSeven.lean`, the one `.lean` this round permits. Each
is an equality of two proof terms, so it elaborates only if the two propositions
are definitionally equal — proof irrelevance makes the `rfl` trivial *once the
statements are the same type*, which is exactly the content being checked. The
module builds: `lake build ScottDomains.Audit.SectionSeven`, exit 0.

| # | Declaration | Module:line | Duplicate of | Check |
| -- | ---------- | ----------- | ------------ | ----- |
| 1 | `liftRange_mem` | `CombinatorRep:447` | `PRep.liftRange_mem` at `r.val` | `liftRange_mem_pair` |
| 2 | `liftRangeMap_le_iff` | `CombinatorRep:461` | `PRep.liftRangeMap_le_iff` at `r.val` | `liftRangeMap_le_iff_pair` |
| 3 | `liftRangeMap_surjective` | `CombinatorRep:476` | `PRep.liftRangeMap_surjective` at `r.val` | `liftRangeMap_surjective_pair` |
| 4 | `val_ne_bot_of_ne_bot` | `PRepFun:1130` | `PRepSum.val_ne_bot_of_ne_bot` | `val_ne_bot_of_ne_bot_pair` |
| 5 | `orderIso_apply_bot` | `PRepSum:845` | **Mathlib's `OrderIso.map_bot`** | `orderIso_apply_bot_is_mathlib_map_bot` |
| 6 | `isStrict_of_isProjection` | `PRepSum:540` | `ScottHom.IsProjection.map_bot` — a rename, `:= hp.map_bot`; cited nowhere, and every call site writes `hp.map_bot` directly | by inspection of the one-line proof |

Rows 1–3 are the `⊥`-lift range isomorphism built twice. `PRep.lean`'s docstring
records the re-derivation as necessary "since the index type changes"; measured,
it is not — `Combinator.liftFamily r` is *by definition* `Combinator.liftMap r.val`,
so the closure-indexed statements are the `ScottHom`-indexed ones at `r.val`, and
all three equivalences elaborate by `rfl`. `PRep`'s are the general ones, so the
resolution is to delete the specializations, not the generalizations.

Row 5 is a Mathlib lemma re-proved in five lines. It has three uses, all inside
`PRepSum`; replacing them with `OrderIso.map_bot` removes the declaration.

## 6. The duplication that is *not* in the label table: 28 copies of one script

The `D` label covers duplicate **declarations**. This area's larger duplication
is of a **proof script**, and it is invisible to any per-declaration measurement:

    rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩
    obtain ⟨c, hc, hpc, hqc⟩ := hd p hp q hq
    exact ⟨…, ⟨c, hc, rfl⟩, …, …⟩

— "the image of a directed set under a coordinate or a `val` is directed" —
occurs **28 times**: `CombinatorRep` 6, `PRep` 8, `PRepFun` 4, `PRepSum` 10.
The block `have hdfst : DirectedOn (· ≤ ·) (Prod.fst '' d)` alone occurs 5 times.

The sting is that the development already has this extracted as a lemma:
`CombinatorRep.directedOn_fst_val` and `directedOn_snd_val` — rows 6 and 7 of the
`U` table, **cited zero times**. They were written at the `Fc(U)` index in r0034
and every later module re-inlined them at the `Fp(U)` index rather than
generalizing them. Generalizing those two lemmas from
`ClosurePoset U × ClosurePoset U` to an arbitrary subtype index would delete
roughly 84 lines across four modules and turn two `U` rows into `S` rows.

`PRepFun` carries the same defect inside one file: `exists_nonBot_of_isLUB`
(line 843) is the extracted form of a block still inlined verbatim at lines
777–790 inside `scottContinuous_smashCollapse`.

## 7. Question 1 — is `CombinatorRep` still needed?

**Answer: reduce it to four declarations. The counterexample the plan protects is
not one of its 29 theorems — it is 30 lines of module docstring.**

### 7.1 The counterexample is prose, not a theorem

The `⊗`/`⊕` three-chain counterexample lives at `CombinatorRep.lean:504–533`,
inside the `/-! … -/` block headed "`⊗` (smash) and `⊕` (coalesced sum): the
closure reading is **false**". Its own text says so: "here is a counterexample —
**a hand computation, not Lean-checked**." It occupies **0 of the 28 real
theorems**. So the evidence the plan calls load-bearing survives any reduction of
the theorem list, and can be moved verbatim into any surviving module.

### 7.2 What the rest of the development actually consumes

`CombinatorRep.lean` is imported by exactly one module (`PRep.lean`, line 2), and
`grep` over `PRep`, `PRepFun`, `PRepSum`, `Lemma28AtU` and `LemThirty` for the
`Combinator.` namespace returns exactly four declarations in code positions:

| # | Declaration | Kind | Used by |
| -- | ---------- | ---- | ------- |
| 1 | `liftMap` | `def` | `PRep.isProjection_liftMap`, `liftRange_mem`, `liftRangeMap`, `liftRangeOrderIso`, `domain_range_liftMap`, `liftFamily` |
| 2 | `scottContinuous_liftFun` | theorem | the continuity field of `liftMap` |
| 3 | `liftMap_mono` | theorem | `PRep.liftFamily_mono` |
| 4 | `isLUB_coe_image` | theorem | `PRep.isLUB_liftFamily` |

Everything else in the file is consumed only by the file itself, and every
internal citation chain terminates at one of `rep_arrow`, `rep_prod`, `rep_lift`
— the three theorems that are cited nowhere, because r0037 kernel-checked
(`PRep.gr_fn_eq_of_both`, `PRep.orderIsoOfBothPairs`) that the closure pair and
the projection pair are simultaneously satisfiable only when `U ≅ V`.

### 7.3 The 28 rows, sorted into the plan's three buckets

| # | Bucket | Count | Declarations |
| -- | ----- | ----- | ------------ |
| 1 | **Evidence — keep** | 0 theorems + the docstring | the `⊗`/`⊕` counterexample and the four-operator obstruction table, lines 498–568 |
| 2 | **Live — keep** | 3 | `scottContinuous_liftFun`, `liftMap_mono`, `isLUB_coe_image` (plus the `def liftMap`) |
| 3 | **Superseded — comment out** | 5 `U` + 3 `D` = 8 | `rep_arrow`, `rep_prod`, `rep_lift`, `directedOn_fst_val`, `directedOn_snd_val`, `liftRange_mem`, `liftRangeMap_le_iff`, `liftRangeMap_surjective` |
| 4 | **Neither — support for bucket 3** | 17 | `scottContinuous_repFamily`, `isRepresentable_of_retracts`, `isRepresentable₂_of_retracts`, `isLUB_fst_val`, `isLUB_snd_val`, `isClosure_arrowFamily`, `arrowFamily_mono`, `isLUB_arrowFamily`, `isClosure_prodFamily`, `prodFamily_mono`, `isLUB_prodFamily`, `isClosure_liftMap`, `isClosure_liftFamily`, `liftFamily_mono`, `isLUB_liftFamily`, `liftMap_bot`, `liftMap_coe` |

Bucket 4 is the honest awkward case: each row has a citer, so none is `U`, but
the citer is in bucket 3. They fall with `rep_arrow`/`rep_prod`/`rep_lift` or
they stay with them — the decision is one decision, not seventeen. `liftMap_bot`
and `liftMap_coe` are the two `@[simp]` tags in this area that **do** fire, so
they stay under either choice.

**Recommendation.** Reduce `CombinatorRep.lean` to the four declarations of
bucket 2 plus the docstring of bucket 1, and comment out buckets 3 and 4 in
place with a note — 25 of 28 theorems. The file is then what its evidential value
actually is: the record that the closure reading of Lemma 28 was tried, the
counterexample that refuted it, and the three lifting facts `PRep` reuses.

Two dissenting considerations, stated so the orchestrator can weigh them:

1. `isRepresentable_of_retracts` / `isRepresentable₂_of_retracts` are the
   **`Fc`-notion** representation scheme, and `UniversalDomain.lem23` is a live
   `P` row at that notion. If §7's closure track is to stay statable in the
   abstract, those two and their support are the abstraction of `lem23` and
   should survive. Nothing currently uses them that way.
2. Commenting out bucket 4 removes the only `Fc`-side instances of
   `isLUB_fst_val` / `isLUB_snd_val`, which §6 argues should instead be
   *generalized* to serve the 28 inline copies. Generalize first, then reduce.

## 8. Question 2 — do `PRep`, `PRepFun`, `PRepSum`, `Lemma28AtU` duplicate each other?

**Answer: no, on the machinery the plan suspected — and yes, on two small
declarations plus one Mathlib lemma. The plan's hypothesis is refuted by
measurement.**

The plan's hypothesis was that "each had to build retraction-pair and
`Domain`-of-image machinery, and that is where the same lemma may exist three
times." Measured, each of those instruments is declared **once**, in `PRep`, and
consumed by the other three:

| # | Instrument | Declared | Uses in `PRepFun` | Uses in `PRepSum` | Uses in `Lemma28AtU` |
| -- | --------- | -------- | ----------------- | ----------------- | -------------------- |
| 1 | `isFinitaryProjection_repOf` — the `Fp` obligation reduced to `Domain (im C)` | `PRep:663` | 3 | 2 | 0 |
| 2 | `domain_orderIso` — `Domain` transports along `≃o` | `PRep:620` | 2 | 2 | 0 |
| 3 | `isPRepresentable₂_of_repFamily` — the paper's `R₊ = Ψ ∘ (r+s) ∘ Φ` scheme | `PRep:756` | 3 | 2 | 0 |
| 4 | `isLUB_val_image_of_isLUB_fp'` — least upper bounds in `Fp(U)` are pointwise | `PRep:535` | 2 | 2 | 0 |
| 5 | `isFinitaryProjection_sSup` — the keystone the notion change costs | `PRep:463` | 0 (via 4) | 0 (via 4) | 0 |
| 6 | `pairAtU` — Theorem 27 in `PRep`'s coordinates | `PRepSum:130` | 0 | 4 | 3 |

There is exactly one representation scheme, one `Domain`-transport lemma and one
retraction-pair transposition in the stack. The division of labour is by
**operator**, not by machinery, and it is clean: `PRep` holds the scheme and the
two conjuncts (`×`, `(·)⊥`) that need no new closure property; `PRepFun` holds
`→`, `⇸`, `⊗` and the two closure properties they needed (`strictHomDomain`,
`smashDomain`, neither of which existed before r0037); `PRepSum` holds `+`, `⊕`,
the coalesced-sum `Domain` and the instantiation at `Dyadic.U`; `Lemma28AtU` is
the four-line join. No conjunct is proved twice.

What **is** duplicated is three small things, all confirmed in §5:

1. `PRepFun.val_ne_bot_of_ne_bot` = `PRepSum.val_ne_bot_of_ne_bot` — one is the
   other at `FpImage a`. Two agents in two worktrees each needed "a non-`⊥` point
   of `im(p)` has a non-`⊥` value" and each wrote it.
2. `PRepSum.projCpo` (a `def`, so outside the theorem table) is
   `BifiniteUniversal.FpImage` under a second name — the same
   `⟨↥(Set.range ⇑p), hp.rangeCompletePartialOrder⟩`. Duplicate 1 is the visible
   symptom of this one: two names for one cpo produced two copies of its API.
3. `PRepSum.orderIso_apply_bot` = Mathlib's `OrderIso.map_bot`.

**Recommendation.** Delete `PRepSum.projCpo` in favour of
`BifiniteUniversal.FpImage`, which collapses duplicates 1 and 2 together; replace
the three uses of `orderIso_apply_bot` with `OrderIso.map_bot`; delete
`isStrict_of_isProjection`, an unused alias of `IsProjection.map_bot`. Net: three
declarations and one `def` removed, no proof changed. The plan's suspicion of
triplicated machinery is not borne out and should be recorded as answered.

## 9. Per-declaration table — 400 rows

Line numbers are as of commit `af05042`. The three docstring artifacts of §1 are
listed and marked `—` rather than silently dropped.

### 9.1 `UniversalDomain` — 21

| # | Declaration | Line | Label | Evidence |
| -- | ---------- | ---- | ----- | -------- |
| 1 | `monotone_enumSup` | 116 | S | `scottContinuous_enumSup` |
| 2 | `scottContinuous_enumSup` | 122 | S | `thm22` |
| 3 | `scottContinuous_enumIndex` | 141 | S | `thm22` |
| 4 | `thm22` | 159 | **P** | §7, Theorem 22 — closure `r : P N → L` for a countably based algebraic lattice |
| 5 | `isAlgebraic_of_isCompactlyGenerated` | 204 | S | `thm22_of_isCompactlyGenerated` |
| 6 | `thm22_of_isCompactlyGenerated` | 218 | **U** | 0 uses; Theorem 22 in Mathlib's vocabulary |
| 7 | `IsClosure.scottContinuous_val` | 249 | S | `restrictHom:649`, `extendHom:657` |
| 8 | `IsClosure.scottContinuous_corestrict` | 267 | S | `restrictHom:650`, `extendHom:656` |
| 9 | `isLUB_val_image_of_isLUB` | 371 | S | `scottContinuous_repClosure`; also `CombinatorRep`, `PRepFun`, `ClosureProperties/StrictFunction` |
| 10 | `scottContinuous_pointwiseSup_set` | 405 | S | `isLUB_sSup_scottHom_set` |
| 11 | `isLUB_sSup_scottHom_set` | 412 | S | `lem23` |
| 12 | `isClosure_compHom` | 437 | S | `isClosure_repFun`, `CombinatorRep.isClosure_arrowFamily` |
| 13 | `compHom_mono` | 448 | S | `isLUB_compHom_of_isLUB`, `PRepFun.arrowFamily_mono` |
| 14 | `isClosure_repFun` | 491 | S | `lem23`, `scottContinuous_repClosure` |
| 15 | `isLUB_compHom_of_isLUB` | 508 | S | `scottContinuous_repClosure`, `CombinatorRep.isLUB_arrowFamily` |
| 16 | `scottContinuous_repClosure` | 547 | S | `lem23` |
| 17 | `fn_mem_range_compHom` | 594 | S | `repRangeOrderIso` |
| 18 | `gr_mem_range_repFun` | 602 | S | `repRangeOrderIso` |
| 19 | `gr_fn_of_mem_range` | 611 | S | `repRangeOrderIso` |
| 20 | `extendHom_mem_range` | 662 | S | `evidentOrderIso` |
| 21 | `lem23` | 712 | **P** | §7, Lemma 23 — `→` representable over `P N` |

### 9.2 `Universality` — 22

| # | Declaration | Line | Label | Evidence |
| -- | ---------- | ---- | ----- | -------- |
| 1 | `scottContinuous_orderIso` | 114 | S | `scottHomOrderIso`, `LambdaModel.ofOrderIso` |
| 2 | `scottContinuous_pairConst` | 122 | S | `isRepresentable_selfProdSquare` |
| 3 | `scottContinuous_pairConstRight` | 133 | S | `isRepresentable_funSpaceConst` |
| 4 | `nontrivial_of_orderIso` | 183 | S | `Iso.nontrivial` |
| 5 | `nontrivial_scottHom` | 193 | S | `lem24` |
| 6 | `solves_iff_iso` | 229 | **U** | 0 uses; `Iff.rfl` bridge, docstring-only |
| 7 | `Iso.refl` | 236 | S | `lem24`, `isRepresentable_funSpaceConst` |
| 8 | `Iso.symm` | 238 | S | `thm25` |
| 9 | `Iso.trans` | 240 | S | `IsClosureOf.of_iso`, `thm25` |
| 10 | `Iso.prodCongr` | 244 | S | `thm25` |
| 11 | `Iso.funSpaceCongr` | 248 | S | `thm25` (3 uses) |
| 12 | `Iso.nontrivial` | 253 | S | `lem24` |
| 13 | `IsClosureOf.of_iso` | 261 | S | `thm25_isUniversal` |
| 14 | `iso_funSpace_prod` | 272 | S | `thm25` |
| 15 | `iso_curry` | 277 | S | `thm25` |
| 16 | `thm21_image` | 314 | S | `lem24` (2 uses) |
| 17 | `isRepresentable_selfProdSquare` | 340 | S | `lem24` |
| 18 | `isRepresentable_funSpaceConst` | 360 | S | `lem24` |
| 19 | `lem24` | 394 | **P** | §7.2, Lemma 24 |
| 20 | `thm25` | 446 | **P** | §7.2, Theorem 25 |
| 21 | `thm25_powerset` | 477 | **P** | §7.2 prose: "take `U` in the theorem to be `P N`" |
| 22 | `thm25_isUniversal` | 497 | **U** | 0 uses; `thm25_powerset` repackaged as `IsUniversal` |

### 9.3 `RecursiveDomain` — 14

| # | Declaration | Line | Label | Evidence |
| -- | ---------- | ---- | ----- | -------- |
| 1 | `pairComp_apply` | 144 | **A** | `@[simp]`; 0 explicit uses; tag never fires (closure of 11 modules probed) |
| 2 | `isClosure_pairComp` | 148 | S | `IsClosureOf.of_isClosurePair` |
| 3 | `mem_range_pairComp` | 157 | S | `pairCompOrderIso` |
| 4 | `IsClosureOf.of_isClosurePair` | 184 | S | `IsUniversal.of_retract` |
| 5 | `IsUniversal.of_retract` | 191 | S | `powersetCpo_isUniversal` |
| 6 | `powersetCpo_isUniversalRetract` | 217 | S | `powersetCpo_isUniversal` |
| 7 | `powersetCpo_isUniversal` | 225 | **P** | §7 prose: "structures such as `P N` are often referred to as universal domains" |
| 8 | `idClosure_le` | 254 | S | `closureCpo` |
| 9 | `directedOn_insert_id` | 257 | S | `closureCpo` |
| 10 | `exists_fixedPoint` | 317 | S | `thm21`, `Universality.thm21_image` |
| 11 | `thm21` | 336 | **P** | §7.1, Theorem 21 |
| 12 | `scottContinuous_diag` | 354 | S | `IsRepresentable₂.diag`, `isRepresentable_selfProdSquare` |
| 13 | `IsRepresentable₂.diag` | 365 | S | `recursiveDomain_funSpace`, `Powerdomain/Universal` |
| 14 | `recursiveDomain_funSpace` | 384 | **P** | §7.2 prose: a cpo `D` with `D ≅ D → D` |

### 9.4 `Combinator` — 41 (+1 artifact)

All 25 `@[simp]` rows are `A` and **none of the 25 tags fires** — the module is a
leaf and a copy with every attribute group deleted elaborates with exit 0.

| # | Declaration | Line | Label | Evidence |
| -- | ---------- | ---- | ----- | -------- |
| 1 | `comp_apply` | 115 | A | `@[simp]`, inert; 3 uses by name |
| 2 | `prodMkHom_apply` | 123 | A | `@[simp]`, inert; **0 uses** |
| — | *(docstring line)* | 129 | — | counting artifact, §1 |
| 3 | `scottContinuous_of_pointwise` | 130 | S | 8 uses (`constHom`, `postHom`, `preHom`, `postHomHom`, `sMid`, `sElem`, `pairHomH`) |
| 4 | `evalHom_apply` | 147 | A | `@[simp]`, inert; **0 uses** |
| 5 | `constHom_apply` | 154 | A | `@[simp]`, inert; 1 use (`kElem_apply`) |
| 6 | `postHom_apply` | 163 | A | `@[simp]`, inert; **0 uses** |
| 7 | `preHom_apply` | 171 | A | `@[simp]`, inert; **0 uses** |
| 8 | `postHomHom_apply` | 180 | A | `@[simp]`, inert; **0 uses** |
| 9 | `iterApp_nil` | 237 | A | `@[simp]`, inert; 2 uses |
| 10 | `iterApp_cons` | 239 | A | `@[simp]`, inert; 6 uses |
| 11 | `elem_of_hom₁` | 243 | **U** | 0 uses; its docstring says nothing consumes it |
| 12 | `elem_of_hom₂` | 249 | **U** | 0 uses; same |
| 13 | `appU_apply` | 262 | A | `@[simp]`, inert; **0 uses** |
| 14 | `apHom_apply` | 268 | A | `@[simp]`, inert; **0 uses** |
| 15 | `kElem_apply` | 274 | A | `@[simp]`, inert; 1 use (`bComb_apply`) |
| 16 | `sInner_apply` | 283 | A | `@[simp]`, inert; 1 use (`sElem_apply`) |
| 17 | `sMid_apply` | 292 | A | `@[simp]`, inert; 1 use (`sElem_apply`) |
| 18 | `sElem_apply` | 302 | A | `@[simp]`, inert; 1 use (`bComb_apply`) |
| 19 | `combEval_ap` | 352 | A | `@[simp]`, inert; 2 uses |
| 20 | `combEval_fstC_apply` | 355 | A | `@[simp]`, inert; 1 use |
| 21 | `combEval_sndC_apply` | 358 | A | `@[simp]`, inert; 1 use |
| 22 | `bComb_apply` | 361 | A | `@[simp]`, inert; 1 use |
| 23 | `appFst_apply` | 384 | A | `@[simp]`, inert; 1 use |
| 24 | `WHom_zero` | 395 | A | `@[simp]`, inert; 1 use |
| 25 | `WHom_succ` | 397 | A | `@[simp]`, inert; 1 use |
| 26 | `iterApp_WHom` | 404 | S | `thm26` |
| 27 | `slotHom_apply` | 431 | A | `@[simp]`, inert; 1 use |
| 28 | `pairHomH_apply` | 443 | A | `@[simp]`, inert; **0 uses** |
| 29 | `tailHom_succ` | 456 | S | `sndIter_tailHom`, `fst_sndIter_psi` |
| 30 | `bigTheta_apply` | 468 | A | `@[simp]`, inert; 2 uses |
| 31 | `psi_eq` | 475 | S | `fst_psi`, `snd_psi` |
| 32 | `fst_psi` | 479 | S | `psi_injective`, `thm26` |
| 33 | `psi_injective` | 484 | S | `thm26` |
| 34 | `snd_psi` | 489 | S | `fst_sndIter_psi` |
| 35 | `sndIter_tailHom` | 494 | S | `fst_sndIter_psi` |
| 36 | `fst_sndIter_psi` | 508 | S | `thm26` |
| 37 | `app_combEval_fstSndPowComb` | 531 | S | `thm26` |
| 38 | `thm26` | 555 | S | `thm26_subalgebra`, `thm26_retract` |
| 39 | `thm26_subalgebra` | 574 | **U** | 0 uses; subset variant, not the paper's retract hypothesis |
| 40 | `thm26_retract` | 590 | **P** | §7.2, Theorem 26 — "a domain `A` that is a retract of `D` … isomorphic to a subalgebra" |
| 41 | `exists_lambdaModel_of_thm25` | 625 | **P** | §7.2 opening prose: the λ-calculus model as a continuous algebra |

### 9.5 `CombinatorRep` — 28 (+1 artifact)

| # | Declaration | Line | Label | Evidence |
| -- | ---------- | ---- | ----- | -------- |
| 1 | `scottContinuous_repFamily` | 118 | S | `isRepresentable_of_retracts`, `isRepresentable₂_of_retracts` (both bucket 3) |
| 2 | `isRepresentable_of_retracts` | 150 | S | `rep_lift` (bucket 3) |
| 3 | `isRepresentable₂_of_retracts` | 167 | S | `rep_arrow`, `rep_prod` (bucket 3) |
| 4 | `directedOn_fst_val` | 196 | **U** | 0 uses; and 5 inline copies exist elsewhere — see §6 |
| 5 | `directedOn_snd_val` | 204 | **U** | 0 uses; same |
| 6 | `isLUB_fst_val` | 213 | S | `isLUB_arrowFamily` |
| 7 | `isLUB_snd_val` | 225 | S | `isLUB_arrowFamily` |
| 8 | `isClosure_arrowFamily` | 248 | S | `rep_arrow` |
| 9 | `arrowFamily_mono` | 251 | S | `rep_arrow` |
| 10 | `isLUB_arrowFamily` | 254 | S | `rep_arrow` |
| — | *(docstring line)* | 265 | — | counting artifact, §1 |
| 11 | `rep_arrow` | 266 | **U** | 0 code uses; Lemma 28's `→` at the refuted closure reading |
| 12 | `isClosure_prodFamily` | 282 | S | `rep_prod` |
| 13 | `prodFamily_mono` | 285 | S | `rep_prod` |
| 14 | `isLUB_prodFamily` | 288 | S | `rep_prod` |
| 15 | `rep_prod` | 297 | **U** | 0 code uses; superseded by `PRep.rep_prod` |
| 16 | `isLUB_coe_image` | 323 | S | **`PRep.isLUB_liftFamily`** — crosses the file boundary |
| 17 | `scottContinuous_liftFun` | 339 | S | the continuity field of `def liftMap`, which `PRep` consumes |
| 18 | `liftMap_bot` | 388 | A | `@[simp]`, **fires** (measured) |
| 19 | `liftMap_coe` | 390 | A | `@[simp]`, **fires** (measured) |
| 20 | `isClosure_liftMap` | 395 | S | `isClosure_liftFamily` |
| 21 | `liftMap_mono` | 406 | S | **`PRep.liftFamily_mono`** — crosses the file boundary |
| 22 | `isClosure_liftFamily` | 416 | S | `rep_lift` |
| 23 | `liftFamily_mono` | 419 | S | `rep_lift` |
| 24 | `isLUB_liftFamily` | 422 | S | `rep_lift` |
| 25 | `liftRange_mem` | 447 | **D** | `PRep.liftRange_mem` — `Audit.SectionSeven.liftRange_mem_pair` |
| 26 | `liftRangeMap_le_iff` | 461 | **D** | `PRep.liftRangeMap_le_iff` — `…liftRangeMap_le_iff_pair` |
| 27 | `liftRangeMap_surjective` | 476 | **D** | `PRep.liftRangeMap_surjective` — `…liftRangeMap_surjective_pair` |
| 28 | `rep_lift` | 492 | **U** | 0 code uses; superseded by `PRep.rep_lift` |

### 9.6 `Dyadic` — 59

| # | Declaration | Line | Label | Evidence |
| -- | ---------- | ---- | ----- | -------- |
| 1 | `zero_mem_S` | 103 | S | `S_nonempty`, `isBasic_lowerHalf` |
| 2 | `S_nonempty` | 105 | S | `isBasic_S` |
| 3 | `mem_Ico_of_mem_S` | 109 | S | `Ivl_zero_one`; `Atomless.mul_two_pow_nonneg` |
| 4 | `zero_mem_E` | 121 | S | `isBasic_S`, `isBasic_lowerHalf` |
| 5 | `one_mem_E` | 123 | S | `isBasic_S` |
| 6 | `max_mem_E` | 127 | S | `isBasic_inter` |
| 7 | `min_mem_E` | 132 | S | `isBasic_inter` |
| 8 | `mem_Ivl` | 142 | A | `@[simp]`, inert; used by name in `Ivl_inter`, `Atomless.mem_Ivl_block` |
| 9 | `Ivl_subset_S` | 144 | S | `unionOf_subset_S` |
| 10 | `Ivl_zero_one` | 147 | S | `isBasic_S` |
| 11 | `Ivl_inter` | 153 | S | `unionOf_inter` (2 uses) |
| 12 | `mem_unionOf` | 164 | S | `unionOf_subset_S`, `unionOf_singleton`, `unionOf_inter`, `Atomless.eq_unionOf_block` |
| 13 | `unionOf_subset_S` | 168 | S | `IsBasic.subset_S` |
| 14 | `unionOf_singleton` | 173 | S | `isBasic_S`, `isBasic_lowerHalf` |
| 15 | `IsBasic.subset_S` | 190 | S | `U₀.toSet_subset_S` (dot notation) |
| 16 | `isBasic_S` | 195 | S | the `OrderBot U₀` instance |
| 17 | `unionOf_inter` | 205 | S | `isBasic_inter` |
| 18 | `isBasic_unionOf` | 223 | S | `isBasic_inter` |
| 19 | `isBasic_inter` | 226 | S | `U₀.exists_isLUB_pair` |
| 20 | `U₀.isBasic` | 250 | S | `toSet_nonempty`, `toSet_subset_S`, `exists_isLUB_pair` |
| 21 | `U₀.toSet_mk` | 255 | **A** | `@[simp]`, inert, **0 uses** |
| 22 | `U₀.ext` | 257 | S | the `PartialOrder`/`OrderBot` instances, `Atomless.psi_bot` |
| 23 | `U₀.toSet_nonempty` | 259 | S | `exists_isLUB_pair`, `Atomless.isNormalIn_range_psi` |
| 24 | `U₀.toSet_subset_S` | 261 | S | the `OrderBot U₀` instance |
| 25 | `U₀.le_iff` | 272 | S | `exists_isLUB_pair`, `mem_principal_iff`, `Atomless.isNormalIn_range_psi`, `Colimit` |
| 26 | `U₀.toSet_bot` | 279 | A | `@[simp]`, inert; 1 use (`Atomless.psi_bot`) |
| 27 | `U₀.countable_isBasic` | 284 | S | the `Countable U₀` instance |
| 28 | `U₀.exists_isLUB_pair` | 295 | S | the `BoundedComplete U` instance, `Atomless.instCountableBC` |
| 29 | `half_mem_S` | 318 | S | `bot_lt_lowerHalf` |
| 30 | `half_mem_E` | 320 | S | `isBasic_lowerHalf` |
| 31 | `isBasic_lowerHalf` | 322 | S | `lowerHalf` |
| 32 | `bot_lt_lowerHalf` | 335 | S | the `Nontrivial U₀` instance |
| 33 | `mem_principal_iff` | 366 | **U** | 0 uses |
| 34 | `compacts_U` | 374 | **U** | 0 uses; Theorem 11's second conjunct at `U₀`, terminal by design |
| 35 | `isCompactElement_iff` | 378 | **U** | 0 uses; re-export of `IdealCompletion.isCompactElement_iff_exists_eq_principal` |
| 36 | `thm11_at_U` | 384 | **U** | 0 uses; literally `IdealCompletion.thm11 U₀` |
| 37 | `emb_mem` | 465 | S | `directedOn_projSet` (2 uses) |
| 38 | `emb_le_emb` | 468 | A | `@[simp]`, inert; 6 uses by name |
| 39 | `emb_mono` | 472 | **U** | 0 uses; every call site uses `emb_le_emb` |
| 40 | `exists_emb_eq` | 476 | S | `directedOn_projSet` |
| 41 | `bot_mem_of_isNormalIn` | 481 | S | `emb_bot` (2 uses) |
| 42 | `emb_bot` | 490 | S | `projSet_nonempty` |
| 43 | `isIdeal_embSet` | 503 | S | `embIdeal`; `LemThirty` |
| 44 | `mem_embIdeal` | 517 | S | `LemThirty` |
| 45 | `embIdeal_mono` | 520 | S | `scottContinuous_embIdeal`; `LemThirty` |
| 46 | `scottContinuous_embIdeal` | 526 | S | `embHom`; `LemThirty` |
| 47 | `embHom_apply` | 538 | **A** | `@[simp]`, inert, **0 uses** |
| 48 | `projSet_nonempty` | 547 | S | `embIdeal_projElem_le` |
| 49 | `directedOn_projSet` | 555 | S | `isLUB_projElem`, `embIdeal_projElem_le` |
| 50 | `isLUB_projElem` | 570 | S | 6 uses |
| 51 | `projSet_mono` | 574 | S | `projElem_mono` |
| 52 | `projElem_mono` | 579 | S | `scottContinuous_projElem` |
| 53 | `scottContinuous_projElem` | 584 | S | `projHom` |
| 54 | `projHom_apply` | 602 | **A** | `@[simp]`, inert, **0 uses** |
| 55 | `projSet_embIdeal` | 610 | S | `projElem_embIdeal` |
| 56 | `projElem_embIdeal` | 618 | S | `thm27_of_isNormallyRepresented` |
| 57 | `embIdeal_projElem_le` | 627 | S | `thm27_of_isNormallyRepresented` |
| 58 | `thm27_of_isNormallyRepresented` | 640 | S | `Dyadic.thm27`, **`Atomless.thm27`** |
| 59 | `thm27` | 652 | **U** | 0 code uses; row 58 plus an unused `[BoundedComplete D]` |

### 9.7 `Atomless` — 56

| # | Declaration | Line | Label | Evidence |
| -- | ---------- | ---- | ----- | -------- |
| 1 | `two_pow_pos` | 110 | S | 4 uses |
| 2 | `two_pow_ne_zero` | 112 | S | `cast_div_two_pow_succ`, `addr_blockLeft` |
| 3 | `cast_div_two_pow_succ` | 122 | S | `div_two_pow_mem_E`, `div_two_pow_mem_S` |
| 4 | `div_two_pow_mem_E` | 130 | S | `isBasic_block` (2 uses) |
| 5 | `div_two_pow_mem_S` | 137 | S | `blockLeft_mem_S` |
| 6 | `mul_two_pow_nonneg` | 147 | S | 4 uses |
| 7 | `addr_lt` | 150 | S | `eq_unionOf_block` |
| 8 | `mem_Ivl_block` | 159 | S | `eq_unionOf_block` (2 uses) |
| 9 | `blockLeft_mem_S` | 166 | S | `pt_mem_S` |
| 10 | `addr_blockLeft` | 169 | S | `addr_pt` |
| 11 | `addr_succ_div_two` | 175 | S | `br_succ`, `addr_pt` |
| 12 | `eq_unionOf_block` | 196 | S | `isBasic_block` |
| 13 | `isBasic_block` | 213 | S | `isBasic_psiSet` |
| 14 | `exists_enum` | 243 | S | `enum`, `enum_surjective` |
| 15 | `enum_surjective` | 251 | S | `idx`; `EffectivePresentation` |
| 16 | `enum_idx` | 257 | A | `@[simp]`, inert; 4 uses by name |
| 17 | `isLUB_jn` | 265 | S | `le_jn_left`, `le_jn_right`, `jn_le` |
| 18 | `le_jn_left` | 271 | S | 4 uses |
| 19 | `le_jn_right` | 274 | S | 3 uses |
| 20 | `jn_le` | 277 | S | `psiSet_inter`, `digits_spec` |
| 21 | `le_step` | 297 | S | `br_le_succ` |
| 22 | `step_stable` | 306 | S | `br_stable` |
| 23 | `st_zero` | 321 | **A** | `@[simp]`, inert, **0 uses** |
| 24 | `st_succ` | 323 | A | `@[simp]`, inert; 2 uses by name |
| 25 | `br_succ` | 330 | S | `br_le_succ`, `br_stable` |
| 26 | `br_le_succ` | 334 | S | `br_mono` |
| 27 | `br_mono` | 338 | S | 5 uses |
| 28 | `br_stable` | 343 | S | `mem_psiSet_iff` |
| 29 | `psiSet_subset_S` | 360 | **U** | 0 uses |
| 30 | `mem_psiSet_iff` | 364 | S | 6 uses |
| 31 | `mem_psiSet_of_le` | 377 | S | `psiSet_subset_of_le`, `psiSet_inter` |
| 32 | `psiSet_bot` | 381 | S | `psi_bot` |
| 33 | `psiSet_subset_of_le` | 387 | S | `psiSet_inter`, `psi_le_psi` |
| 34 | `bddAbove_of_psiSet_inter_nonempty` | 395 | S | `isNormalIn_range_psi` |
| 35 | `psiSet_inter` | 407 | S | `isNormalIn_range_psi` |
| 36 | `digits_lt` | 430 | S | `digits_lt` (recursion), `pt_mem_S` |
| 37 | `digits_div_two` | 441 | S | `digits_spec`, `addr_pt` |
| 38 | `digits_mod_two` | 446 | S | `digits_spec` |
| 39 | `digits_mod_two'` | 451 | S | `digits_spec` |
| 40 | `digits_spec` | 459 | S | `st_digits_le`, `le_st_digits` |
| 41 | `st_digits_le` | 500 | S | `le_of_psiSet_subset` |
| 42 | `le_st_digits` | 502 | S | `pt_mem_psiSet` |
| 43 | `pt_mem_S` | 510 | S | `addr_pt`, `pt_mem_psiSet` |
| 44 | `addr_pt` | 512 | S | `pt_mem_psiSet`, `le_of_psiSet_subset` |
| 45 | `pt_mem_psiSet` | 527 | S | `psiSet_nonempty`, `le_of_psiSet_subset` |
| 46 | `psiSet_nonempty` | 532 | S | `isBasic_psiSet` |
| 47 | `le_of_psiSet_subset` | 538 | S | `psi_le_psi` |
| 48 | `isBasic_psiSet` | 549 | S | `psi` |
| 49 | `toSet_psi` | 555 | A | `@[simp]`, inert; 2 uses by name |
| 50 | `psi_le_psi` | 559 | A | `@[simp]`, inert; 4 uses by name |
| 51 | `psi_injective` | 562 | S | `psiOrderIso` |
| 52 | `psi_bot` | 565 | A | `@[simp]`, inert; 1 use (`isNormalIn_range_psi`) |
| 53 | `isNormalIn_range_psi` | 571 | S | `isNormallyRepresented` |
| 54 | `isNormallyRepresented` | 597 | S | `isNormallyRepresented_compacts` |
| 55 | `isNormallyRepresented_compacts` | 640 | S | `thm27` |
| 56 | `thm27` | 646 | **P** | §7.3, Theorem 27 — projection `p : U → D` for every bounded complete domain; **the live one**, cited by `PRepSum.pairAtU` |

### 9.8 `PRepresentable` — 3

| # | Declaration | Line | Label | Evidence |
| -- | ---------- | ---- | ----- | -------- |
| 1 | `FpImage_carrier` | 90 | **A** | `@[simp]`, inert, **0 uses**; closure of 6 modules probed |
| 2 | `eq_id_of_mem_Fp_of_mem_Fc` | 119 | **U** | 0 uses; the `Fp ∩ Fc = {id}` measurement — keep as evidence |
| 3 | `isProjection_repOf` | 147 | S | `PRep.isFinitaryProjection_repOf` |

### 9.9 `PRep` — 39

| # | Declaration | Line | Label | Evidence |
| -- | ---------- | ---- | ----- | -------- |
| 1 | `smythOp_eq` | 229 | **U** | 0 uses; `rfl` measurement that `(·)♯` is definable on `Cpo` — keep as evidence |
| 2 | `hoareOp_eq` | 233 | **U** | 0 uses; same for `(·)♭` |
| 3 | `lemma28_of` | 267 | S | `PRepSum.lemma28AtU_of` |
| 4 | `isProjection_sSup` | 313 | S | `isFinitaryProjection_sSup`, `exists_mem_range_of_isCompactElement` |
| 5 | `apply_eq_of_mem_range_of_le` | 331 | S | `range_subset_of_le` |
| 6 | `range_subset_of_le` | 337 | S | `isFinitaryProjection_sSup` (3 uses) |
| 7 | `boundedComplete_range` | 352 | S | `PRepFun.domain_range_compHom`, `domain_range_strictArrowFamily` |
| 8 | `countable_compacts_range` | 378 | S | `isFinitaryProjection_sSup`; `FinitaryProjectionPoset` |
| 9 | `isLUB_val_image_of_isLUB_fp` | 393 | S | `isLUB_val_image_of_isLUB_fp'` |
| 10 | `exists_mem_range_of_isCompactElement` | 432 | S | `isFinitaryProjection_sSup` (2 uses) |
| 11 | `isFinitaryProjection_sSup` | 463 | S | `isLUB_val_image_of_isLUB_fp'` |
| 12 | `isLUB_val_image_of_isLUB_fp'` | 535 | S | `isLUB_liftFamily`, `isLUB_prodFamily`, `PRepFun.isLUB_arrowFamily`, `PRepSum.isLUB_coalSumFamily` |
| 13 | `directedOn_orderIso_image` | 563 | S | `isCompactElement_orderIso`, `isAlgebraic_orderIso`; `LemThirty` |
| 14 | `isLUB_orderIso_image` | 569 | S | `isCompactElement_orderIso`, `isAlgebraic_orderIso`; `LemThirty` |
| 15 | `isCompactElement_orderIso` | 580 | S | `compacts_orderIso`, `compactsBelow_orderIso` (4 uses) |
| 16 | `compacts_orderIso` | 589 | S | `domain_orderIso` |
| 17 | `compactsBelow_orderIso` | 597 | S | `isAlgebraic_orderIso` (2 uses) |
| 18 | `isAlgebraic_orderIso` | 610 | S | `domain_orderIso` |
| 19 | `domain_orderIso` | 620 | S | `isFinitaryProjection_repOf`, `domain_range_liftMap`, `domain_range_prodMap`, `PRepFun`, `PRepSum` |
| 20 | `isFinitaryProjection_repOf` | 663 | S | `rep_lift`, `rep_prod`, `PRepFun` ×3, `PRepSum` ×2 |
| 21 | `gr_fn_eq_of_both` | 693 | S | `orderIsoOfBothPairs`; the r0037 non-transfer result |
| 22 | `scottContinuous_repFamilyFp` | 718 | S | `isPRepresentable_of_repFamily`, `isPRepresentable₂_of_repFamily` |
| 23 | `isPRepresentable_of_repFamily` | 740 | S | `rep_lift` |
| 24 | `isPRepresentable₂_of_repFamily` | 756 | S | `rep_prod`; `PRepFun` ×3, `PRepSum` ×2 |
| 25 | `isProjection_liftMap` | 801 | S | `domain_range_liftMap`, `isProjection_liftFamily` |
| 26 | `liftRange_mem` | 819 | S | `liftRangeMap` — the general form of `CombinatorRep:447` |
| 27 | `liftRangeMap_le_iff` | 832 | S | `liftRangeOrderIso` — general form of `CombinatorRep:461` |
| 28 | `liftRangeMap_surjective` | 847 | S | `liftRangeOrderIso` — general form of `CombinatorRep:476` |
| 29 | `domain_range_liftMap` | 865 | S | `rep_lift`; `PRepSum.domain_range_sepSumFamily` |
| 30 | `isProjection_liftFamily` | 882 | S | `rep_lift`; `PRepSum.sepSumFamily` (7 uses) |
| 31 | `liftFamily_mono` | 885 | S | `rep_lift`; `PRepSum.sepSumFamily_mono` |
| 32 | `isLUB_liftFamily` | 892 | S | `rep_lift`; `PRepSum.isLUB_sepSumFamily` |
| 33 | `rep_lift` | 922 | S | `PRepSum.repLiftAtU`; `LemThirty` |
| 34 | `isProjection_prodMap` | 952 | S | `domain_range_prodMap`, `isProjection_prodFamily` |
| 35 | `domain_range_prodMap` | 960 | S | `rep_prod` |
| 36 | `isProjection_prodFamily` | 977 | S | `rep_prod` |
| 37 | `prodFamily_mono` | 980 | S | `rep_prod` |
| 38 | `isLUB_prodFamily` | 986 | S | `rep_prod`; `PRepFun.isLUB_smashFamily` |
| 39 | `rep_prod` | 1027 | S | `PRepSum.repProdAtU`; `LemThirty` |

### 9.10 `PRepFun` — 51 (+1 artifact)

| # | Declaration | Line | Label | Evidence |
| -- | ---------- | ---- | ----- | -------- |
| 1 | `scottContinuous_val` | 157 | S | `restrictHomP`, `extendHomP` |
| 2 | `scottContinuous_corestrict` | 169 | S | `restrictHomP`, `extendHomP` |
| 3 | `compHom_extendHomP` | 223 | S | `extendHomP_mem_range`, `strictEvidentOrderIso` |
| 4 | `extendHomP_mem_range` | 234 | S | `evidentOrderIsoP` |
| 5 | `domain_range_compHom` | 275 | S | `rep_arrow` |
| 6 | `isProjection_arrowFamily` | 296 | S | `rep_arrow` |
| 7 | `arrowFamily_mono` | 300 | S | `rep_arrow` |
| 8 | `isLUB_arrowFamily` | 314 | S | `rep_arrow`, `isLUB_strictArrowFamily` |
| 9 | `rep_arrow` | 368 | S | `Lemma28AtU.repArrowAtU` |
| 10 | `isStrict_of_le` | 405 | S | `val_image_compactsBelow`, `strictHomIsAlgebraic` |
| 11 | `val_image_compactsBelow` | 413 | S | `strictHomIsAlgebraic` (3 uses); `Theorem6` |
| 12 | `strictHomIsAlgebraic` | 426 | S | `strictHomDomain` |
| — | *(docstring line)* | 449 | — | counting artifact, §1 |
| 13 | `strictHomDomain` | 450 | S | `domain_range_strictArrowFamily`; `Lemma28AtU.repStrictArrowAtU` |
| 14 | `strictArrowFamily_val` | 506 | **A** | `@[simp]`, inert, **0 uses** |
| 15 | `isProjection_strictArrowFamily` | 511 | S | `domain_range_strictArrowFamily`, `rep_strictArrow` (3 uses) |
| 16 | `strictArrowFamily_mono` | 516 | S | `rep_strictArrow` |
| 17 | `isLUB_strictArrowFamily` | 524 | S | `rep_strictArrow` |
| 18 | `val_mem_range_compHom` | 551 | S | `strictEvidentOrderIso` |
| 19 | `domain_range_strictArrowFamily` | 612 | S | `rep_strictArrow` |
| 20 | `rep_strictArrow` | 632 | S | `Lemma28AtU.repStrictArrowAtU` |
| 21 | `smashEmbed_bot` | 687 | **A** | `@[simp]`, inert, **0 uses** |
| 22 | `smashEmbed_coe` | 689 | **A** | `@[simp]`, inert, **0 uses** |
| 23 | `smashCollapse_of` | 698 | S | 13 uses |
| 24 | `smashCollapse_of_not` | 702 | S | 7 uses |
| 25 | `monotone_smashCollapse` | 706 | S | 4 uses |
| 26 | `scottContinuous_smashEmbed` | 722 | S | `smashMap`, `isCompactElement_smash_coe_iff` |
| 27 | `scottContinuous_smashCollapse` | 766 | S | `smashMap`, `isCompactElement_smash_coe_iff`, `isLUB_smashFamily` |
| 28 | `smash_le_of_coe_le` | 825 | S | 4 uses |
| 29 | `smash_coe_le_of_le` | 830 | S | 8 uses |
| 30 | `nonBot_of_le` | 834 | S | `isCompactElement_smash_coe_iff`, `smashIsAlgebraic` |
| 31 | `exists_nonBot_of_isLUB` | 843 | S | `smashIsAlgebraic`; **note**: the same script is still inlined at 777–790 |
| 32 | `isCompactElement_smash_coe_iff` | 891 | S | 7 uses |
| 33 | `smashIsAlgebraic` | 926 | S | `smashDomain` |
| 34 | `smashDomain` | 992 | S | `domain_range_smashFamily`; `Lemma28AtU.repSmashAtU` |
| 35 | `smashMap_apply` | 1034 | **A** | `@[simp]`, inert, **0 uses** |
| 36 | `smashMap_bot` | 1040 | S | `isProjection_smashMap`, `bot_mem_range_smashFamily` (4 uses) |
| 37 | `isProjection_smashMap` | 1050 | S | `isProjection_smashFamily` |
| 38 | `smashMap_mono` | 1076 | S | `smashFamily_mono` |
| 39 | `isProjection_smashFamily` | 1087 | S | `domain_range_smashFamily`, `rep_smash` |
| 40 | `smashFamily_mono` | 1091 | S | `rep_smash` |
| 41 | `isLUB_smashFamily` | 1099 | S | `rep_smash` |
| 42 | `val_ne_bot_of_ne_bot` | 1130 | **D** | `PRepSum.val_ne_bot_of_ne_bot` — `Audit.SectionSeven.val_ne_bot_of_ne_bot_pair` |
| 43 | `ne_bot_of_val_ne_bot` | 1137 | S | `smashRangeMap_surjective` |
| 44 | `bot_mem_range_smashFamily` | 1142 | S | `smashRangeMap` |
| 45 | `coe_mem_range_smashFamily` | 1147 | S | `smashRangeMap` |
| 46 | `range_smashFamily_cases` | 1158 | S | `smashRangeMap_surjective` |
| 47 | `nonBotPairDown_le_iff` | 1175 | S | `smashRangeMap_le_iff` |
| 48 | `smashRangeMap_le_iff` | 1187 | S | `smashRangeOrderIso` |
| 49 | `smashRangeMap_surjective` | 1209 | S | `smashRangeOrderIso` |
| 50 | `domain_range_smashFamily` | 1232 | S | `rep_smash` |
| 51 | `rep_smash` | 1255 | S | `Lemma28AtU.repSmashAtU` |

### 9.11 `PRepSum` — 62

| # | Declaration | Line | Label | Evidence |
| -- | ---------- | ---- | ----- | -------- |
| 1 | `pairAtU` | 130 | S | `repProdAtU`, `repLiftAtU`, `repCoalSumAtU`, `repSepSumAtU`; `Lemma28AtU` ×3 |
| 2 | `repProdAtU` | 157 | **P** | Lemma 28 conjunct 3 (`×`) over `Dyadic.U`, no hypothesis |
| 3 | `repLiftAtU` | 166 | **P** | Lemma 28 conjunct 7 (`(·)⊥`) over `Dyadic.U` |
| 4 | `isCompactElement_sumInl` | 194 | S | `mem_compactsBelow_sumInl` |
| 5 | `isCompactElement_sumInr` | 200 | S | `mem_compactsBelow_sumInr` |
| 6 | `mem_compactsBelow_sumInl` | 207 | S | `directedOn_compactsBelow_coe_inl`, `isLUB_compactsBelow_coe_inl` |
| 7 | `mem_compactsBelow_sumInr` | 218 | S | the `inr` counterparts |
| 8 | `eq_bot_or_sumInl_of_mem_compactsBelow` | 231 | S | `directedOn_compactsBelow_coe_inl` (2 uses) |
| 9 | `eq_bot_or_sumInr_of_mem_compactsBelow` | 247 | S | `directedOn_compactsBelow_coe_inr` |
| 10 | `compactsBelow_diff_bot_nonempty` | 265 | S | `isLUB_compactsBelow_coe_inl`/`_inr` |
| 11 | `directedOn_compactsBelow_coe_inl` | 270 | S | `isAlgebraic_coalescedSum` |
| 12 | `directedOn_compactsBelow_coe_inr` | 282 | S | `isAlgebraic_coalescedSum` |
| 13 | `isLUB_compactsBelow_coe_inl` | 294 | S | `isAlgebraic_coalescedSum` |
| 14 | `isLUB_compactsBelow_coe_inr` | 319 | S | `isAlgebraic_coalescedSum` |
| 15 | `isAlgebraic_coalescedSum` | 347 | S | `domain_coalescedSum` |
| 16 | `compacts_coalescedSum_subset` | 366 | S | `domain_coalescedSum` |
| 17 | `domain_coalescedSum` | 390 | S | `domain_range_coalSumMap`, `repCoalSumAtU`, `repSepSumAtU` |
| 18 | `coalescedSum_cases` | 406 | S | 15 uses |
| 19 | `not_sumInl_le_bot` | 421 | S | `sumInl_le_sumInl_iff`, `coalSumRangeMap_le_iff`, `coalSumCongrFun_le_iff` |
| 20 | `not_sumInr_le_bot` | 424 | S | the `inr` counterparts |
| 21 | `sumInl_le_sumInl_iff` | 428 | S | `coalSumRangeMap_le_iff`, `coalSumCongrFun_le_iff` |
| 22 | `sumInr_le_sumInr_iff` | 437 | S | same |
| 23 | `not_sumInl_le_sumInr` | 449 | S | `coalSumRangeMap_le_iff`, `coalSumCongrFun_le_iff` |
| 24 | `not_sumInr_le_sumInl` | 458 | S | same |
| 25 | `sumInlFun_eq_sumInl` | 472 | S | `scottContinuous_sumInl` |
| 26 | `sumInrFun_eq_sumInr` | 477 | S | `scottContinuous_sumInr` |
| 27 | `scottContinuous_sumInl` | 482 | S | `inlHom`, `isLUB_coalSumFamily`, `isLUB_sepSumFamily` |
| 28 | `scottContinuous_sumInr` | 488 | S | `inrHom`, and the `inr` counterparts |
| 29 | `isStrict_of_isProjection` | 540 | **D** | rename of `ScottHom.IsProjection.map_bot`; 0 uses, every call site writes `hp.map_bot` |
| 30 | `val_ne_bot_of_ne_bot` | 545 | S | `coalSumRangeMap_le_iff`; the general form of `PRepFun:1130` |
| 31 | `coalSumMap_bot` | 572 | A | `@[simp]`, **fires** |
| 32 | `coalSumMap_coe` | 574 | S | `coalSumMap_sumInl`, `coalSumMap_sumInr` |
| 33 | `coalSumMap_sumInl` | 578 | A | `@[simp]`, **fires**; 5 uses |
| 34 | `coalSumMap_sumInr` | 585 | A | `@[simp]`, **fires**; 5 uses |
| 35 | `isProjection_coalSumMap` | 594 | S | `domain_range_coalSumMap`, `isProjection_coalSumFamily`, `isProjection_sepSumFamily` |
| 36 | `coalSumMap_mono` | 609 | S | `coalSumFamily_mono`, `sepSumFamily_mono` |
| 37 | `rangeSumVal_bot` | 639 | A | `@[simp]`, **fires**; 4 uses |
| 38 | `projCpo_bot_val` | 642 | S | `rangeSumVal_sumInl`, `rangeSumVal_sumInr` |
| 39 | `rangeSumVal_sumInl` | 645 | A | `@[simp]`, **fires**; 6 uses |
| 40 | `rangeSumVal_sumInr` | 651 | A | `@[simp]`, **fires**; 6 uses |
| 41 | `rangeSumVal_mem_range` | 659 | S | `coalSumRangeMap` |
| 42 | `coalSumRangeMap_le_iff` | 677 | S | `coalSumRangeOrderIso` |
| 43 | `coalSumRangeMap_surjective` | 705 | S | `coalSumRangeOrderIso` |
| 44 | `domain_range_coalSumMap` | 731 | S | `rep_coalSum`, `domain_range_sepSumFamily` |
| 45 | `isProjection_coalSumFamily` | 751 | S | `rep_coalSum` |
| 46 | `coalSumFamily_mono` | 754 | S | `rep_coalSum` |
| 47 | `isLUB_coalSumFamily` | 761 | S | `rep_coalSum` |
| 48 | `rep_coalSum` | 812 | S | `repCoalSumAtU` |
| 49 | `orderIso_apply_bot` | 845 | **D** | Mathlib `OrderIso.map_bot` — `Audit.SectionSeven.orderIso_apply_bot_is_mathlib_map_bot` |
| 50 | `orderIso_apply_ne_bot` | 853 | S | `coalSumCongrFun_le_iff` (2 uses) |
| 51 | `coalSumCongrFun_bot` | 865 | A | `@[simp]`, **fires**; 4 uses |
| 52 | `coalSumCongrFun_sumInl` | 869 | A | `@[simp]`, **fires**; 4 uses |
| 53 | `coalSumCongrFun_sumInr` | 876 | A | `@[simp]`, **fires**; 4 uses |
| 54 | `coalSumCongrFun_le_iff` | 883 | S | `coalSumCongr` |
| 55 | `isProjection_sepSumFamily` | 955 | S | `domain_range_sepSumFamily`, `rep_sepSum` |
| 56 | `sepSumFamily_mono` | 958 | S | `rep_sepSum` |
| 57 | `domain_range_sepSumFamily` | 973 | S | `rep_sepSum` |
| 58 | `isLUB_sepSumFamily` | 983 | S | `rep_sepSum` |
| 59 | `rep_sepSum` | 1024 | S | `repSepSumAtU` |
| 60 | `repCoalSumAtU` | 1042 | **P** | Lemma 28 conjunct 6 (`⊕`) over `Dyadic.U`, no hypothesis |
| 61 | `repSepSumAtU` | 1052 | **P** | Lemma 28 conjunct 5 (`+`) over `Dyadic.U`, no hypothesis |
| 62 | `lemma28AtU_of` | 1066 | S | `Lemma28AtU.lemma28AtU_of'` |

### 9.12 `Lemma28AtU` — 4

| # | Declaration | Line | Label | Evidence |
| -- | ---------- | ---- | ----- | -------- |
| 1 | `repArrowAtU` | 59 | **P** | Lemma 28 conjunct 1 (`→`) over `Dyadic.U`, no hypothesis |
| 2 | `repStrictArrowAtU` | 68 | **P** | Lemma 28 conjunct 2 (`⇸`) over `Dyadic.U`, no hypothesis |
| 3 | `repSmashAtU` | 79 | **P** | Lemma 28 conjunct 4 (`⊗`) over `Dyadic.U`, no hypothesis |
| 4 | `lemma28AtU_of'` | 87 | **U** | 0 uses; the join, terminal by design — its arity 2 is the progress measurement |

## 10. Two documentation defects found while labelling

Neither changes a label; both are stale prose that a later reader would act on.

1. **`PRepresentable.lean:39–43`** states "Lemma 28 (…) is the `Fc` notion;
   Lemma 30 (…) is the `Fp` notion." That is the sentence `PRep.lean:53–57`
   identifies as refuted by the paper's own "for the remainder of this section",
   and it sits in the file that *defines* `IsPRepresentable`. It contradicts the
   settled reading three files downstream and should be corrected to match
   `PRep.lean`'s.
2. **`Dyadic.lean:414–417`** describes `IsNormallyRepresented` as "the only part
   of Theorem 27 not proved in this module", which is accurate, but the module
   docstring's §Statements list (lines 87–92) still advertises `compacts_U` and
   `thm11_at_U` as deliverables when both are uncited re-exports (`U` rows 34 and
   36).

## 11. Verification that this round moved nothing

| # | Check | Before | After |
| -- | ---- | ------ | ----- |
| 1 | `scripts/compile.sh` exit | 0 | 0 |
| 2 | `sorry` warnings | 1 | 1 |
| 3 | jobs | 1223 | 1224 (+1: the audit module) |
| 4 | `counts.sh` theorems | 1308 | 1313 (+5: the five equivalence theorems) |
| 5 | modules | 72 | 73 |
| 6 | existing `.lean` files edited | — | **none** |

The only additions are `ScottDomains/Audit/SectionSeven.lean` (97 lines, 5
theorems, all `rfl`) and four scripts. No existing declaration, proof, docstring
or attribute was touched.

## 12. Scripts added

| # | Script | What it measures |
| -- | ----- | ---------------- |
| 1 | `scripts/a5-decls.sh` | every `theorem`/`lemma` in the twelve modules with module, line, `@[simp]` status and statement head |
| 2 | `scripts/a5-citations.sh` | per-name use counts split into own-module and cross-module, over a comment-stripped index so a docstring mention is not counted as a use |
| 3 | `scripts/a5-simp-firing.sh` | whether a module's own `@[simp]` tags do work inside that module, by elaborating a scratch copy with the attribute groups deleted |
| 4 | `scripts/a5-simp-downstream.sh` | whether a tag fires in any module downstream, by splicing `attribute [-simp]` into scratch copies of the reverse-dependency closure |

Scripts 3 and 4 exist because the round forbids editing `.lean` files while the
`A` label asks whether removing a tag changes the build. Both write only to the
scratch tree.
