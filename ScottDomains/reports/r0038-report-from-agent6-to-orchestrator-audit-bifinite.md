---
round: r0038
from: agent6
to: orchestrator
subject: audit-bifinite
date: 2026-0808-09:57
started: 2026-0808-09:39
finished: 2026-0808-09:57
related:
  - plans/r0038-plan-from-orchestrator-to-orchestrator-theorem-audit.md
  - docs/PropertiesVsTheorems.md
---

# r0038 — `Audit.Bifinite`: 224 theorems classified

Area: `BifiniteUniversal`, `Colimit`, `LemThirty`, `JungSFP`, `JungFinite`,
`JungNets`, `ContinuousConstruction`.

No existing `.lean` file was edited. One file was added,
`ScottDomains/ScottDomains/Audit/Bifinite.lean`, carrying the plan's permitted
equivalence theorem for the one `D` pair that admits one. Measured after that
addition: `lake build` 1224 jobs, **zero errors, zero new warnings**, `sorry`
unchanged at 1, theorem total 1308 → 1310 (the two added theorems, both in the
audit namespace, imported by nothing).

## 0. A measurement correction before any label

The plan quotes 228 theorems for this area, from `scripts/module-counts.sh`. The
real count is **224**. The counting rule is `^(@\[…\] )?(theorem|lemma) `, which
also matches a **prose line inside a doc comment that happens to begin with the
word `theorem` or `lemma` at column 0**, and it counts a declaration that has
been commented out in place.

| # | Module | `module-counts.sh` | Real | Difference |
| -- | ------ | ------------------ | ---- | ---------- |
| 1 | `BifiniteUniversal.lean` | 26 | 26 | — |
| 2 | `Colimit.lean` | 73 | 73 | — |
| 3 | `LemThirty.lean` | 37 | 37 | — |
| 4 | `JungSFP.lean` | 23 | 23 | — |
| 5 | `JungFinite.lean` | 22 | 20 | `climbDown_le` (line 291) is inside a `/- … -/` block, retired by r0020's method; line 496 is the prose `lemma graded by \`ℕ\` — is applied instead, …` |
| 6 | `JungNets.lean` | 12 | 10 | lines 29 and 76 are prose beginning `theorem` at column 0 |
| 7 | `ContinuousConstruction.lean` | 35 | 35 | — |
| — | **total** | **228** | **224** | **−4** |

Three of the four are prose; one is an already-retired declaration that the
script still counts. `docs/PropertiesVsTheorems.md`'s headline **1308 is
therefore an over-count of at least 4**, and the same defect may inflate the
other five streams. The fix is one line in each script: skip lines inside
comment blocks. `ScottDomains/Audit/Bifinite.lean`'s own docstring is wrapped to
avoid triggering it, and says so.

## 1. Labelling rules used

Exactly one label per declaration, decided by these rules, stated so the
orchestrator can re-check them:

| # | Label | Rule applied here |
| -- | ----- | ----------------- |
| 1 | `P` | States a **Gunter–Scott** property: a numbered result, one conjunct of one, a prose claim, or a kernel-checked refutation of the paper's printed text. Jung's numbered results are *not* `P` — they are imported machinery serving Theorem 18, so they take `S` when cited. |
| 2 | `S` | At least one **Lean proof** cites it. A mention in a docstring is not a citation and does not earn `S`. Citer named. |
| 3 | `A` | Projection / membership / coercion / `rfl`-equation API: `_apply`, `_coe`, `_base`, `_cover`, `mem_`, `_bot`, `_zero`, defining case equations. `@[simp]` status stated. |
| 4 | `U` | Uncited by any proof, not a paper property, not API. Split below into *terminal by design* and *speculative*. |
| 5 | `D` | Same statement as another declaration, or interderivable with it in one application. Other named. |
| 6 | `W` | Proved at a strength nothing consumes. **Zero found**; two near-misses named in §6. |

Measurement method: `scripts/bifinite-audit-citations.sh` (new, committed) gives
per-declaration self/external citation counts and the citing modules;
`scripts/bifinite-audit-qualified.sh` (new, committed) reconstructs fully
qualified names from the namespace stack, which is required because the
final-component matching in `scripts/unused-theorems.sh` reports 169 "uses" of
`JungSFP.IsJungPatch.monotone` — every occurrence of the word `monotone` in the
package. Every zero-citation claim below was then confirmed by reading the
mention lines to separate docstring text from proof text.

## 2. Per-label totals

| # | Module | Thms | `P` | `S` | `A` | `U` | `D` | `W` |
| -- | ------ | ---- | --- | --- | --- | --- | --- | --- |
| 1 | `BifiniteUniversal` | 26 | 12 | 9 | 5 | 0 | 0 | 0 |
| 2 | `Colimit` | 73 | 3 | 50 | 16 | 2 | 2 | 0 |
| 3 | `LemThirty` | 37 | 12 | 15 | 3 | 7 | 0 | 0 |
| 4 | `JungSFP` | 23 | 0 | 13 | 9 | 1 | 0 | 0 |
| 5 | `JungFinite` | 20 | 1 | 19 | 0 | 0 | 0 | 0 |
| 6 | `JungNets` | 10 | 0 | 6 | 0 | 2 | 2 | 0 |
| 7 | `ContinuousConstruction` | 35 | 0 | 22 | 5 | 8 | 0 | 0 |
| — | **total** | **224** | **28** | **134** | **38** | **20** | **4** | **0** |

`U` splits into two populations, which is the split the plan's §4 asks for:

| # | Population | Count | Meaning |
| -- | ---------- | ----- | ------- |
| 1 | `U`-terminal | 6 | a deliberate record — a measured obstruction, a nondegeneracy check, or a stated result of Jung's. Nothing *should* cite it. |
| 2 | `U`-speculative | 14 | r0020's population 3: written for a caller that never appeared. |

**The number the round asks for: 14 + 4 = 18 of 224, or 8.0%, serve neither a
paper property nor a proof of one today.** r0020's rate was 3%. Eleven of the 18
are in two modules, `ContinuousConstruction` (6) and `LemThirty`'s composition
wrappers (5).

## 3. The tables

### 3.1 `BifiniteUniversal.lean` — 26

| # | Declaration | Label | Evidence |
| -- | ----------- | ----- | -------- |
| 1 | `MPair.mem_upper` | `A` | not `@[simp]`; `Iff.rfl` unfolding of `MPair.upper`; 0 citations anywhere |
| 2 | `MPair.le_iff` | `S` | `Colimit.mpairMap_le_mpairMap_iff:199` (twice) |
| 3 | `MPair.le_of_paperLE` | `S` | `pointA_le_pointB:273` |
| 4 | `MPair.equiv_of_upper_eq` | `P` | §7.4: "`(a,{a}) ⊢ (a,{a,b})` and `(a,{a,b}) ⊢ (a,{a})` so we have identified these elements"; 0 citations, terminal by design |
| 5 | `eta_base` | `A` | `@[simp]`; 0 citations |
| 6 | `eta_cover` | `A` | `@[simp]`; fires by name in `MSub_isNormalIn:344,356`, `Colimit.stg_one_eq:977` |
| 7 | `mem_upper_eta` | `S` | `eta_le_eta_iff:212`, `instOrderBot:220`, `MSub_isNormalIn:353`; `Colimit:610,628` |
| 8 | `eta_le_eta_iff` | `P` | §7.4: "each stage of the construction is embedded in the next one by the map `x ↦ (x,{x})`" — the embedding claim; 0 citations |
| 9 | `bot_eq_eta_bot` | `A` | `@[simp]`; `MSub_isNormalIn:343`, `Colimit:834,836,977` |
| 10 | `paperLE_irrefl_pointB` | `P` | §7.4 **defect 1**, at the paper's own `b = (⊥,∅)`: the printed relation is not reflexive |
| 11 | `paperLE_irrefl_boolPair` | `P` | §7.4 defect 1, shown independent of the empty cover |
| 12 | `not_reflexive_paperLE` | `P` | §7.4 defect 1: the printed relation is not a pre-ordering, contra "define a pre-ordering on `M(A)`" |
| 13 | `paperLE_pointA_pointB` | `P` | §7.4 **defect 2**: the printed definition yields `a ⊢ b` |
| 14 | `not_paperLE_pointB_pointA` | `P` | §7.4 defect 2: refutes the printed "with `b ⊢ a`" (p. 42, verified against the PDF this round) |
| 15 | `pointA_le_pointB` | `P` | §7.4's Figure 4 direction under the repair |
| 16 | `not_pointB_le_pointA` | `P` | same |
| 17 | `mpair_punit_eq` | `P` | §7.4: "At the second step, `I⁺`, there are elements `a = (⊥,{⊥})` and `b = (⊥,∅)`" — the count 2 |
| 18 | `MSub_finite` | `S` | `isPlotkinOrder_MPair:378` |
| 19 | `MSub_isNormalIn` | `S` | `isPlotkinOrder_MPair:378`; `Colimit.isNormalIn_range_stgEmb:513` |
| 20 | `mem_MSub_of_subset` | `A` | not `@[simp]`; `MSub` membership introduction, body `⟨hb,hc⟩`; 0 citations |
| 21 | `isPlotkinOrder_MPair` | `S` | `thm29:476` |
| 22 | `isPlotkinOrder_image` | `S` | `thm29:477`; `Colimit.isBifinite_V:780` |
| 23 | `isPlotkinOrder_univ_subtype` | `S` | `thm29:476` |
| 24 | `principal_le_principal_iff` | `S` | `thm29:478`; `Colimit.isBifinite_V:782`, `toCompacts_le_iff:914`, `principal_pointB1_ne_bot:996` |
| 25 | `nonempty_domain_plus` | `P` | §7.4: "we define `D⁺` to be the **domain** of ideals over `⟨M(A),⊢⟩`"; 0 citations, terminal |
| 26 | `thm29` | `P` | **Theorem 29, first sentence**, verified against p. 42 of the PDF; cited by `Colimit.isBifinite_plus_V:947` |

### 3.2 `Colimit.lean` — 73

| # | Declaration | Label | Evidence |
| -- | ----------- | ----- | -------- |
| 1 | `mpairMap_base` | `A` | `@[simp]`; 0 citations |
| 2 | `mpairMap_cover` | `A` | `@[simp]`; `mpairMap_congr:252`, `mpairMap_trans:262` |
| 3 | `mem_upper_of_mem_cover` | `S` | `upper_mpairMap_subset:181` |
| 4 | `mem_upper_mpairMap` | `S` | `upper_mpairMap_eq_iff:189`, `mpairMap_le_mpairMap_iff:202,205` |
| 5 | `upper_mpairMap_subset` | `S` | `upper_mpairMap_eq_iff:191,192` |
| 6 | `upper_mpairMap_eq_iff` | `S` | `mpairMap_le_mpairMap_iff:203,206` |
| 7 | `mpairMap_le_mpairMap_iff` | `S` | `stepEmb:413–415`, `expandSucc:813,814`, `expandStg_le_iff_same:860`, `isoPlus:942` |
| 8 | `range_mpairMap` | `S` | `surjective_mpairMap:246`, `isNormalIn_range_stgEmb:512`, `expand_surjective:897` |
| 9 | `mpairMap_eta` | `S` | `expandStg_stgEmb:834` |
| 10 | `surjective_mpairMap` | `S` | `isoPlus:943` |
| 11 | `mpairMap_congr` | `S` | `expandStg_stgEmb:842` |
| 12 | `mpairMap_trans` | `S` | `expandStg_stgEmb:840` |
| 13 | `isIdeal_image` | `S` | `idealCongr:311` |
| 14 | `isIdeal_preimage` | `S` | `idealCongr:312` |
| 15 | `isNormalIn_image_range` | `S` | `isNormalIn_range_liftStg:587` |
| 16 | `isNormalIn_image_univ` | `S` | `isNormalIn_range_stgEmb:524` |
| 17 | `mk_surjective` | `S` | `isNormalIn_range_stgEmb:519`, `expandStg_stgEmb:838`, `expandStg_le_iff_same:858,859`, `expand_surjective:891`, `isoPlus:941`, `stg_one_eq:971` |
| 18 | `mk_le_mk` | `A` | `@[simp]`; `instOrderBotStep:394`, `expandSucc:813,814`, `isoPlus:941` |
| 19 | `bot_eq_mk_bot` | `A` | `@[simp]`; 0 citations |
| 20 | `stepEmb_mk` | `A` | `@[simp]`; 0 citations |
| 21 | `range_stepEmb` | **`D`** | 0 citations. Its only would-be caller, `isNormalIn_range_stgEmb`, **re-derives the identical equation inline** as `hstep` at lines 514–522, since `stgEmb (n+1) = stepEmb (stgEmb n)`. One of the two should go; the inline one is 9 lines and the lemma is 8 |
| 22 | `stepEmb_bot` | `S` | `stgEmb_bot:495` |
| 23 | `Stg_zero` | `A` | not `@[simp]`; `rfl`; 0 citations |
| 24 | `Stg_succ` | `A` | not `@[simp]`; `rfl`; 0 proof citations (docstring 441) |
| 25 | `stgEmb_succ` | `A` | not `@[simp]`; `rfl`; 0 citations |
| 26 | `stgEmb_bot` | `S` | own recursion `:495`, `liftStg_bot:555`, `stgEmb_ne_mk_eta:625` |
| 27 | `isNormalIn_range_stgEmb` | `S` | own recursion `:513`, `isNormalIn_range_liftStg:588` |
| 28 | `liftStg_self` | `A` | `@[simp]`; `incl_le_incl:692`, `incl_lift:699,700`, `incl_zero_le:708`, `expandStg_lift:847`, `liftStg_one_step:804` |
| 29 | `liftStg_succ` | `S` | `liftStg_le_liftStg:549`, `liftStg_bot:555`, `isNormalIn_range_liftStg:582,584`, `expandStg_lift:849`, `liftStg_one_step:804` |
| 30 | `liftStg_trans` | `S` | `germLE_at:650,651` |
| 31 | `liftStg_le_liftStg` | `S` | `liftEmb:559`, `germLE_at:651`, `isNormalIn_range_incl:739,740` |
| 32 | `liftStg_bot` | `S` | `incl_zero_le:708`, `incl_bot:719` |
| 33 | `liftEmb_apply` | `A` | `@[simp]`; 0 citations |
| 34 | `isNormalIn_range_liftStg` | `S` | `isNormalIn_range_incl:734` |
| 35 | `not_pointB1_le_bot` | `S` | `pointB1_ne_bot:614`, `stgEmb_ne_mk_eta:628` |
| 36 | `pointB1_ne_bot` | `S` | `stgEmb_ne_mk_eta:629`, `incl_pointB1_ne_bot:987` |
| 37 | `stgEmb_ne_mk_eta` | `P` | §7.4 **defect 3**: "each stage of the construction is embedded in the next one by the map `x ↦ (x,{x})`" is refuted at stage 1→2 by the kernel; 0 citations, terminal |
| 38 | `germLE_at` | `S` | `germLE_refl:655`, `germLE_trans:661,662`, `incl_le_incl_iff:687`, `expand:873,874` |
| 39 | `germLE_refl` | `S` | `instPreorderGerm:666` |
| 40 | `germLE_trans` | `S` | `instPreorderGerm:667` |
| 41 | `incl_surjective` | `S` | `incl_zero_le:707`, `isNormalIn_range_incl:728`, `expand_le_iff:880,881` |
| 42 | `incl_le_incl_iff` | `S` | `incl_le_incl:692`, `incl_lift:699,700`, `incl_zero_le:708`, `isNormalIn_range_incl:731,732,738`, `expand_le_iff:883` |
| 43 | `incl_le_incl` | `A` | `@[simp]`; `inclEmb:799`, `incl_injective:695`, `isNormalIn_range_incl:739,740` |
| 44 | `incl_injective` | `S` | `incl_pointB1_ne_bot:987` |
| 45 | `incl_lift` | `S` | `range_incl_subset:704`, `incl_bot:719`, `incl_stgEmb:807`; `LemThirty.exists_stage_ge_of_finite:446` |
| 46 | `range_incl_subset` | `S` | `exists_stage_of_finite:753,754` |
| 47 | `incl_zero_le` | `S` | `instOrderBotAinf:713` |
| 48 | `incl_bot` | `S` | `isNormalIn_range_incl:726`, `expandStg_stgEmb:836`, `incl_pointB1_ne_bot:986` |
| 49 | `isNormalIn_range_incl` | `S` | `isPlotkinOrder_Ainf:763` |
| 50 | `exists_stage_of_finite` | `S` | `isPlotkinOrder_Ainf:762`, `expand_surjective:894`; `LemThirty.exists_stage_ge_of_finite:443` |
| 51 | `isPlotkinOrder_Ainf` | `S` | `isBifinite_V:782` |
| 52 | `domain_V` | `P` | §7.4 constructs the fixed point as an operator **on domains** ("we define `D⁺` to be the domain of ideals"); `theorem`, not `instance`, so `LemThirty` resolves the instance directly — 0 proof citations, terminal |
| 53 | `isBifinite_V` | `S` | ten citers, all in `LemThirty`: `retracts_lift:323`, `retracts_prod:329`, `retracts_smyth:334`, `retracts_hoare:338`, `retracts_plotkin:344`, `retracts_smash:359`, `retracts_sepSum:364`, `retracts_coalSum:368`, `retracts_fun_of_boundedComplete:378`, `retracts_strictFun_of_boundedComplete:383` |
| 54 | `inclEmb_apply` | `A` | `@[simp]`; 0 citations |
| 55 | `liftStg_one_step` | `S` | `incl_stgEmb:807` |
| 56 | `incl_stgEmb` | `S` | `expandStg_stgEmb:842` |
| 57 | `expandStg_zero` | `A` | `@[simp]`; `expandStg_stgEmb:832` |
| 58 | `expandStg_mk` | `A` | `@[simp]`; `expand_surjective:899` |
| 59 | `expandStg_stgEmb` | `S` | `expandStg_lift:849` |
| 60 | `expandStg_lift` | `S` | `expandStg_le_iff:864` (twice) |
| 61 | `expandStg_le_iff_same` | `S` | `expandStg_le_iff:864` |
| 62 | `expandStg_le_iff` | `S` | `expand:872,874`, `expand_le_iff:882` |
| 63 | `expand_incl` | `A` | `@[simp]`; `expand_le_iff:882`, `expand_surjective:899` |
| 64 | `expand_le_iff` | `S` | `isoPlus:940` |
| 65 | `expand_surjective` | `S` | `isoPlus:940` |
| 66 | `toCompacts_le_iff` | `S` | `toCompactsEmb:923` |
| 67 | `toCompacts_surjective` | `S` | `isoPlus:943` |
| 68 | `toCompactsEmb_apply` | `A` | `@[simp]`; 0 citations |
| 69 | `isBifinite_plus_V` | **`U`**-speculative | 0 citations; body is `thm29 V isBifinite_V`, one application. The docstring calls it a "consistency check"; it re-states row 26 of §3.1 at `D = V` and nothing consumes it |
| 70 | `iso_plus_V` | `P` | §7.4's "how the desired fixed point is obtained" — `V ≅ V⁺`, and it is the hypothesis `D ≅ D⁺` of Theorem 29's second sentence; 0 proof citations, terminal |
| 71 | `stg_one_eq` | **`D`** | duplicate of `BifiniteUniversal.mpair_punit_eq` (§3.1 row 17). `Stg 1 = Antisymmetrization (MPair (Stg 0))` and `Stg 0` is definitionally `PUnit`, so this follows from `mpair_punit_eq` with `mk_surjective`; instead it re-runs the same `Finset.eq_empty_or_nonempty` + `Subsingleton.elim` script. Both assert §7.4's count 2. 0 citations |
| 72 | `incl_pointB1_ne_bot` | `S` | `principal_pointB1_ne_bot:993` |
| 73 | `principal_pointB1_ne_bot` | `U`-terminal | 0 citations; the nondegeneracy check the docstring calls for — "`V ≅ V⁺` would hold vacuously of a one-point domain". Keep |

### 3.3 `LemThirty.lean` — 37

Nothing in the package imports `LemThirty.lean`; it is a leaf. Every "0
citations" below is therefore package-wide.

| # | Declaration | Label | Evidence |
| -- | ----------- | ----- | -------- |
| 1 | `plotkinOp_carrier` | `A` | `@[simp]`; 0 citations |
| 2 | `domain_plotkinOp` | `U`-speculative | 0 proof citations (docstring 182). Records where `[Domain D]` is spent; body is `inferInstance` |
| 3 | `lemma30_of` | `P` | **Lemma 30**, ten-fold; the arity is the kernel's check on the printed operator line, verified this round against p. 43 (ten slots); 0 citations, terminal |
| 4 | `lemma30_iff_lemma28_and_plotkin` | `P` | §7.4: Lemma 30's list is Lemma 28's nine plus `(·)♮`; 0 citations, terminal |
| 5 | `thm29SecondAtDomains_of_thm29Second` | `U`-speculative | 0 proof citations. Everything downstream uses `thm29SecondAtDomains_of_thm29Normal` (row 35) instead |
| 6 | `retracts_of_isBifinite` | `S` | rows 13,14,15,16,17 below |
| 7 | `retracts_of_isDomain` | `S` | rows 8,9,10,11,12 below |
| 8 | `retracts_lift` | `S` | `rep_lift_V:403` |
| 9 | `retracts_prod` | `S` | `rep_prod_V:409` |
| 10 | `retracts_smyth` | `P` | Lemma 30 conjunct 8's retraction pair, §7.4's printed recipe "take a pair of continuous functions `Φ`, `Ψ` …"; 0 citations |
| 11 | `retracts_hoare` | `P` | conjunct 9; 0 citations |
| 12 | `retracts_plotkin` | `P` | conjunct 10 — the pair §7.4 displays in full on p. 43; 0 citations |
| 13 | `retracts_smash` | `P` | conjunct 4; 0 citations |
| 14 | `retracts_sepSum` | `P` | conjunct 5; 0 citations |
| 15 | `retracts_coalSum` | `P` | conjunct 6; 0 citations |
| 16 | `retracts_fun_of_boundedComplete` | `P` | conjunct 1, with the development's `[BoundedComplete V]` kept in the signature; 0 citations. See §6 — the instance is arguably unsatisfiable, deliberately |
| 17 | `retracts_strictFun_of_boundedComplete` | `P` | conjunct 2, same; 0 citations |
| 18 | `rep_lift_V` | `P` | Lemma 30 conjunct 7, conditional on `Thm29SecondAtDomains`; cited by row 36 |
| 19 | `rep_prod_V` | `P` | Lemma 30 conjunct 3, same; cited by row 37 |
| 20 | `exists_stage_ge_of_finite` | `U`-terminal | 0 proof citations. A measurement: the stages are already cofinal among finite subsets of `A∞`, so the r0036 plan's location of the gap was wrong. Keep — it is the record |
| 21 | `monotone_of_reflects` | `U`-speculative | 0 citations anywhere; one-line utility. Its neighbour `injective_of_reflects` does have a consumer |
| 22 | `injective_of_reflects` | `S` | `countable_compacts_of_reflects:515` |
| 23 | `countable_compacts_of_reflects` | `U`-terminal | 0 proof citations (docstrings 148, 269, 460, 511). It is the recorded reason `Thm29Normal` carries `[Domain E]` — without it the statement is refutable, not open. Keep |
| 24 | `map_bot_of_normal` | `S` | `isIdeal_projSet:576` |
| 25 | `isIdeal_embSet` | `S` | `embIdeal:549` |
| 26 | `mem_embIdeal` | `A` | `@[simp]`; 0 citations (the `ext=1` reported by the final-component matcher is `Dyadic.mem_embIdeal`, a different declaration — see §5) |
| 27 | `embIdeal_mono` | `S` | `scottContinuous_embIdeal:629` |
| 28 | `isIdeal_projSet` | `S` | `projIdeal:589` |
| 29 | `mem_projIdeal` | `A` | `@[simp]`; 0 citations |
| 30 | `projIdeal_embIdeal` | `S` | `exists_embeddingProjectionPair_of_thm29Normal:693` |
| 31 | `embIdeal_projIdeal_le` | `S` | `exists_embeddingProjectionPair_of_thm29Normal:697` |
| 32 | `scottContinuous_embIdeal` | `S` | `exists_embeddingProjectionPair_of_thm29Normal:674` |
| 33 | `scottContinuous_projIdeal` | `S` | `exists_embeddingProjectionPair_of_thm29Normal:679` |
| 34 | `exists_embeddingProjectionPair_of_thm29Normal` | `S` | `thm29SecondAtDomains_of_thm29Normal:709` |
| 35 | `thm29SecondAtDomains_of_thm29Normal` | `S` | rows 36, 37 |
| 36 | `rep_lift_V_of_thm29Normal` | `U`-speculative | 0 citations; body is `rep_lift_V (thm29SecondAtDomains_of_thm29Normal h)`, one application of two existing theorems |
| 37 | `rep_prod_V_of_thm29Normal` | `U`-speculative | 0 citations; same shape |

### 3.4 `JungSFP.lean` — 23

| # | Declaration | Label | Evidence |
| -- | ----------- | ----- | -------- |
| 1 | `isCompactElement_of_minimal_upperBounds` | `S` | `mem_minimalUpperBounds_of_minimal:177`, `lemma213:519`, `lemma217:849` |
| 2 | `minimal_upperBounds_of_mem_minimalUpperBounds` | `S` | `lemma213:493,512`, `lemma217:792`; `JungFinite.apply_eq_self_of_mem_mubIter_compacts:552` |
| 3 | `mem_minimalUpperBounds_of_minimal` | `S` | `JungNets.hasCompleteMub_of_hasChainInfima:278` |
| 4 | `exists_mem_minimalUpperBounds_le` | `S` | `lemma217:798` |
| 5 | `jungFun_of_both` | `A` | not `@[simp]`; defining case equation; 15 uses |
| 6 | `jungFun_of_left` | `A` | not `@[simp]`; 10 uses |
| 7 | `jungFun_of_right` | `A` | not `@[simp]`; 10 uses |
| 8 | `jungFun_of_neither` | `A` | not `@[simp]`; 7 uses |
| 9 | `jungFun_congr` | `S` | `lemma213:618` |
| 10 | `exists_mem_of_isLUB_pair` | `S` | `exists_eq_of_forall_minimal:438`, `lemma213:505,552,597`, `lemma217:836` |
| 11 | `IsJungPatch.monotone` | `S` | `IsJungPatch.scottContinuous:300`. The 169 external "uses" the final-component matcher reports are occurrences of the word `monotone`, not of this lemma |
| 12 | `IsJungPatch.scottContinuous` | `S` | `jungHom:326`. Same collision caveat (86 reported) |
| 13 | `coe_jungHom` | `A` | `@[simp]`; `lemma217:876` |
| 14 | `step_le_jungHom` | `S` | `minimal_upperBounds_jungHom:367` |
| 15 | `minimal_upperBounds_jungHom` | `S` | `lemma213:511`, `lemma217:850` |
| 16 | `fVal_pos` | `A` | not `@[simp]`; defining case equation; 6 uses |
| 17 | `fVal_neg` | `A` | not `@[simp]`; 8 uses |
| 18 | `exists_eq_of_forall_minimal` | `S` | `lemma213:564` |
| 19 | `lemma213` | `S` | `thm214:703`, `lemma217:785` |
| 20 | `thm214` | `U`-terminal | **0 proof citations package-wide** — every one of its nine mentions is docstring prose. `lemma217:782–785` re-derives the branch it needs (`HasAtMostOneMubBelow` from an infinite `mub`) directly from `lemma213`, and `JungFinite.thm18_of_propertyM` never calls it. It is Jung's Theorem 2.14 stated and proved; keep as the recorded bifurcation, but note that the route to Theorem 18 does not pass through it |
| 21 | `sVal_pos` | `A` | not `@[simp]`; 6 uses |
| 22 | `sVal_neg` | `A` | not `@[simp]`; 5 uses |
| 23 | `lemma217` | `S` | `JungNets.lemma217_of_thm137:350`; `JungFinite.thm18_of_propertyM:703` |

### 3.5 `JungFinite.lean` — 20 live (+1 already retired)

| # | Declaration | Label | Evidence |
| -- | ----------- | ----- | -------- |
| 1 | `exists_finite_complete_upperBoundsIn` | `S` | `minimalUpperBounds_finite_of_pairs:201` |
| 2 | `minimalUpperBounds_finite_of_pairs` | `S` | `lemma129:236` |
| 3 | `minimalUpperBounds_compacts_empty` | `S` | `lemma129:237` |
| 4 | `lemma129` | `S` | `thm18_of_propertyM:708` |
| 5 | `climbDown_mem` | `S` | `subset_biUnion_desc:309`, `desc_subset_insert_biUnion:324` |
| — | `climbDown_le` | — | **already retired**: inside a `/- … -/` block at lines 284–300 with a note, exactly the r0020 method. Not counted in the 20; `module-counts.sh` still counts it |
| 6 | `subset_biUnion_desc` | `S` | `exists_monotone_seq:379` |
| 7 | `desc_subset_insert_biUnion` | `S` | `exists_monotone_seq:388` |
| 8 | `exists_monotone_seq` | `S` | `exists_strictMono_mem_mubClosure:516` |
| 9 | `mubStep_finite` | `S` | `mubIter_finite:445` |
| 10 | `mubIter_finite` | `S` | own recursion `:445`, `exists_strictMono_mem_mubClosure:504` |
| 11 | `mubDiff_subset_mubClosure` | `S` | `exists_strictMono_mem_mubClosure:519` |
| 12 | `mubDiff_finite` | `S` | `exists_strictMono_mem_mubClosure:517` |
| 13 | `mubDiff_nonempty` | `S` | `exists_strictMono_mem_mubClosure:517` |
| 14 | `exists_mem_mubDiff_le` | `S` | `exists_strictMono_mem_mubClosure:518` |
| 15 | `mubDiff_ne` | `S` | `exists_strictMono_mem_mubClosure:521` |
| 16 | `exists_strictMono_mem_mubClosure` | `S` | `lemma22:647` |
| 17 | `apply_eq_self_of_mem_mubIter_compacts` | `S` | `apply_eq_self_of_mem_mubClosure_compacts:563` |
| 18 | `apply_eq_self_of_mem_mubClosure_compacts` | `S` | `lemma22:652` |
| 19 | `lemma22` | `S` | `thm18_of_propertyM:710` |
| 20 | `thm18_of_propertyM` | `P` | **Theorem 18**, §6: "If `D` and `D → D` are domains, then `D` is bifinite", verified against p. 32 of the PDF, conditional on two named hypotheses; 0 citations, terminal by design |

This module is the cleanest in the area: **19 of 20 are `S`, the twentieth is the
paper's theorem**, and its one already-retired declaration was retired the right
way. Zero `U`, zero `D`, zero `A`.

### 3.6 `JungNets.lean` — 10 live (12 reported)

| # | Declaration | Label | Evidence |
| -- | ----------- | ----- | -------- |
| 1 | `IsBicomplete.hasChainInfima` | `S` | `IsBicomplete.exists_minimal_upperBounds_le:258`, `Thm137.toChains:322` |
| 2 | `exists_minimal_mem` | `S` | `exists_minimal_upperBounds_le:250` |
| 3 | `exists_minimal_upperBounds_le` | `S` | `IsBicomplete.exists_minimal_upperBounds_le:258`, `hasCompleteMub_of_hasChainInfima:277` |
| 4 | `IsBicomplete.exists_minimal_upperBounds_le` | `U`-speculative | 0 citations. It is row 3 restated at the strictly **stronger** hypothesis `IsBicomplete`; the module's own docstring §2 argues at length that `HasChainInfima` is the honest hypothesis. Keeping the weaker theorem beside the stronger one, with no consumer, is the mirror image of `W` |
| 5 | `hasCompleteMub_of_hasChainInfima` | `S` | `hasCompleteMub_pair:285`, `forall_hasCompleteMub_of_thm137:338` |
| 6 | `hasCompleteMub_pair` | `S` | `lemma217_of_thm137:351` |
| 7 | `Thm137.toChains` | `S` | `forall_hasCompleteMub_of_thm137:338`, `lemma217_of_thm137:351` |
| 8 | `forall_hasCompleteMub_of_thm137` | `U`-speculative | 0 citations — **and this is the seam between the two r0037 agents.** Its conclusion is `JungFinite.thm18_of_propertyM`'s hypothesis `hm` with the two arguments transposed. See §4 |
| 9 | `lemma217_of_thm137` | **`D`** | with row 10; interderivable in one application each, proved in `ScottDomains/Audit/Bifinite.lean`. Its only citer is row 10 |
| 10 | `propertyM_pairs_of_thm137` | **`D`** | with row 9; 0 citations. Body is `fun _ _ hx₁ hx₂ => lemma217_of_thm137 h hAlg hCount hx₁ hx₂` — an η-expansion of row 9 with the pair moved from the implicit telescope to an explicit `∀` |
| — | lines 29, 76 | — | prose inside doc comments, counted as declarations by `module-counts.sh`. Not declarations |

### 3.7 `ContinuousConstruction.lean` — 35

Imported by exactly one file, `JungFinite.lean`. Grouped by the module's own
three sections so the verdict in §7 reads off the table.

**Group I — the `familyFun` constructor (11).**

| # | Declaration | Label | Evidence |
| -- | ----------- | ----- | -------- |
| 1 | `mem_valuesAt` | `A` | not `@[simp]`; `Iff.rfl`; 0 citations |
| 2 | `mem_valuesAt_of_mem` | `S` | `le_familyFun:151`, `directedOn_valuesAt_of_comparable:331,332` |
| 3 | `valuesAt_mono_family` | `U`-speculative | 0 citations |
| 4 | `valuesAt_mono_point` | `S` | `monotone_familyFun:154` |
| 5 | `isLUB_familyFun` | `S` | `le_familyFun:151`, `monotone_familyFun:154`, `familyFun_le_iff:165`, `scottContinuous_familyFun:183`, `isLUB_basisExtension:279`, `shift_apply_le:361`, `shift_chain:370` |
| 6 | `le_familyFun` | `S` | `familyFun_le_iff:163`, `scottContinuous_familyFun:186`, `isLUB_of_iUnion:221,228` |
| 7 | `monotone_familyFun` | `S` | `scottContinuous_familyFun:181`, `isLUB_of_iUnion:220` |
| 8 | `familyFun_le_iff` | `S` | `isLUB_of_iUnion:220,225` |
| 9 | `scottContinuous_familyFun` | `S` | `family:190` |
| 10 | `coe_family` | `A` | `@[simp]`; 0 citations |
| 11 | `isLUB_of_iUnion` | `U`-speculative | 0 proof citations (docstring 46). Nothing in the package takes a union of families |

**Group II — the two classes of admissible family (11).**

| # | Declaration | Label | Evidence |
| -- | ----------- | ----- | -------- |
| 12 | `valuesAt_graphOn` | `S` | `directedOn_valuesAt_graphOn:262`, `isLUB_basisExtension:278` |
| 13 | `directedOn_valuesAt_graphOn` | `S` | `basisExtension:271`, `isLUB_basisExtension:279` |
| 14 | `coe_basisExtension` | `A` | `@[simp]`; 0 citations |
| 15 | `isLUB_basisExtension` | `S` | `basisExtension_apply_of_isCompactElement:285`, `eq_basisExtension_of_eqOn:302` |
| 16 | `basisExtension_apply_of_isCompactElement` | `U`-speculative | 0 citations |
| 17 | `eq_basisExtension_of_eqOn` | `S` | `coe_eq_basisExtension_self:309` |
| 18 | `coe_eq_basisExtension_self` | `U`-speculative | 0 proof citations (docstring 58). **But see §7(c)**: it is `CompactFunction.lean`'s decomposition without `[BoundedComplete β]` — a strengthening of a foundation result, not Theorem 18 machinery. Relocate rather than retire |
| 19 | `directedOn_valuesAt_of_comparable` | `S` | `directedOn_valuesAt_chainFamily:345` |
| 20 | `directedOn_valuesAt_chainFamily` | `S` | `shift:356`, `shift_apply_le:361`, `shift_chain:370` |
| 21 | `shift_apply_le` | `U`-speculative | 0 citations. The §6.2 perturbation r0028 asked for; the Jung route never builds one |
| 22 | `shift_chain` | `U`-speculative | 0 citations. Same |

**Group III — the Figure 3 reduction and the live citation (13).**

| # | Declaration | Label | Evidence |
| -- | ----------- | ----- | -------- |
| 23 | `idHom_apply` | `A` | `@[simp]`; 0 citations |
| 24 | `le_idHom_iff` | `A` | not `@[simp]`; `Iff.rfl` unfolding of "deflation"; 0 citations |
| 25 | `diagStep_of_isCompactElement` | `S` | `isCompactElement_diagStep:413`, `diagStep_le_iff:420` |
| 26 | `isCompactElement_diagStep` | `S` | `exists_isCompactElement_le:438` |
| 27 | `diagStep_le_iff` | `S` | `exists_isCompactElement_le:439,443` |
| 28 | `exists_isCompactElement_le` | `S` | **`JungFinite.lemma22:649` — the only live-route citation of this module.** Jung's step 4, move 2 |
| 29 | `apply_mem_upperBounds` | `S` | `hasCompleteMub_of_finite_image:479,484`, `minimalUpperBounds_subset_image:496` |
| 30 | `hasCompleteMub_of_finite_image` | `S` | `isBifinite_of_exists_finite_projection:602` |
| 31 | `minimalUpperBounds_subset_image` | `S` | `isBifinite_of_exists_finite_projection:600`. Named in `Section62.lean:452` prose but not used there |
| 32 | `exists_strictAnti_of_not_hasCompleteMub` | `U`-terminal | 0 proof citations (docstring 89). The recorded other side of the intended contradiction. Keep |
| 33 | `isCompactElement_of_mem_range` | `S` | `range_subset_compacts:574` |
| 34 | `range_subset_compacts` | `S` | `isBifinite_of_exists_finite_projection:592` |
| 35 | `isBifinite_of_exists_finite_projection` | `U`-terminal | 0 citations. The converse: the finiteness Smyth's argument must produce is *sufficient* for bifiniteness. No other module states it. Keep |

## 4. Second question: the three Jung modules, written by two agents in two rounds

**No theorem is duplicated between `JungSFP` (r0036) and `JungFinite`/`JungNets`
(r0037).** Around minimal upper bounds specifically, the two agents' work
composes correctly rather than overlapping:

| # | Declaration | Direction | Note |
| -- | ----------- | --------- | ---- |
| 1 | `JungSFP.exists_mem_minimalUpperBounds_le` | *consumes* `HasCompleteMub` | converts the relative quantifier to the absolute one |
| 2 | `JungNets.exists_minimal_upperBounds_le` | *produces* the same shape | from `HasChainInfima`, by Zorn downwards |
| 3 | `JungNets.hasCompleteMub_of_hasChainInfima` | the join | calls `JungSFP.mem_minimalUpperBounds_of_minimal` to land in row 1's shape |

The third source the plan flagged, `MinimalUpperBounds.lean` (agent2), supplies
only the **definitions** — `upperBoundsIn`, `minimalUpperBounds`,
`HasCompleteMub`, `mubStep`, `mubIter`, `mubClosure`,
`isBifinite_iff_mubClosure`. All three Jung modules import them; none restates
one. **No duplication across that boundary.**

What the two agents did miss is each other's *interface*:

**4.1 The missing composition (one line).** `JungNets.forall_hasCompleteMub_of_thm137`
concludes

    ∀ v : Set D, v.Finite → v ⊆ compacts D → HasCompleteMub (compacts D) v

and `JungFinite.thm18_of_propertyM`'s hypothesis `hm` is

    ∀ v : Set α, v ⊆ compacts α → v.Finite → HasCompleteMub (compacts α) v

— the same proposition with the two arguments transposed. Nothing composes them.
There is no `thm18_of_thm137`, and that is exactly why
`forall_hasCompleteMub_of_thm137` has zero citations. Adding the composition
would reduce Theorem 18 to **two named propositions**, `JungNets.Thm137` and
`JungFinite.FixedPointOfCompactDeflationIsCompact`, which is a strictly sharper
statement of where the development stands than either file gives alone.
**Recommended for the follow-on round.**

**4.2 The `D` pair, with a kernel-checked proof.** `JungNets.lemma217_of_thm137`
and `JungNets.propertyM_pairs_of_thm137` are each one application of the other.
`ScottDomains/ScottDomains/Audit/Bifinite.lean` proves both directions;
`propertyM_pairs_from_lemma217`'s proof term is character-for-character the body
of `propertyM_pairs_of_thm137` itself. `propertyM_pairs_of_thm137` has zero
citations and `lemma217_of_thm137`'s only citer is `propertyM_pairs_of_thm137`,
so retiring either costs nothing consumed.

**4.3 The same step proved a third time, inline.**
`JungFinite.thm18_of_propertyM:700–705` derives property M at pairs from `hm` via
`JungSFP.lemma217`, without calling either member of the `D` pair — a third
instance of the identical two-line derivation.

**4.4 One repeated argument across four declarations** (a pattern, not a
duplication). "Minimality inside a finite complete set of upper bounds upgrades
to minimality outright" is proved four times, and three of the four docstrings
name one of the others as "the same step":

| # | Declaration | Module | Owner |
| -- | ----------- | ------ | ----- |
| 1 | `hasCompleteMub_of_isNormalIn` | `MinimalUpperBounds.lean` | agent2 |
| 2 | `hasCompleteMub_of_finite_image` | `ContinuousConstruction.lean` | agent6 |
| 3 | `exists_finite_complete_upperBoundsIn` | `JungFinite.lean` | agent6 |
| 4 | `minimalUpperBounds_finite_of_pairs` | `JungFinite.lean` | agent6 |

One lemma stated over an abstract finite complete set of upper bounds would
subsume all four. This straddles the agent2/agent6 boundary.

## 5. Cross-boundary duplicate the orchestrator should see (agent5 ↔ agent6)

`LemThirty.lean`'s universality machinery and `Dyadic.lean`'s (agent5's area) are
**the same construction under the same names at two different universal
domains** — §7.4's bifinite `V` and §7.3's bounded-complete `U`:

| # | `LemThirty` (over `A∞`, `V`) | `Dyadic` (over `U₀`, `U`) |
| -- | -------------------------- | ------------------------ |
| 1 | `embSet` (def) | `embSet` (def) |
| 2 | `isIdeal_embSet` | `isIdeal_embSet` |
| 3 | `embIdeal` (def) | `embIdeal` (def) |
| 4 | `mem_embIdeal` | `mem_embIdeal` |
| 5 | `embIdeal_mono` | `embIdeal_mono` |
| 6 | `scottContinuous_embIdeal` | `scottContinuous_embIdeal` |
| 7 | `projSet` (def) | `projSet` (def) |
| 8 | `projIdeal_embIdeal` | `projSet_embIdeal` / `projElem_embIdeal` |
| 9 | `embIdeal_projIdeal_le` | `embIdeal_projElem_le` |

Seven theorem-level pairs plus three definition pairs. They are not literal
duplicates: `LemThirty`'s take an abstract order-reflecting `f : K(E) → A∞` and
an **ideal**, `Dyadic`'s a fixed `φ` into `U₀` and an **element**. `LemThirty`'s
is the more general of the two, and `Dyadic`'s element form is `LemThirty`'s
ideal form precomposed with `idealOfElem`. Neither agent5 nor agent6 can see both
sides. This is the largest single duplication I found and it is exactly the
tier-2 case the plan anticipates. If one version parameterized by (carrier,
order-reflecting map) subsumes both, it removes about seven theorems from the
1308.

## 6. `W`: none found, two near-misses named

No declaration in this area meets `W`'s definition — a hypothesis in the
statement that no call site supplies. Two things worth the orchestrator's
attention are adjacent to it but are not `W`:

| # | Declaration | Why not `W` |
| -- | ----------- | ----------- |
| 1 | `JungNets.IsBicomplete.exists_minimal_upperBounds_le` | the mirror image: its hypothesis is *stronger* than the one next to it, and nothing consumes it. Labelled `U` |
| 2 | `LemThirty.retracts_fun_of_boundedComplete`, `retracts_strictFun_of_boundedComplete` | carry `[BoundedComplete V]`, which the module's own docstring argues **cannot hold** if `Thm29Second` does, since `PRep.boundedComplete_range` would then force every bifinite domain to be bounded complete. That is stronger than "no call site supplies it", and it is stated deliberately to keep the obstruction in the signature rather than in a comment. Labelled `P` |

## 7. Verdict on `ContinuousConstruction` (35 theorems)

### 7.1 The measurements the verdict rests on

| # | Measurement | Value |
| -- | ----------- | ----- |
| 1 | Files importing `ContinuousConstruction` | **1** (`JungFinite.lean:1`) |
| 2 | Its theorems cited by the live route | **1** — `exists_isCompactElement_le`, at `JungFinite.lemma22:649` |
| 3 | Other symbols `JungFinite` takes from it | the definition `idHom` only |
| 4 | Its theorems named in `Section62.lean` | 2, both in **prose** (lines 229, 452); zero Lean uses |
| 5 | Internal dependency closure of the one live citation | 3 further theorems (`diagStep_of_isCompactElement`, `isCompactElement_diagStep`, `diagStep_le_iff`) + the defs `idHom`, `diagStep` |
| 6 | Theorems of the `familyFun` constructor and its two classes with **any** consumer outside their own module | **0** |
| 7 | `U`-labelled theorems | 8 of 35 (6 speculative, 2 terminal) |

### 7.2 What the paper says, checked this round

Gunter & Scott p. 32, verified against `papers/Gunter Scott 1990.pdf`:

> **Theorem 18** If `D` and `D → D` are domains, then `D` is bifinite.
> The theorem is due to Smyth and its proof may be found in [Smy83a]. **It is
> carried out by analyzing each of the cases pictured in Figure 3** and showing
> that if `D → D` is not a domain, then `D` cannot be bifinite.

So the Figure 3 case analysis is **the paper's own stated proof method** for
Theorem 18. Jung's route is an alternative found later. A precise record of where
the paper's own method stops is therefore a statement about the paper, not a
statement about a failed attempt in this development, and it is what the
project's practice keeps.

### 7.3 The verdict, in three parts

**Is the module still needed? Yes — but at roughly one third its size. It is not
removable: deleting it breaks `JungFinite.lemma22`, hence Theorem 18's
assembly.**

| # | Group | Count | Disposition |
| -- | ----- | ----- | ----------- |
| a | **Live route** | **4** | Keep as is |
| b | **Recorded dead end (paper's own method)** | **8** | Keep as is |
| c | **Neither** | **23** | 21 to retire the r0020 way; 2 to relocate |

**(a) Live — 4 theorems, keep.** `exists_isCompactElement_le`,
`diagStep_of_isCompactElement`, `isCompactElement_diagStep`, `diagStep_le_iff`,
with the definitions `idHom` and `diagStep`. This is Jung's step 4 move 2 and it
compiles nothing without it.

**(b) Recorded dead end — 8 theorems, keep.** `apply_mem_upperBounds`,
`hasCompleteMub_of_finite_image`, `minimalUpperBounds_subset_image`,
`exists_strictAnti_of_not_hasCompleteMub`, `isCompactElement_of_mem_range`,
`range_subset_compacts`, `isBifinite_of_exists_finite_projection`,
`le_idHom_iff`. Three reasons to keep, all measured:

1. it is the reduction of the paper's own Figure 3(a) **and** 3(b) to a single
   statement, (★), and the module's docstring names the failing step exactly;
2. r0036 measured (★) as *equivalent* to Theorem 18 rather than below it
   (`Section62.lean:212–214`). That measurement is only meaningful because this
   module states (★) precisely; erasing the statement erases the measurement's
   subject;
3. `isBifinite_of_exists_finite_projection` proves the finiteness the method asks
   for is **sufficient** for bifiniteness, which no other module in the
   development states.

**(c) Neither — 23 theorems.** The whole `familyFun` constructor (rows 1–11 of
§3.7), the basis-extension class (rows 12–18), the chain class (rows 19–22), and
`idHom_apply`. This is r0028's stated missing prerequisite — "the least
continuous function above a given monotone partial assignment on `K(D)`" — and
the §6.2 perturbation `shift`. It is correct, it is `sorry`-free, and **nothing
in the package consumes any of it**, because the Jung route obtains its deflation
from algebraicity of `[D → D]` rather than by assembling a family of step
functions. Recommendation, following r0020:

* **retire 21 in place** — comment out with the existing docstring paragraphs as
  the note, rebuild, confirm the build is unchanged, which will also confirm that
  the three `@[simp]` lemmas among them (`coe_family`, `coe_basisExtension`,
  `idHom_apply`) were never firing;
* **relocate 2** — `eq_basisExtension_of_eqOn` and `coe_eq_basisExtension_self`
  belong next to `CompactFunction.lean`. Together they say that every continuous
  function is the basis extension of its own restriction to `K(D)` **with no
  `[BoundedComplete β]`**, where `CompactFunction.lean` obtains the same
  decomposition only under that instance. That is a strengthening of the
  development's own foundations, independent of Theorem 18, and it is the one
  thing in group (c) that would be a real loss.

Net: `ContinuousConstruction` shrinks from 35 to 12 theorems and stays.

## 8. The `U`/`D`/`W` list, consolidated

**`D` — 4.**

| # | Declaration | Module | Duplicate of |
| -- | ----------- | ------ | ------------ |
| 1 | `range_stepEmb` | `Colimit` | the inline `hstep` in `isNormalIn_range_stgEmb:514–522` |
| 2 | `stg_one_eq` | `Colimit` | `BifiniteUniversal.mpair_punit_eq` |
| 3 | `lemma217_of_thm137` | `JungNets` | `propertyM_pairs_of_thm137` — proved in `Audit/Bifinite.lean` |
| 4 | `propertyM_pairs_of_thm137` | `JungNets` | `lemma217_of_thm137` — proved in `Audit/Bifinite.lean` |

**`U`-speculative — 14.**

| # | Declaration | Module | What it was written for |
| -- | ----------- | ------ | ----------------------- |
| 1 | `isBifinite_plus_V` | `Colimit` | a one-line consistency check of `thm29` at `D = V` |
| 2 | `domain_plotkinOp` | `LemThirty` | recording where `[Domain D]` is spent; `inferInstance` |
| 3 | `thm29SecondAtDomains_of_thm29Second` | `LemThirty` | the weakening step, superseded by `…_of_thm29Normal` |
| 4 | `monotone_of_reflects` | `LemThirty` | a utility whose neighbour got the caller |
| 5 | `rep_lift_V_of_thm29Normal` | `LemThirty` | a one-line composition |
| 6 | `rep_prod_V_of_thm29Normal` | `LemThirty` | a one-line composition |
| 7 | `IsBicomplete.exists_minimal_upperBounds_le` | `JungNets` | the `IsBicomplete` form of a theorem stated at the weaker `HasChainInfima` |
| 8 | `forall_hasCompleteMub_of_thm137` | `JungNets` | **the seam — connect it, do not retire it** (§4.1) |
| 9 | `valuesAt_mono_family` | `ContinuousConstruction` | family monotonicity; `valuesAt_mono_point` got the caller |
| 10 | `isLUB_of_iUnion` | `ContinuousConstruction` | unions of families; nothing takes one |
| 11 | `basisExtension_apply_of_isCompactElement` | `ContinuousConstruction` | the basis-extension class |
| 12 | `coe_eq_basisExtension_self` | `ContinuousConstruction` | **relocate, do not retire** (§7.3(c)) |
| 13 | `shift_apply_le` | `ContinuousConstruction` | §6.2's perturbation |
| 14 | `shift_chain` | `ContinuousConstruction` | §6.2's perturbation |

**`U`-terminal — 6, all recommended keep.** `Colimit.principal_pointB1_ne_bot`
(nondegeneracy of `isoPlus`); `LemThirty.exists_stage_ge_of_finite` and
`countable_compacts_of_reflects` (two measurements that locate the remaining gap);
`JungSFP.thm214` (Jung's Theorem 2.14, stated and proved, but the route to
Theorem 18 does not pass through it);
`ContinuousConstruction.exists_strictAnti_of_not_hasCompleteMub` and
`isBifinite_of_exists_finite_projection` (§7.3(b)).

**`W` — none.** §6.

## 9. Recommended actions, in cost order

| # | Action | Effect |
| -- | ------ | ------ |
| 1 | Fix the comment-block defect in `counts.sh` / `module-counts.sh` / `unused-theorems.sh` | corrects 1308 downward by ≥4; the other five streams may hold more |
| 2 | Add `JungFinite.thm18_of_thm137` (one line, §4.1) | gives `forall_hasCompleteMub_of_thm137` a consumer and reduces Theorem 18 to two named propositions |
| 3 | Retire one of the `JungNets` `D` pair (§4.2) | −1 theorem, evidence already kernel-checked |
| 4 | Retire `Colimit.range_stepEmb` **or** inline `hstep`; retire `Colimit.stg_one_eq` | −2 theorems |
| 5 | Retire the 21 `ContinuousConstruction` theorems of group (c), r0020's way; relocate 2 to `CompactFunction.lean` | −21 theorems; module 35 → 12 and stays |
| 6 | Retire `LemThirty`'s 5 speculative wrappers and `Colimit.isBifinite_plus_V` | −6 theorems |
| 7 | Tier-2 only: decide the `LemThirty`/`Dyadic` shared construction (§5) | up to −7 theorems, straddles agent5/agent6 |
| 8 | Tier-2 only: factor the four copies of the finite-complete-set argument (§4.4) | up to −3 theorems, straddles agent2/agent6 |

Actions 3–6 total **−30 of 224, 13.4%**, and none of them touches a paper
property, a proof of one, or a `sorry`.

## 10. State at close

| # | Measurement | Value |
| -- | ----------- | ----- |
| 1 | `.lean` files edited | 0 |
| 2 | `.lean` files added | 1 (`ScottDomains/ScottDomains/Audit/Bifinite.lean`, 2 theorems, no `sorry`, imported by nothing) |
| 3 | `lake build` | 1224 jobs, exit 0, zero errors, zero new warnings |
| 4 | `sorry` | 1, unchanged (`Skeleton/Section6.lean:197`) |
| 5 | Theorem total | 1308 → 1310 |
| 6 | Scripts added | `scripts/bifinite-audit-citations.sh`, `scripts/bifinite-audit-qualified.sh` |
| 7 | Commit | `3c55203` on branch `agent6`; not pushed, per the project's agent rule |
