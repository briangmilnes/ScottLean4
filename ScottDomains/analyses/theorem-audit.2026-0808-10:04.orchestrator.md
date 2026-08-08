# Theorem audit — consolidated, all six areas

Round r0038. Tier 2 of the two-tier artifact split: the per-declaration tables
live in `reports/r0038-report-from-agentN-…`, this file merges them and answers
the cross-area questions no single agent could see.

*(An interim version of this file, covering five areas, is in this file's git
history at `dcd1eec`.)*

## 1. The question

1308 theorem-ish declarations against a paper of ~100 atomic properties, a ratio
of 13.2 : 1. Is the development carrying theorems that serve neither a paper
property nor a proof of one?

## 2. The labels

| # | Area | Live decls | `P` | `S` | `A` | `U` | `D` | `W` |
| -- | ---- | ----: | ----: | ----: | ----: | ----: | ----: | ----: |
| 1 | Foundations (agent1) | 118 | 9 | 65 | 26 | 12 | 6 | 0 |
| 2 | Projections (agent2) | 184 | 28 | 119 | 22 | 9 | 4 | 2 |
| 3 | Skeleton (agent3) | 170 | 32 | 114 | 17 | 1 | 6 | 0¹ |
| 4 | Powerdomains (agent4) | 201 | 11 | 121 | 42 | 20 | 5 | 2 |
| 5 | §7 representability (agent5) | 400 | 18 | 301 | 54 | 21 | 6 | 0 |
| 6 | Bifinite (agent6) | 224 | 28 | 134 | 38 | 20 | 4 | 0 |
| — | **total** | **1297** | **126** | **854** | **199** | **83** | **31** | **4** |

¹ agent3 reports 6 declarations carrying surplus hypotheses, read off the proof
terms rather than kernel-checked, since confirming means editing a live
declaration and this round forbade that. Counted as a note, not as `W`.

**The `U` column over-reads, and every agent said so unprompted.** Stripping
theorems terminal by construction — nondegeneracy witnesses, refutation
witnesses, recorded dead ends — the r0020-comparable population is **about 46 of
1297, ≈3.5%**, against r0020's 3% on a body six times smaller.

**So the ratio is not bloat.** 13 : 1 is the cost of formalizing a paper that
elides its own foundations. The development is at roughly the speculative-API
rate it had at 199 theorems.

## 3. The largest finding: `@[simp]` tags that never fire

**Only agent5 measured this, and in its area 43 of 54 `@[simp]` tags fire
nowhere.** Measured, not inferred: one script elaborates a scratch copy with the
attribute groups deleted, another splices `attribute [-simp]` into every module
of the full reverse-dependency closure. `Combinator` is decisive — 25 tags,
nothing imports the module, all 25 removed and it still elaborates. Only
`PRepSum` (9) and `CombinatorRep` (2) carry load-bearing tags. **18 of the 43 are
additionally cited nowhere**, which is r0020's speculative API at six times its
scale.

That makes agent5's disjoint total **45 of 400, 11.25%** — three times the rate
the label table alone suggests.

**This is the audit's real gap.** The other five areas reported `A` counts but
did not test firing, so **199 `A` declarations development-wide are unmeasured
outside §7**. If §7's ratio holds elsewhere, the dead-tag population is far
larger than the `U` population. Re-running agent5's two scripts across the other
five areas is the single highest-value follow-up, and it costs no new judgement —
the method is mechanical and already written.

## 4. Duplication across module boundaries

31 declarations in ~21 pairs, and **none visible to `lake build`, because nothing
imports both sides.** That is the r0028 failure mode, which cost a round when it
last surfaced.

| # | Pair or family | Areas | Note |
| -- | -------------- | ----- | ---- |
| 1 | `smashPair` and its two lemmas, in `Skeleton/Sum` and `Isomorphism/StrictCurry` | 3 | defined character-for-character identically; one pair shares a name, only the namespace separating them |
| 2 | one upper-bound lemma declared **four times in three modules** | 2, 3 | two at the general hypothesis, two at the `t ⊆ s` case. Found by the elaborator, not grep: an unqualified name resolved to the wrong one |
| 3 | Theorem 11's second conjunct routed three ways across the powerdomains | 4 | collapsing onto `IdealCompletion.thm11` retires four |
| 4 | `Lift`'s two lemmas re-instantiated at `WithBot γ` in `Smash` and `CoalescedSum` | 1, 3, 5 | a *merge* across 26 call sites, not a deletion |
| 5 | `eq_kleeneOperator_op` vs `theorem3` | 1 | discharged by **`Iff.rfl`** — the same proposition |
| 6 | `LemThirty` and `Dyadic` carry the same ideal-completion construction under **the same seven names** | 5, 6 | `LemThirty`'s is the more general |
| 7 | `Powerdomain/Universal.repOf` family = `UniversalDomain.repFun` generalized | 4, 5 | 7 declarations; `repRangeOrderIso` is declared under that final name in **both** namespaces, so each masks the other's citation count |
| 8 | `PRepSum.projCpo` = `BifiniteUniversal.FpImage` under a second name | 5 | deleting `projCpo` collapses two further duplicates |
| 9 | `PRepSum.orderIso_apply_bot` re-proves **Mathlib's `OrderIso.map_bot`**; `isStrict_of_isProjection` is an unused rename of `IsProjection.map_bot` | 5 | the only duplications of Mathlib found |

Rows 6 and 7 are exactly what tier 2 exists for. Row 7 also means
`scripts/unused-theorems.sh` under-reports, as its own header warns.

**One repetition is larger than any pair.** A three-line "the image of a directed
set is directed" script occurs **28 times** across four §7 modules. The extracted
lemmas already exist — `CombinatorRep.directedOn_fst_val`/`directedOn_snd_val` —
and are cited **zero** times, because they were written at the `Fc(U)` index and
everyone since re-inlined at `Fp(U)`. Generalizing them deletes ~84 lines and
converts two `U` rows to `S`.

## 5. Findings that are not bloat

1. **A missing paper result, not dead code.** `ComputableFunction.lean` is
   imported by no module and `EffectivePresentation.lean` only by it — eight
   theorems with no external consumer — because the theorem that would consume
   them is **Theorem 7's second sentence**, formalized nowhere. Prove it.
2. **`ContinuousConstruction`: keep, at one third the size.** Deleting it breaks
   `JungFinite.lemma22`. Exactly **one** of its 35 theorems is cited by the live
   Theorem 18 route. 4 live; 8 a recorded dead end worth keeping (p. 32: the
   proof "is carried out by analyzing each of the cases pictured in Figure 3");
   23 neither, of which **2 should be relocated** — they give
   `CompactFunction.lean`'s decomposition without `[BoundedComplete β]`.
3. **One line reduces Theorem 18** to `Thm137` + `FixedPointOfCompactDeflationIsCompact`:
   `JungNets.forall_hasCompleteMub_of_thm137` concludes exactly
   `JungFinite.thm18_of_propertyM`'s `hm` with two arguments transposed.
   `scripts/check-thm18-composition.sh` already elaborates it; make it a library
   theorem.
4. **`W` traces to one false premise.** `Hoare.Powerdomain`'s *elaborated*
   signature does not take `[Domain D]`, contrary to what
   `instBoundedCompleteHoare`'s docstring gives as its reason for carrying it.
   Reading the source is not reading the signature — `variable` inclusion
   decides. `instBoundedCompleteHoare` is behavioural: an unconsumed `[Domain α]`
   restricts when the instance resolves, and its sibling already omits it.

## 6. Two refutations are prose, not kernel-checked

Recorded together because the pattern now has three instances and the project has
twice treated one of them as checked evidence.

| # | Refutation | Status |
| -- | ---------- | ------ |
| 1 | Theorem 26 is false for a signature admitting arity 0 | prose in the docstring, already flagged in `PaperInventory` |
| 2 | `Colimit.Thm29Second` is false without `[Domain E]` | `countable_compacts_of_reflects` is checked; the step from it is docstring prose |
| 3 | **the `⊗`/`⊕` counterexample refuting Lemma 28's closure reading** | **30 lines of docstring at `CombinatorRep.lean:504–533`, whose own text says "a hand computation, not Lean-checked"** |

Row 3 corrects the record: this project — including my own reporting of r0037 —
has repeatedly described that counterexample as load-bearing kernel-checked
evidence. It occupies **0 of `CombinatorRep`'s 28 theorems**. The conclusion it
supports is independently confirmed by proof (`⊗` and `⊕` *are* p-representable
at the projection notion, r0037), so nothing downstream is wrong; but the
counterexample itself should be put under the kernel or described accurately.

## 7. Where my own planning was wrong

The plan is not evidence. This round produced five corrections to it.

| # | My claim | Measured |
| -- | -------- | -------- |
| 1 | `ContinuousAlgebra` is "the highest ratio, the best place to find `U` and `W`" | zero `W`, 6.5% `U` — *below* its area average. Its 62-for-6 is a `FinSets` class stating Theorem 12 once instead of three times. The concentrations are `Smyth` (31%) and `Plotkin` (21%) |
| 2 | `Section62.apply_eq_self_of_mem_mubClosure` is consumed by `JungFinite` | **zero uses**; `JungFinite` declares its own `*_compacts` copies |
| 3 | the three Jung modules may duplicate each other | they duplicate **nothing**; what they missed was each other's *interface* |
| 4 | `PRep`/`PRepFun`/`PRepSum`/`Lemma28AtU` likely duplicate machinery | **refuted**: each instrument is declared once in `PRep` and consumed 4–7 times. The split is by operator, not by machinery, and no conjunct is proved twice |
| 5 | the `⊗`/`⊕` counterexample is load-bearing evidence to protect | it is a docstring; see §6 |

## 8. Defects in my own measurement scripts

Five agents found three independent defects. `counts.sh` and `module-counts.sh`
match `^(@\[…\] )?(theorem|lemma) ` and therefore count:

| # | Defect | Found by | Effect |
| -- | ------ | -------- | ------ |
| 1 | declarations inside `/- … -/` block comments | agent1, agent2 | r0020's five commented-out declarations counted, including both `@[simp]` ones attributed to `ScottHom.lean` |
| 2 | docstring prose lines beginning "theorem"/"lemma" at column 0 | agent3, agent5, agent6 | at least 8 lines, e.g. "lemma graded by ℕ …" |
| 3 | `protected theorem` missed | agent4 | `IdealCompletion` under-reports by 4 |

Net: **1308 is wrong in both directions**. agent5 puts the package at **1305**;
with defects 1 and 3 also applied the true figure is near **1297**, which is the
live-declaration total in §2. Fix the regex and restate
`docs/PropertiesVsTheorems.md` §2 before quoting the ratio again.

## 9. Corrections to the paper-property baseline

From agents reading the PDF rather than the docstrings: prose claim 8
(finiteness of the step-function join) is **not a claim the paper makes**; §4.1
states two claims the inventory omits; and "way below" occurs on **zero** pages —
the development's `≪` is machinery, appearing in a *statement* in only two
places, both `Domain.lean`. Net: prose claims 12 → 13, paper properties
**99 → 100**.

## 10. Recommended actions, in cost-to-value order

1. **Re-run agent5's two `simp`-firing scripts over the other five areas.**
   Mechanical, no judgement, and §3 says it is where the mass is.
2. **Fix the three counting defects**, re-measure, restate the ratio.
3. **Generalize `directedOn_fst_val`/`directedOn_snd_val`** — ~84 lines, and it
   converts two `U` rows to `S`.
4. **Merge the duplicate families**, not delete them: rows 2, 4, 6, 7 of §4 have
   live call sites on both sides. Rows 8 and 9 are straight deletions.
5. **Reduce `CombinatorRep` to its 3 live declarations** and
   `ContinuousConstruction` to 4 + 8, r0020's way: comment out in place with a
   note, rebuild, confirm nothing changed.
6. **Weaken the three over-strength signatures**; each is already discharged by
   an `example` re-running its own proof term.
7. **Fix two stale prose claims**: `PRepresentable.lean:39–43` still asserts
   "Lemma 28 is the `Fc` notion", in the file that *defines* `IsPRepresentable`;
   and §6 row 3.
8. **Prove Theorem 7's second sentence**, which unblocks eight theorems.

Nothing here changes a proof. Every agent confirmed the invariants: build 1224
jobs, 0 errors, `sorry` 1, no existing `.lean` file modified.
