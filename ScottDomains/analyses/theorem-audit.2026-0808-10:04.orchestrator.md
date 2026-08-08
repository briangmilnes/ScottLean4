# Theorem audit — consolidated, INTERIM (5 of 6 areas)

Round r0038. Tier 2 of the two-tier artifact split: the per-declaration tables
live in `reports/r0038-report-from-agentN-…`, this file merges them.

**Interim.** `Audit.SectionSeven` (agent5) is still running. That area holds
~419 of the ~1308 declarations — the whole §7 representability stack — and is
where duplication is most likely, because Lemma 28 has been attacked at two
notions by four agents across three rounds. **Every total below excludes it and
will move.** The rates, however, have been stable across five independent areas,
which is itself a result.

## 1. The question

1308 theorem-ish declarations against a paper of ~100 atomic properties, a ratio
of 13.2 : 1. Is the development carrying theorems that serve neither a paper
property nor a proof of one?

## 2. Answer so far

| # | Area | Live decls | `P` | `S` | `A` | `U` | `D` | `W` |
| -- | ---- | ----: | ----: | ----: | ----: | ----: | ----: | ----: |
| 1 | Foundations (agent1) | 118 | 9 | 65 | 26 | 12 | 6 | 0 |
| 2 | Projections (agent2) | 184 | 28 | 119 | 22 | 9 | 4 | 2 |
| 3 | Skeleton (agent3) | 170 | 32 | 114 | 17 | 1 | 6 | 0¹ |
| 4 | Powerdomains (agent4) | 201 | 11 | 121 | 42 | 20 | 5 | 2 |
| 5 | Bifinite (agent6) | 224 | 28 | 134 | 38 | 20 | 4 | 0 |
| — | **total** | **897** | **108** | **553** | **145** | **62** | **25** | **4** |

¹ agent3 reports 6 declarations carrying surplus hypotheses, read off the proof
terms rather than kernel-checked, since confirming means editing a live
declaration and this round forbids that. Counted here as a note, not as `W`.

**The `U` column over-reads and every agent said so unprompted.** Stripping the
theorems that are terminal by construction — nondegeneracy witnesses, refutation
witnesses, recorded dead ends — the r0020-comparable population is:

| # | Area | speculative `U` | rate |
| -- | ---- | ----: | ----: |
| 1 | Foundations | 12, but 5 are one blocked cluster (below) | 5.9% net |
| 2 | Projections | 5 | 2.7% |
| 3 | Skeleton | 1 | 0.6% |
| 4 | Powerdomains | 8 | 4.0% |
| 5 | Bifinite | 14 | 6.3% |
| — | **total** | **~35 of 897** | **≈3.9%** |

**r0020's rate on a body six times smaller was 3%.** So the honest answer to the
concern is: the 13.2 : 1 ratio is the cost of formalizing a paper that elides its
own foundations, not accumulated bloat. The development is at roughly the same
speculative-API rate it had at 199 theorems.

## 3. What the audit actually found

The finding is not `U`. It is **duplication across module boundaries** — 25
declarations in ~18 pairs, several spanning two agents' areas, and **none of them
visible to `lake build`, because nothing imports both sides.** That is the r0028
failure mode, which cost a round when it last surfaced.

| # | Pair or family | Areas | Note |
| -- | -------------- | ----- | ---- |
| 1 | `smashPair` and its two lemmas, in `Skeleton/Sum` and `Isomorphism/StrictCurry` | 3 | defined character-for-character identically; one pair shares a name, only the namespace separating them |
| 2 | one upper-bound lemma declared **four times in three modules** | 2, 3 | two at the general hypothesis, two at the `t ⊆ s` case. Found by the elaborator, not grep: an unqualified name resolved to the wrong one |
| 3 | Theorem 11's second conjunct routed three ways across the powerdomains | 4 | collapsing onto `IdealCompletion.thm11` retires four |
| 4 | `Lift`'s two lemmas re-instantiated at `WithBot γ` in `Smash` and `CoalescedSum` | 1, 3, 5 | a *merge* across 26 call sites, not a deletion |
| 5 | `eq_kleeneOperator_op` vs `theorem3` | 1 | discharged by **`Iff.rfl`** — the same proposition, not merely equivalent |
| 6 | `LemThirty` and `Dyadic` carry the same ideal-completion construction under **the same seven names** | 5, 6 | `embSet`, `isIdeal_embSet`, `embIdeal`, `mem_embIdeal`, `embIdeal_mono`, `scottContinuous_embIdeal`, `projSet`; `LemThirty`'s is more general |
| 7 | `Powerdomain/Universal.repOf` family = `UniversalDomain.repFun` family generalized | 4, 5 | 7 declarations; `repRangeOrderIso` is declared under that final name in **both** namespaces, so each masks the other's citation count |

Rows 6 and 7 are exactly what tier 2 exists for: neither agent could see both
halves. Row 7 also means `scripts/unused-theorems.sh` under-reports, as its own
header warns.

## 4. Findings that are not bloat

1. **A missing paper result, not dead code.** `ComputableFunction.lean` is
   imported by no module and `EffectivePresentation.lean` only by it — eight
   theorems with no external consumer — because the theorem that would consume
   them is **Theorem 7's second sentence** ("if `D` and `E` have effective
   presentations then `D → E` has one"), formalized nowhere. The response is to
   prove that sentence.
2. **`ContinuousConstruction`: keep, at one third the size.** Not removable —
   deleting it breaks `JungFinite.lemma22`. Exactly **one** of its 35 theorems is
   cited by the live Theorem 18 route. 4 live, 8 a recorded dead end worth
   keeping (p. 32: the proof "is carried out by analyzing each of the cases
   pictured in Figure 3"), 23 neither. Two of the 23 should be **relocated**
   rather than retired: they give `CompactFunction.lean`'s decomposition without
   `[BoundedComplete β]`.
3. **One line reduces Theorem 18** to `Thm137` + `FixedPointOfCompactDeflationIsCompact`:
   `JungNets.forall_hasCompleteMub_of_thm137` concludes exactly
   `JungFinite.thm18_of_propertyM`'s `hm` with two arguments transposed, and
   nothing composes them. (`scripts/check-thm18-composition.sh` already
   elaborates this; it should become a library theorem.)
4. **`W` traces to one false premise.** `Hoare.Powerdomain`'s *elaborated*
   signature does not take `[Domain D]`, contrary to what
   `instBoundedCompleteHoare`'s docstring gives as its reason for carrying it.
   Reading the source is not reading the signature — `variable` inclusion
   decides. `lem13_hoare` carries two unconsumed classes, `lem13_smyth` one.
   `instBoundedCompleteHoare` is behavioural: an unconsumed `[Domain α]`
   restricts when the instance resolves, and its sibling already omits it.

## 5. Where my own planning was wrong

Recorded because the plan is not evidence and this round proved it again.

| # | My claim | Measured |
| -- | -------- | -------- |
| 1 | `ContinuousAlgebra` is "the highest ratio in the development, the best place to find `U` and `W`" | zero `W`, 6.5% `U` — *below* its area average. Its 62-for-6 is a `FinSets` class stating Theorem 12 once instead of three times: 22 declarations rather than 66. The concentrations are `Smyth` (31%) and `Plotkin` (21%) |
| 2 | `Section62.apply_eq_self_of_mem_mubClosure` is consumed by `JungFinite` | **zero uses**. `JungFinite` declares its own `*_compacts` copies without the `hgA` hypothesis |
| 3 | the three Jung modules may duplicate each other | they duplicate **nothing**; what they missed was each other's *interface* — see §4.3 |

## 6. Defects in my own measurement scripts

Four agents found three independent defects. `counts.sh` and
`module-counts.sh` match `^(@\[…\] )?(theorem|lemma) ` and therefore count:

| # | Defect | Found by | Effect |
| -- | ------ | -------- | ------ |
| 1 | declarations inside `/- … -/` block comments | agent1, agent2 | r0020's five commented-out declarations counted, including both `@[simp]` ones attributed to `ScottHom.lean` |
| 2 | module-docstring prose lines beginning "theorem"/"lemma" | agent3, agent6 | ≥5 lines counted, e.g. "lemma graded by ℕ …" |
| 3 | `protected theorem` missed | agent4 | `IdealCompletion` under-reports by 4 |

Net: **1308 is wrong in both directions and is an over-count by at least 10.**
Fix the regex, re-run, and restate `docs/PropertiesVsTheorems.md` §2 before
quoting the ratio again.

## 7. Corrections to the paper-property baseline

From agents reading the PDF rather than the docstrings:

* prose claim 8 (finiteness of the step-function join) is **not a claim the paper
  makes**;
* §4.1 states two claims the inventory omits (`fst(L)`/`snd(L)` directedness);
* "way below" occurs on **zero** pages — the development's `≪` is machinery, and
  it appears in a *statement* in only two places, both in `Domain.lean`.

Net: prose claims 12 → 13, paper properties **99 → 100**, ratio unchanged at
about 13 : 1 pending the theorem-count fix.

## 8. Next

1. Wait for `Audit.SectionSeven`; re-total.
2. Fix the three counting defects and re-measure.
3. Merge the six branches, run the composition check, confirm `sorry` is 1 and
   the build unchanged.
4. Act on the list the way r0020 did — comment out in place with a note, rebuild,
   confirm nothing changed. **Duplicates are merges, not deletions**: rows 2, 4,
   6 and 7 of §3 have live call sites on both sides.
