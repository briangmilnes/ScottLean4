---
round: r0050
from: agent3
to: orchestrator
subject: jung-numbered-names
date: 2026-0810-14:40
started: 2026-0810-14:30
finished: 2026-0810-14:40
related:
  - plans/r0050-plan-from-orchestrator-to-orchestrator-numbered-name-standard.md
---

# r0050 phase 1, agent3 — the Jung partition renamed and aliased

## Counts

| # | Measure | Value |
| -- | ------- | ----: |
| 1 | Modules owned | 12 |
| 2 | Modules containing a numbered declaration | 11 |
| 3 | Defining declarations renamed | 32 |
| 4 | Plain `alias`es added | 32 |
| 5 | Declarations left alone as unattributed | 0 |
| 6 | Reference sites edited | 0 |
| 7 | Build errors | 0 |
| 8 | Build warnings | 0 |
| 9 | `sorry` | 0 |
| 10 | Lake jobs | 1372 |

Build log: `ScottDomains/logs/compile-20260810-143920.agent3.log` —
`exit 0 · wall 0:17.38 · jobs 1372 · lake errors 0 · sorry 0 · other warnings 0`.
The baseline before any edit
(`ScottDomains/logs/compile-20260810-143410.agent3.log`) was also 0/0/0, so the
rename introduced no diagnostic.

`ScottDomains/ScottDomains/JungCor136.lean` is the one owned module with nothing
to rename: it defines no declaration whose name carries a number. The result the
filename refers to — Jung's Corollary 1.36 — is present under the semantic name
`JungFinite.FixedPointOfCompactDeflationIsCompact` and as
`JungCor136.fixedPointOfCompactDeflationIsCompact`, neither of which encodes a
number.

## Method

The work list was produced by `scripts/a3-r50-decls2.sh`, which selects every
line in the twelve owned modules that introduces a declaration whose *name*
contains a digit. "Name contains a digit" is the recall-safe filter: the first
attempt filtered on the prefixes `thm|lem|prop|cor` and both over-matched
(`isCompactElement_apply` matched on the `lem` inside "Element") and
under-matched. The two filters agree on 32 declarations, and the scan finds no
indented or attribute-prefixed declaration the column-0 scan missed.

Every attribution below was read from the defining module before the rename was
made; the confirming line is quoted in the table. No attribution was inferred
from the three-digit encoding alone.

## Foreign-author results — rule 2

Eighteen declarations belong to A. Jung, *Cartesian Closed Categories of
Domains*, CWI Tract 66 (1989). None belongs to Gunter 1987, Spreen 2005, Iwamura
or Markowsky (see "Sources present but carrying no numbered name" below).

| # | Old name | New name | Paper | Printed number | Confirming docstring line |
| -- | -------- | -------- | ----- | -------------- | ------------------------- |
| 1 | `JungBicomplete.prop122` | `jung_proposition_1_22` | Jung 1989 | Proposition 1.22 | `JungBicomplete.lean:419` — "**Jung 1989, Proposition 1.22.**" |
| 2 | `JungFinite.lemma129` | `jung_lemma_1_29` | Jung 1989 | Lemma 1.29 | `JungFinite.lean:33` — "> **Lemma 1.29** A poset `D` with property m has property M if and only if the empty set and each pair of elements have a finite set of minimal upper bounds."; `JungFinite.lean:225` — "**Lemma 1.29 over `K(D)`.**" |
| 3 | `JungFinite.lemma22` | `jung_lemma_2_2` | Jung 1989 | Lemma 2.2 | `JungFinite.lean:634` — "**Jung 1989, Lemma 2.2 — step 4.**" |
| 4 | `JungNets.Thm137` (`Prop`-valued `def`) | `Theorem137` (rule 3) | Jung 1989 | Theorem 1.37 | `JungNets.lean:312` — "**Jung 1989, Theorem 1.37**, as a proposition about `D`." |
| 5 | `JungNets.Thm137Chains` (`Prop`-valued `def`) | `Theorem137Chains` (rule 3) | Jung 1989 | Theorem 1.37, chain form | `JungNets.lean:345` — "**The minimal remaining obligation**, weaker than `Thm137`: infima of nonempty *chains* rather than of all filtered sets." |
| 6 | `JungNets.Thm137.toChains` | `Theorem137.toChains` (rule 3) | Jung 1989 | Theorem 1.37 | namespace of #4 |
| 7 | `JungNets.forall_hasCompleteMub_of_thm137` | `forall_hasCompleteMub_of_jung_theorem_1_37` | Jung 1989 | Theorem 1.37 | `JungNets.lean:365` — "**The first conjunct of `isBifinite_iff_mubClosure`, reduced to Theorem 1.37.**" |
| 8 | `JungNets.lemma217_of_thm137` | `jung_lemma_2_17_of_jung_theorem_1_37` | Jung 1989 | Lemma 2.17, from Theorem 1.37 | `JungNets.lean:382` — "**`JungSFP.lemma217` with its property-m hypothesis discharged.**"; `JungSFP.lean:738` fixes `lemma217` as Lemma 2.17 |
| 9 | `JungNets.propertyM_pairs_of_thm137` | `propertyM_pairs_of_jung_theorem_1_37` | Jung 1989 | Theorem 1.37 | `JungNets.lean:398` — "**Property M at every pair of compact elements**, modulo `Thm137` …" |
| 10 | `JungSFP.lemma213` | `jung_lemma_2_13` | Jung 1989 | Lemma 2.13 | `JungSFP.lean:447` — "**Jung 1989, Lemma 2.13.**" |
| 11 | `JungSFP.thm214` | `jung_theorem_2_14` | Jung 1989 | Theorem 2.14 | `JungSFP.lean:673` — "**Jung 1989, Theorem 2.14 — the bifurcation.**" |
| 12 | `JungSFP.lemma217` | `jung_lemma_2_17` | Jung 1989 | Lemma 2.17 | `JungSFP.lean:738` — "**Jung 1989, Lemma 2.17.**" |
| 13 | `Iwamura.thm137_of_thm137Chains` | `jung_theorem_1_37_of_jung_theorem_1_37_chains` | Jung 1989 | Theorem 1.37 | `Iwamura.lean:610` — "**`Thm137Chains` now implies `Thm137`.**" |
| 14 | `Iwamura.thm137Chains_iff_thm137` | `jung_theorem_1_37_chains_iff_jung_theorem_1_37` | Jung 1989 | Theorem 1.37 | `Iwamura.lean:620` — "The two forms of Jung's Theorem 1.37 recorded in `JungNets` are equivalent." |
| 15 | `Iwamura.thm137Chains_of_wellOrderedInfima` | `jung_theorem_1_37_chains_of_wellOrderedInfima` | Jung 1989 | Theorem 1.37, chain form | `Iwamura.lean:627–630` — "**The obligation this round is left with, in its weakest form.** `JungNets.Thm137Chains D` — and hence, by `thm137Chains_iff_thm137`, `JungNets.Thm137 D` — follows from finding infima for monotone injective nets indexed by an ordinal alone." |
| 16 | `PropertyM.Thm137Omega` (`Prop`-valued `def`) | `Theorem137Omega` (rule 3) | Jung 1989 | Theorem 1.37, `ωᵒᵖ` form | `PropertyM.lean:745` — "**The remaining obligation, in its weakest named form.** `JungNets.Thm137` is `IsAlgebraic (ScottHom D D) → IsBicomplete D`; … this weakens it again to infima of decreasing sequences" |
| 17 | `PropertyM.Thm137Chains.toOmega` | `Theorem137Chains.toOmega` (rule 3) | Jung 1989 | Theorem 1.37 | namespace of #5 |
| 18 | `PropertyM.Thm137.toOmega` | `Theorem137.toOmega` (rule 3) | Jung 1989 | Theorem 1.37 | namespace of #4 |
| 19 | `PropertyM.lemma217_of_omega` | `jung_lemma_2_17_of_omega` | Jung 1989 | Lemma 2.17 | `PropertyM.lean:767` — "**`JungSFP.lemma217` with its property-m hypothesis discharged from `HasOmegaOpInfima` instead of from Jung's Theorem 1.37.**" |
| 20 | `R45.Agent5.thm137Omega` | `jung_theorem_1_37_omega` | Jung 1989 | Theorem 1.37, `ωᵒᵖ` form | `A5Thm137.lean:6` — "# Jung's Theorem 1.37 for algebraic dcpos, without Iwamura's lemma"; `A5Thm137.lean:174` — "**Claim 3 discharged** … `PropertyM.Thm137Omega D`" |
| 21 | `R45.Agent5.thm137Chains` | `jung_theorem_1_37_chains` | Jung 1989 | Theorem 1.37, chain form | `A5Thm137.lean:273` — "**Claim 2 discharged** for every `ω`-algebraic cpo." with claim 2 = `JungNets.Thm137Chains` at `A5Thm137.lean:14` |
| 22 | `R45.Agent5.thm137` | `jung_theorem_1_37` | Jung 1989 | Theorem 1.37 | `A5Thm137.lean:282` — "**Claim 1 discharged** for every `ω`-algebraic cpo" with claim 1 = `JungNets.Thm137` at `A5Thm137.lean:13` |

Rows 4, 5, 6, 16, 17 and 18 are `Prop`-valued claim `def`s and the theorems
living in their namespaces. Rule 3 governs them: they keep UpperCamelCase and
only the abbreviation `Thm` → `Theorem` changes. They therefore do **not** carry
the author qualification, even though they are Jung's — the two rules point in
different directions and rule 3 was given as the one that wins for this shape.
`docs/` and `CLAUDE.md` may want a sentence recording that.

## Gunter & Scott's own numbered results — plain form

| # | Old name | New name | Printed number | Confirming docstring line |
| -- | -------- | -------- | -------------- | ------------------------- |
| 23 | `JungFinite.thm18_of_propertyM` | `theorem_18_of_propertyM` | Theorem 18 | `JungFinite.lean:691` — "> **Theorem 18** If `D` and `D → D` are domains, then `D` is bifinite." |
| 24 | `PropertyM.thm18_of_cor136` | `theorem_18_of_jung_corollary_1_36` | Theorem 18 | `PropertyM.lean:1005` — "> **Theorem 18** If `D` and `D → D` are domains, then `D` is bifinite." |
| 25 | `Thm18.thm18_of_thm137Chains_and_cor136` | `theorem_18_of_jung_theorem_1_37_chains` | Theorem 18 | `Thm18.lean:8` — "Gunter & Scott, *Semantic Domains*, §6.2, printed page 33: > **Theorem 18** …" |
| 26 | `Thm18.thm18_of_thm137_and_cor136` | `theorem_18_of_jung_theorem_1_37_and_jung_corollary_1_36` | Theorem 18 | same |
| 27 | `Thm18.thm18_viaProjections_of_thm137_and_cor136` | `theorem_18_viaProjections_of_jung_theorem_1_37` | Theorem 18 | same |
| 28 | `SFP.thm14_forward` | `theorem_14_forward` | Theorem 14 | `SFP.lean:13` — "> **Theorem 14** The following are equivalent for any cpo `D`."; `SFP.lean:239` — "**Theorem 14, `1 → 2`.**" |
| 29 | `SFP.thm14_converse` | `theorem_14_converse` | Theorem 14 | `SFP.lean:472` — "**Theorem 14, `2 → 1`.**" |
| 30 | `R45.Agent5.thm18_of_cor136_via_thm137Chains` | `theorem_18_of_jung_corollary_1_36_via_chains` | Theorem 18 | `A5Thm137.lean:297` — "**Cross-check, not a new result.** `Thm18.thm18_of_thm137Chains_and_cor136` was written against `JungNets.Thm137Chains α` as an open hypothesis" |
| 31 | `FinitaryProjectionEmbedding.thm16_first_conjunct` | `theorem_16_first_conjunct` | Theorem 16 | `FinitaryProjectionEmbedding.lean:9` — "> **Theorem 16** If `D` is bifinite, then the poset `Fp(D)` of finitary …" |
| 32 | `RecursiveDomain.thm21` | `theorem_21` | Theorem 21 | `RecursiveDomain.lean:19` — "> **Theorem 21** If an operator `F` is representable over a cpo `U`, then there is …" |

## The 60-character rule (rule 4) applied three times

| # | Full derivation name | Length | Name used | Length |
| -- | ------------------- | -----: | --------- | -----: |
| 1 | `theorem_18_of_jung_theorem_1_37_chains_and_jung_corollary_1_36` | 62 | `theorem_18_of_jung_theorem_1_37_chains` | 38 |
| 2 | `theorem_18_viaProjections_of_jung_theorem_1_37_and_jung_corollary_1_36` | 70 | `theorem_18_viaProjections_of_jung_theorem_1_37` | 46 |
| 3 | `theorem_18_of_jung_corollary_1_36_via_jung_theorem_1_37_chains` | 62 | `theorem_18_of_jung_corollary_1_36_via_chains` | 44 |

Rows 1 and 2 drop the `_and_<second>` component exactly as rule 4 prescribes;
both docstrings already name Corollary 1.36 as the second hypothesis, so no
docstring text was added or changed. Row 3 has no `_and_` component — the second
component is joined by `_via_` — so the analogous reduction was applied to it:
`_via_jung_theorem_1_37_chains` shortened to `_via_chains`. This is the one place
the standard did not dictate the name; flag it if you want a different spelling.

`theorem_18_of_jung_theorem_1_37_and_jung_corollary_1_36` is 55 characters and
was kept whole.

## Sources present but carrying no numbered name — nothing to rename

Three foreign results named in the plan are in these modules but are not
numbered in their Lean names, so rule 2 has no work to do on them. Recorded here
so a later pass does not go looking for them.

| # | Result | Declaration | Source located at |
| -- | ----- | ----------- | ----------------- |
| 1 | Spreen 2005, Lemma 5.8 | `PropertyM.hasOmegaOpBoundsAbove_pair` | `PropertyM.lean:430` — "D. Spreen, *The largest Cartesian closed category of domains, considered constructively*, Math. Struct. in Comp. Sci. **15** (2005) 299–321, Lemma 5.8" |
| 2 | Iwamura's lemma (Jung's Theorem 1.2) | `Iwamura.exists_chain_directed_cover` | `Iwamura.lean:8` — "This file supplies **Jung 1989, Theorem 1.2** … which Jung attributes to Iwamura" |
| 3 | Markowsky's theorem | `Iwamura.hasDirectedSuprema_of_hasWellOrderedSuprema` | `Iwamura.lean:42` — "**Markowsky's theorem**" |

If the standard is meant to reach these too, they need `spreen05_lemma_5_8` and
`jung_theorem_1_2` — but that is a rename of a semantic name to a numbered one,
which is outside phase 1's remit, so nothing was touched.

## What was not done

* No reference site was edited anywhere in the package. Every one of the ~700
  sites still resolves through the 32 plain `alias`es. Phase 2 deletes them.
* No `@[deprecated]` attribute was used, so no site emits a warning.
* No statement, proof, binder or docstring claim changed. Three declarations were
  re-wrapped across lines because the longer name pushed the signature past 100
  columns (`JungNets.Theorem137.toChains`,
  `JungNets.forall_hasCompleteMub_of_jung_theorem_1_37`,
  `PropertyM.theorem_18_of_jung_corollary_1_36`); the tokens are unchanged.
* `scripts/a3-r50-decls2.sh` was added as the work-list generator and is the
  instrument phase 2 can re-run to confirm the set is closed.
  `scripts/a3-r50-cites.sh` re-locates every docstring line this report cites, so
  the line numbers above are read off the post-edit files rather than the
  pre-edit ones — inserting an `alias` shifts everything below it.
