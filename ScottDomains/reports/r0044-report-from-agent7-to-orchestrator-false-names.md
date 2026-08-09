---
round: r0044
from: agent7
to: orchestrator
subject: false-names
date: 2026-0808-17:45
started: 2026-0808-17:06
finished: 2026-0808-17:45
related:
  - plans/r0044-plan-from-orchestrator-to-orchestrator-specification-defects.md
  - scripts/a7-sweep.sh
  - scripts/r0043-verify-citations.sh
---

# r0044 class 4, mechanical half — cited declaration names that do not exist

## Headline

**218 defect sites, 126 distinct names, across 258 files.** 48 of the 218 sites
are in `.lean` files — **40 in docstrings**, the severe class, because a
docstring is read as documentation of live code — and 170 are in `docs/`,
`analyses/`, `plans/` and `reports/`.

The 218 split into three kinds, which have different fixes and very different
precision, so they are never added into one number:

| # | Kind | Sites | `.lean` | prose | Audited precision |
| -- | ---- | ----: | ------: | ----: | ----------------: |
| 1 | **wrong-module-qualifier** — the name exists; it is cited under its *module path* instead of its namespace | 113 | 30 | 83 | **41 of 41 = 100%** |
| 2 | **nonexistent** — no declaration has that name, anywhere, in our package or Mathlib | 93 | 15 | 78 | 15 of 27 = 56% |
| 3 | **wrong-qualifier** — last component is real, qualifier matches neither namespace nor module | 12 | 3 | 9 | 1 of 5 = 20% |

A fourth category, **absence-claim (85 sites)**, is reported separately and is
**not** counted as a defect: the name is cited *to say it is absent* — a zero-hit
grep, a retired declaration, a list of name variants searched for. Unresolved is
the correct outcome there, exactly as r0043 documented.

**Measured precision: 44 of 48 on `.lean` sites (91.7%, exhaustive — every one
checked by hand), 13 of 25 on a fixed-stride sample of prose sites (52.0%).
Weighting the prose rate over its 170 sites gives an estimated 132 of 218
overall, 60.7%.** Kind 1 alone — 113 of the 218 — was 100% precise on all 41
audited sites, and it is mechanically certain rather than heuristic.

## The instrument

`scripts/a7-sweep.sh` reproduces everything below. It runs
`a7-dump-env.sh` → `a7-cite-scan.py` → `a7-resolve.py`, and
`a7-audit.sh` builds the audit views.

### What was wrong with generalizing the existing script as written

The plan said to generalize `scripts/r0043-verify-citations.sh`. **That script
has a defect that makes a direct generalization useless**, which agent2 found
independently and the orchestrator relayed mid-round; I had hit the same wall
from the other side. It matches a cited name by its **last component only**
(`tail="${name##*.}"`, then `grep -qxF "$tail"` against an unqualified list), so
every wrong-namespace citation passes. That is a false *negative*, and it is the
single largest real category here — 113 of my 218 sites, none of which the r0043
checker could see.

The root cause is worth stating once, because it will recur: **a module path is
not a namespace.** `ScottDomains/ScottDomains/Smash.lean` declares into namespace
`ScottDomains`, not `ScottDomains.Smash`. Anyone writing a citation from the file
path gets it wrong, and it looks right.

### Name universe: the elaborated environment, not a source lexer

`lean-decls.py --list` cannot serve as the universe. It emits **unqualified**
names, and it matches only `theorem`/`lemma` openers — no `def`, `structure`,
`instance`, no structure/class **projections**, no inductive **constructors**, no
Mathlib. Three of the four false-positive sources named in my brief follow
directly from those gaps.

So the universe is dumped from the **elaborated environment**: `a7-dump-env.sh`
generates a Lean file importing all 100 modules plus `Mathlib`, and writes every
constant as `module<TAB>fully-qualified-name`. **770,249 constants**, of which
**3,691 are ours**. This removes three false-positive classes by construction
rather than by hand-waving:

* `IsSemilattice.op_comm`, `op_idem`, `Combinator.LambdaModel.app_lam` — class and
  structure **projections are genuine constants** and resolve. Verified present.
* `Function.cantor_surjective` and every other Mathlib name resolves.
* `def`s, instances, structures and constructors resolve.

Matching is on **component boundaries**, never substring or prefix. That
distinction is the whole instrument: `smyth_oneBot_eq_bot` is a proper prefix of
the real `smyth_oneBot_eq_bot_eq_unit_bot`, and a prefix test would call the
known-false citation resolved.

**Two defects found in the tree while building this**, both reported as findings:

1. **`import ScottDomains` does not give the library.** The root module
   `ScottDomains.lean` re-exports the Mathlib foundations and imports **none** of
   the 100 submodules; the lakefile builds them through the `ScottDomains.+`
   glob. A dump importing only the root saw 235,431 constants and **zero of
   ours**. The dump file must list all 100 imports, so it is generated
   (`a7-gen-dump.py`).
2. **`ScottDomains.ExistingTheories` declares no constants**, so it never appears
   in the environment's module column and citations of it read as nonexistent
   names. The module list is therefore taken from the tree as well.

### Extraction

Only `.lean` **comment** text is scanned — code is blanked first by the lexer
`lean-decls.py` uses, run inverted, so a declaration's own name is never mistaken
for a citation of it. A citation is **a whole backtick span that is exactly a
Lean identifier**; `` `#check @d` `` and `` `u ⊢♮ v` `` are not citations. Taking
sub-tokens out of prose inside backticks is what makes such a sweep unusable and
is deliberately not done.

### Filters, and why each exists

Of 20,730 backticked citations, 10,612 are removed by a **shape filter** before
any lookup, because an identifier-shaped span is usually not a declaration
citation at all. Every rule was written against observed output:

| # | Rule | Drops |
| -- | ---- | ----- |
| 1 | must contain a lowercase letter | `N`, `D`, `T`, `PATH` |
| 2 | dotted ⇒ first component uppercase and longer than one char | `q.val`, `G.val`, `v4.32.2` |
| 3 | underscored ⇒ ≥ 2 components of length ≥ 2 | `S_f`, `p_N`, `fix_D`, `_bot` |
| 4 | bare word ⇒ uppercase-initial, length ≥ 4 | `grep`, `pdftotext`, `hmono`, `smash` |
| 5 | leading `_`, trailing `.`, numeric last component | `_of_ne`, `Combinator.`, `IsLUB.2` |

A 40-entry stoplist (`scripts/a7-stoplist.txt`) removes 92 further sites; every
entry was observed in output and classified by reading its site, none guessed —
`ToUnicode` (a PDF font-dictionary key), `Spreen` (an author surname and a
`section` name), `Iinf`/`Ihat` (locals bound by `set` inside a proof).

The **absence-claim** test reads a three-line window around the citation for
phrases such as "there is no", "has no", "no \`", "zero hits", "were retired",
"searched for". A one-line window was measured to miss cases where the sentence
wraps ("… and were retired" landed on the following line). Six cues were
**removed** after measurement because each suppressed a real defect — `never`,
`no such`, `missing`, `absent`, `grep`, `retired` — restoring 3 of 17 suppressed
`.lean` sites.

## Ranked findings

### Rank 1 — nonexistent names in live `.lean` docstrings (13 confirmed)

Each was checked against the environment and its site read. These are the
highest-severity hits: a docstring naming a declaration that does not exist.

| # | File:line | Cited name | What it probably meant |
| -- | --------- | ---------- | ---------------------- |
| 1 | `FlatPowerdomain.lean:34` | `smyth_oneBot_eq_bot` | `smyth_oneBot_eq_bot_eq_unit_bot` |
| 2 | `FlatPowerdomain.lean:34` | `smyth_bot_eq_bot` | same declaration; the row states two names for one result |
| 3 | `Dyadic.lean:45` | `Dyadic.instPartialOrderU₀` | `Dyadic.U₀.instPartialOrder` |
| 4 | `Dyadic.lean:46` | `Dyadic.instOrderBotU₀` | `Dyadic.U₀.instOrderBot` |
| 5 | `Dyadic.lean:47` | `Dyadic.instCountableU₀` | `Dyadic.U₀.instCountable` |
| 6 | `Colimit.lean:59` | `etaChain_not_wellDefined` | nothing — no `etaChain` anything exists in the whole environment, yet the docstring says it "exhibits the failure … with `u = ∅`" |
| 7 | `Combinator.lean:47` | `exists_thm26_of_thm25` | `exists_lambdaModel_of_thm25` (line 625) |
| 8 | `Kleene/Graph.lean:32` | `sSup_recover` | `sSup_recoverAt` (line 94) |
| 9 | `PRep.lean:105` | `isProjection_sSup_of_directed` | `isProjection_sSup` |
| 10 | `PRepFun.lean:662` | `SmashObstruction` | nothing — "`SmashObstruction` below" has no referent in the file or the environment |
| 11 | `Flat.lean:53` | `Flat.Truth.forall_eq` | `truth_forall_eq` (line 348) |
| 12 | `FixedPoint.lean:23` | `OmegaCompletePartialOrder.ωSup_iterate_mem_fixedPoint` | `OmegaCompletePartialOrder.fixedPoints.ωSup_iterate_mem_fixedPoint` — the `fixedPoints` component is missing |
| 13 | `ContinuousConstruction.lean:505` | `Function.iterate` | `Nat.iterate` — Mathlib has no `Function.iterate` |

Rows 3–5 are one table in one module docstring listing three instances **by
name, none of which exists**. Rows 1–2 are the brief's known true positive, and
the instrument catches both.

Two `.lean` `nonexistent` rows are **false positives** and are not in the table:
`FpLattice` at `SFP.lean:35` and `:45` names a `section FpLattice` in
`FinitaryProjectionPoset.lean`, and a section name is not a constant.

### Rank 2 — wrong-module-qualifier in `.lean` files (30 sites, all confirmed)

The declaration exists; the name **as written elaborates to nothing** because the
qualifier is the module path. `#check Smash.directedOn_val_smashBase` fails;
`#check ScottDomains.directedOn_val_smashBase` succeeds. Distinct names:

| # | Cited name | Real name |
| -- | ---------- | --------- |
| 1 | `Smash.directedOn_val_smashBase` (×2) | `ScottDomains.directedOn_val_smashBase` |
| 2 | `UniformFixedPoint.directedOn_val_image_subtype` (×2) | `ScottDomains.directedOn_val_image_subtype` |
| 3 | `MinimalUpperBounds.isBifinite_iff_mubClosure` (×3) | `ScottDomains.isBifinite_iff_mubClosure` |
| 4 | `MinimalUpperBounds.isNormalIn_of_isMubClosed` (×2) | `ScottDomains.isNormalIn_of_isMubClosed` |
| 5 | `MinimalUpperBounds.hasCompleteMub_of_isNormalIn` | `ScottDomains.hasCompleteMub_of_isNormalIn` |
| 6 | `UniformFixedPoint.eq_kleeneOperator_op` | `ScottDomains.eq_kleeneOperator_op` |
| 7 | `UniformFixedPoint.theorem3` | `ScottDomains.theorem3` |
| 8 | `Lift.coe_mem_of_mem_liftBase`, `Lift.directedOn_liftBase` | `ScottDomains.coe_mem_of_mem_liftBase`, `…directedOn_liftBase` |
| 9 | `Smash.coe_mem_of_mem_smashBase`, `Smash.directedOn_smashBase` | `ScottDomains.…` |
| 10 | `CoalescedSum.coe_mem_of_mem_sumBase`, `.directedOn_sumBase`, `.sumSup` | `ScottDomains.…` |
| 11 | `NormalProjection.normalHom` | `ScottDomains.normalHom` |
| 12 | `Currying.scottContinuous_pairLeft` | `ScottDomains.scottContinuous_pairLeft` |
| 13 | `FinitaryProjectionPoset.mem_Fc_iff` | `ScottDomains.mem_Fc_iff` |
| 14 | `FinitaryProjectionPoset.Fc.completePartialOrder` | `ScottDomains.Fc.completePartialOrder` |
| 15 | `ComputableFunction.RecursiveLE` | `ScottDomains.Computable.RecursiveLE` |
| 16 | `FunctionSpaceCountable.countable_compacts_scottHom` | `ScottDomains.ScottHom.countable_compacts_scottHom` |
| 17 | `PowerdomainCompacts.finitaryProjection_not_maps_compacts` | `ScottDomains.PowerdomainMap.Compacts.…` |
| 18 | `ScottDomains.PowerdomainMapRep.lemma28AtU_of''` | `ScottDomains.PowerdomainMap.Rep.lemma28AtU_of''` |
| 19 | `CombinatorRep.arrowFamily` | `ScottDomains.Combinator.arrowFamily` |
| 20 | `Plotkin.not_single_le_pair` | `ScottDomains.Plotkin.FinCompacts.not_single_le_pair` |
| 21 | `ScottDomains.comp` | `ScottDomains.Combinator.comp` |

`Audit/Foundations.lean` carries 11 of the 30 — it is an audit module whose whole
purpose is to cite other modules' declarations, and it qualifies every one by
module.

### Rank 3 — prose sites (170)

83 wrong-module-qualifier, 78 nonexistent, 9 wrong-qualifier. Confirmed in the
sample and worth fixing:

* `Set.instCompleteLattice` (×2, `r0040-…-s2-s3.md`) — **Mathlib has no such
  instance**; the report cites it as the thing the development consumes.
* `Atomless.instCountableBC` (`r0038-…-section-seven.md:569`) — truncated; the
  real names are `instCountableBCU₀` and `instCountableBCCompacts`.
* `sSup_compactsBelow` (`r0004-…-algebraic-domain.md:65`) — a delivery table row
  naming a declaration that does not exist; the real one is
  `IsAlgebraic.isLUB_compactsBelow`.
* `ClosureProperties.lem17_fun` and `Skeleton.Recovered.thm14` /
  `Skeleton.Recovered.IsBifiniteViaProjections` — the three instances agent2
  reported. All three are caught, and the instrument resolves the real names
  automatically (`ScottDomains.lem17_fun`, `ScottDomains.Recovered.…`).

`reports/r0038-report-from-agent1-to-orchestrator-audit-foundations.md` holds 36
sites on its own, almost all wrong-module-qualifier — the same systematic error
as its subject module.

## Precision, measured

| # | Population | Sites | Audited | True | Precision |
| -- | ---------- | ----: | ------: | ---: | --------: |
| 1 | `.lean` (docstrings + comments) | 48 | **48 (all)** | 44 | **91.7%** |
| 2 | prose, fixed-stride sample | 170 | 25 | 13 | **52.0%** |
| 3 | all defect sites | 218 | 73 | 57 | **60.7% estimated** |
| 4 | kind 1 only (wrong-module-qualifier) | 113 | 41 | 41 | **100%** |

The four `.lean` false positives: `FpLattice` ×2 (a `section` name) and `MPair.le`
×2 (informal reference to the order on `MPair`; `MPair.le_iff` and
`MPair.PaperLE` exist, `MPair.le` does not, so the instrument's literal claim is
true but the site is not worth fixing).

Prose false positives are dominated by names quoted **as data** rather than
asserted: proposed names in plans (`lem13_plotkin` "if the paper's `D]` and `D[`
cover it"), naming prescriptions (`ScottDomain` "would render that compound as
…"), capitalization discussions (`RePred` versus `REPred`), and section names
(`FpLattice`). These are why kind 2 in prose is only 16.7% precise while kind 2
in `.lean` is 86.7%.

## Recall limits, stated

* **The shape filter discards 9,577 citations that would have resolved.** Those
  are overwhelmingly single letters and short variables that resolve by accident
  against 770k names; but the filter is the reason the output is 218 rows rather
  than 2,961, and any declaration whose name is a bare lowercase word or a
  one-letter-suffixed form is invisible to this sweep.
* **Fenced code blocks are not scanned.** In `plans/` they hold *proposed*
  statements naming declarations that intentionally do not exist yet; scanning
  them would report intent as defect.
* **Only backticked spans count.** A name written in prose without backticks is
  not seen.
* **The absence-claim test is a text heuristic.** It removes 85 sites. Three
  `.lean` sites were measured being wrongly suppressed and the responsible cues
  were removed; the remaining error rate on that class is not separately
  measured, and it can still hide a defect whose sentence happens to contain a
  negation.

## Corrections

1. **To the plan.** The plan says to generalize `r0043-verify-citations.sh`. Its
   matching rule is defective (last-component only) and a faithful generalization
   would have reproduced the false negative across the whole tree. The mechanism
   had to be replaced, not extended.
2. **To r0043's reported result.** "No cited name fails to exist" was checked
   with that matcher and is weaker than stated; the r0043 reports are in this
   corpus and contribute defect sites of their own.
3. **Cross-reference for agent8 (the reading half).** `PowerdomainMap.lean:19`
   says nine name variants "returned zero hits", listing `powerdomainMap` and
   `Powerdomain.map` among them. `ScottDomains.PowerdomainMap.map` now exists —
   in that very module. The docstring's claim is stale. My sweep classifies the
   site as an absence-claim and therefore does **not** count it; it is a false
   *claim*, which is agent8's category, not mine.

## What this instrument reads from the environment, and what it does not

Stated explicitly because a reader cannot tell from the outside, and because
agent6 found an environment-API defect that would corrupt a different design.

This sweep reads **only `Name` and declaring module**, by iterating
`env.constants` and calling `env.getModuleFor?`. It **never** touches
`ConstantInfo.value?`, never inspects a declaration's type or proof term, and
never walks references inside a proof. So **agent6's `allowOpaque := true`
defect does not apply here**: the flag governs `value?` on theorems, and nothing
in `a7-gen-dump.py` calls it. Had the instrument counted references rather than
matched names, it would have been affected.

Three counts of "how many declarations" are in play this round and **none should
be reconciled with another** — they measure different sets:

| # | Number | What it counts |
| -- | -----: | -------------- |
| 1 | 1773 | `counts.sh` — `theorem`/`lemma` openers in source |
| 2 | 1869 | agent6 — theorems in the environment; the extra 96 are `Prop`-valued class instances, which are theorems in the environment but not `theorem` openers in source |
| 3 | **3691** | **this report** — *every* constant declared in a `ScottDomains.*` module: theorems, `def`s, structures, classes, instances, projections, constructors and equation lemmas |

Figure 3 is the one the sweep needs, because a docstring may cite any of those
and all of them must resolve. It is not a theorem count and is not comparable to
1773 or 1869.

## Verification

No `.lean` file was edited.

* `scripts/counts.sh` — modules 100, lines 37300, theorems 1773, sorry 0.
* `scripts/compile.sh -r r0044` — 1339 jobs, 0 lean diagnostics, 0 lake errors,
  0 sorry, 0 other warnings; log
  `ScottDomains/logs/compile-20260808-173905.agent7.log`.

## Scripts

| # | Script | Does |
| -- | ------ | ---- |
| 1 | `scripts/a7-sweep.sh` | runs the whole sweep; the one command that reproduces the numbers |
| 2 | `scripts/a7-dump-env.sh` | dumps 770,249 environment constants as `module<TAB>name` |
| 3 | `scripts/a7-gen-dump.py` | generates the 100-import Lean dump file and the module list |
| 4 | `scripts/a7-cite-scan.py` | extracts backticked citations from Lean comments and prose |
| 5 | `scripts/a7-resolve.py` | shape filter, five resolution tiers, three defect categories |
| 6 | `scripts/a7-stoplist.txt` | 40 observed non-citations, each justified at its site |
| 7 | `scripts/a7-triage.sh` | collapses sites to distinct names for hand review |
| 8 | `scripts/a7-audit.sh` | builds the precision-audit views and samples |
| 9 | `scripts/a7-report-data.sh` | regenerates every table quoted above |
