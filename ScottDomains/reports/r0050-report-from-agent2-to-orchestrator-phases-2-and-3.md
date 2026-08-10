---
round: r0050
from: agent2
to: orchestrator
subject: phases-2-and-3
date: 2026-0810-16:38
started: 2026-0810-16:12
finished: 2026-0810-16:38
related:
  - plans/r0050-plan-from-orchestrator-to-orchestrator-numbered-name-standard.md
  - reports/r0050-report-from-agent1-to-orchestrator-numbered-name-standard-phase1.md
  - reports/r0050-report-from-agent3-to-orchestrator-jung-numbered-names.md
  - reports/r0050-report-from-agent4-to-orchestrator-numbered-name-standard-phase1.md
---

# r0050 phases 2 and 3 — the scaffolding is gone and the module names follow

## Outcome

All 140 phase-1 `alias` statements are deleted, **912** reference sites and
citations are repointed, three modules and one namespace are renamed, and the
package builds at **1372 jobs, 0 errors, 0 warnings beyond the 3 `sorry`
warnings**. The `sorryAx` cone is still exactly the three constants r0052
introduced. 27 `lake build` runs, 15 of which named stale sites that were then
fixed.

| # | Measurement | Before phase 2 | After phase 3 |
| -- | ---------- | -------------: | ------------: |
| 1 | `alias` statements added by r0050 | 140 | 0 |
| 2 | lake jobs | 1372 | 1372 |
| 3 | Lean diagnostics (errors) | 0 | 0 |
| 4 | warnings other than `sorry` | 0 | 0 |
| 5 | `sorry` declarations | 3 | 3 |
| 6 | constants in the `sorryAx` cone | 3 | 3 |
| 7 | surviving token occurrences of a retired name | 912 | 0 |

Two commits: `ac51422` (phase 2) and the phase-3 commit below. Not pushed.

## Phase 2 — deleting the aliases

### Reference sites repointed, by how the compiler exposed them

The 140 aliases split into two populations that behave completely differently
when the alias is deleted, and the split is the main technical finding of this
round.

| # | Population | Aliases | Sites | How a stale site is found |
| -- | --------- | ------: | ----: | ------------------------- |
| 1 | theorem aliases | 131 | 149 | `Unknown identifier` at a reported line and column |
| 2 | `Prop`-valued claim `def` aliases | 9 | 289 | not reported at all — see below |
| 3 | citations in docstrings and comments | — | 474 | not reported at all — prose |
| | **total** | **140** | **912** | |

The three populations are disjoint: the census that produced the 474 was taken
after populations 1 and 2 were already repointed and the build was clean.

**Population 1** is the compiler-driven case the plan describes, and it worked
exactly as designed. Deleting all 140 aliases at once and rebuilding exposes the
stale sites one layer of the import DAG at a time, because a module that fails to
build hides the sites in every module importing it. It took **15 build/fix
cycles** to reach a fixed point. Each cycle is cheap — a partial rebuild is 4–8 s
and a full one is 30 s — so the whole population cost about four minutes of
machine time. `scripts/a2-r50-fixsites.py` reads the compile log, and for each
`error: <file>:<line>:<col>: Unknown identifier \`<name>\`` it replaces the
identifier **at that codepoint offset**, refusing to act if the text at the
offset is not the identifier reported. Nothing is searched for; the elaborator
supplies both the position and the name.

Three properties of Lean 4.32's diagnostics had to be handled and are worth
recording, because any future rename hits them:

1. The message is `` Unknown identifier `x` `` — capital U, backtick-delimited.
   A Lean identifier may itself end in `'`, so the closing delimiter must be
   scanned as a backtick: `Lemma28AtU.lemma28AtU_of'` was reported that way.
2. The name reported is the **fully qualified** name Lean tried to resolve, not
   what the author wrote. `IdealCompletion.thm11` in the source is reported as
   `ScottDomains.IdealCompletion.thm11`. The fixer takes the longest dotted
   suffix that occurs literally at the reported offset.
3. The renamed declaration can sit **inside** a dotted name with components on
   both sides: `Recovered.thm14.mpr` is a projection applied to a renamed
   theorem. The substitution replaces the longest contiguous span the alias map
   knows and leaves the rest.

**Population 2 is the finding.** The nine aliases whose target is a
`Prop`-valued `def` — `Thm137`, `Thm137Chains`, `Thm137Omega`, `Thm29Normal`,
`Thm29Second`, `Thm29SecondAtDomains`, `Thm29NormalWithoutDomain`,
`Thm26Printed`, `Lem30Arrow` — appear almost exclusively in **type** positions,
and Lean's `autoImplicit` option turns an unknown identifier in a type position
into an implicitly bound variable rather than reporting it. Deleting those
aliases therefore produces **no `Unknown identifier` at the reference site at
all**. What Lean reports instead is a downstream symptom several lines away:

    error: LemThirty.lean:299:0: type of theorem
      `…theorem_29_secondAtDomains_of_thm29Second` is not a proposition
      {Thm29SecondAtDomains : Sort u_1} → Theorem29Second → Thm29SecondAtDomains

    error: Audit/Bifinite.lean:54:43: Function expected at
      Thm137
    Hint: The identifier `Thm137` is unknown, and Lean's `autoImplicit` option
    causes an unknown identifier to be treated as an implicitly bound variable…

Neither message carries the offset of the stale identifier, so the
position-driven fixer cannot see these sites. They were repointed by
`scripts/a2-r50-retired-defs.py` on a different but equally sound argument:
after phase 1 renamed the nine `def`s and phase 2 deleted their aliases, **no
declaration by the old name exists** in the package or in Mathlib, so every
identifier-boundary-anchored token occurrence is a reference to something that
is gone and there is nothing else it could denote. The build then confirms it.

**This is a hazard for r0051.** Any future rename of a `Prop`-valued `def` in
this package is invisible to the compiler-driven method while `autoImplicit` is
on. The cheap countermeasure is `set_option autoImplicit false` for the duration
of such a rename; the alternative is the token argument used here, which is only
valid once the old name provably denotes nothing.

### Sites fixed, by cluster

Population 2 is the whole of the nine `def` names and accounts for 289 of the
912 on its own:

| # | Identifier | Sites | New name |
| -- | --------- | ----: | -------- |
| 1 | `Thm29Normal` | 89 | `Theorem29Normal` |
| 2 | `Thm29SecondAtDomains` | 71 | `Theorem29SecondAtDomains` |
| 3 | `Thm29Second` | 44 | `Theorem29Second` |
| 4 | `Thm137` | 41 | `Theorem137` |
| 5 | `Thm137Chains` | 20 | `Theorem137Chains` |
| 6 | `Lem30Arrow` | 13 | `Lemma30Arrow` |
| 7 | `Thm137Omega` | 6 | `Theorem137Omega` |
| 8 | `Thm29NormalWithoutDomain` | 3 | `Theorem29NormalWithoutDomain` |
| 9 | `Thm26Printed` | 2 | `Theorem26Printed` |

The largest clusters in population 3 (docstring and comment citations):
`lemma217` 33, `lem17_fun` 18, `thm27` 16, `lem10_smash` 11,
`thm29SecondAtDomains_of_thm29Normal` 10, `thm18` 10, `theorem3` 10.
Population 1's sites are spread thin — the biggest single identifier is
`Colimit.Thm29Second` at 7 and `theorem1` at 7 — which is what you expect once
the two large `def` clusters are removed from it.

The full per-site record is in `analyses/a2-r50-leftovers.txt` (the census
taken before the prose pass) and `analyses/a2-r50-prose.txt`. The plan's
estimates were close: it predicted 92/74/43/32/27/21/19/16 for the largest
clusters; measured, `Thm29Normal` is 89 and `Thm29SecondAtDomains` is 71, the
difference being the alias statements themselves plus the sites phase-1 agents
had already moved inside their own files.

### `simp only` and `unfold` over the alias names — measured, zero

The plan asked for this because an `alias` over a `def` elaborates to a `def`
indirection, so `simp only [OldName]` or `unfold OldName` at a reference site
would unfold one step further than a direct reference and could change a proof.
Searched over all nine `def` alias names for `unfold`, `simp only [`, `simp [`,
`dsimp only [`, `rw [` and `delta`: **zero occurrences**. Phase 1 measured zero
over its four; the same holds over all nine. No proof could have changed shape,
and none did — no proof body was edited in this round.

### Docstring and comment citations — 474, and why they were repointed

After the build was clean, 474 token occurrences of retired names survived in
docstrings and comments (`analyses/a2-r50-leftovers.txt`). Each names a
declaration that no longer exists, so each is a dangling citation of exactly the
same kind as a code reference — the elaborator simply cannot see it. They were
repointed by `scripts/a2-r50-prose.py`, which refuses to run unless two guards
hold, and both did:

1. **No retired name maps to two different new names.** Five short names are
   defined in two modules each (`lem17_fun`, `lem17_strictFun`, `thm27`, …);
   substituting is only sound because both copies were renamed identically.
2. **No retired name is still a live declaration.** Checked against every
   `theorem`/`lemma`/`def`/`abbrev`/`instance`/`structure`/`inductive` binding
   in the package — a third module defining the same short name and never
   renamed would have pointed prose at the wrong result.

This substitutes a name for a name. No sentence, statement, proof, binder or
claim was altered.

### The two `#print axioms` comment blocks

Refreshed by hand, as asked.

- `ContinuousAlgebra.lean`: 4 rows (`thm12`, `thm12_hoare`, `thm12_smyth`,
  `thm12_plotkin`), column alignment preserved against the block's longest name.
- `Universality.lean`: 5 rows (`thm21_image`, `lem24`, `thm25`,
  `thm25_powerset`, `thm25_isUniversal`) plus 4 names in the prose paragraph
  that follows (`ScottDomains.lem23`, `lem24`, `thm25`, `thm22`); that paragraph
  was rewrapped because the longer names pushed one line past the margin.

### One cost worth recording

The standard's names are longer than the abbreviations they replace, so lines
grow. Measured over the phase-2 diff: **37 lines added past column 100 and 15
removed, a net +22**. No line-length linter is enabled in this package (the
build reports 0 warnings), so nothing is broken; it is a real and permanent cost
of the standard and it is stated here rather than discovered later.

## Phase 3 — module and section names

One module at a time, `git mv` then rebuild to zero before the next.

| # | From | To | Files touched | Occurrences |
| -- | --- | -- | ------------: | ----------: |
| 1 | `Thm18.lean` | `Theorem18.lean` | 6 | 15 |
| 2 | `JungCor136.lean` | `JungCorollary136.lean` | 3 | 7 |
| 3 | `LemThirty.lean` | `Lemma30.lean` | 14 | 157 |

Row 1 carried a namespace too — `namespace ScottDomains.Thm18` — which the plan
listed only for `LemThirty`; it was renamed to `ScottDomains.Theorem18`. Only
**one** `import` line existed for `Thm18` (`A5Thm137.lean`) and **one** for
`JungCor136`; the rest of each count is qualified references and citations.
`LemThirty` had no `import` line at all under that name — every one of its 157
occurrences was a qualified reference or a citation, which is exactly why the
plan put it last.

The package root `ScottDomains.lean` needed **no** change: it imports Mathlib
foundations only, and the package's own modules are found by the lakefile's
glob, not by a list.

### The `LemThirty` → `Lemma30` namespace rename collides with a declaration

`ScottDomains.LemThirty` contained `def Lemma30`, the ten-fold conjunction. After
the namespace rename that declaration's full name is
`ScottDomains.Lemma30.Lemma30`, and Lean's `linter.dupNamespace` fires on it —
one warning, which the round's acceptance criteria do not allow.

Removing the duplication means renaming one of the two, and both names were
fixed by instructions above my authority: the namespace is `Lemma30` because the
plan says so, and the `def` is `Lemma30` because that is what the naming
standard prescribes for a `Prop`-valued claim of Lemma 30. **This is a decision
for you.** I took the option that changes no name: `set_option
linter.dupNamespace false in` on that one declaration, with a comment at the site
saying why and that the choice is open. The three alternatives are (1) leave it
as is, (2) rename the `def` (`Lemma30.Statement`, or keep `Lemma30AtV` as the
only public form), (3) name the namespace something other than the module.

### Section names

The plan named three sections. Measured, the situation had moved:

| # | Section | File | Action |
| -- | ------ | ---- | ------ |
| 1 | `Thm27` | `Atomless.lean` | renamed to `Theorem27` |
| 2 | `Thm27` | `Dyadic.lean` | renamed to `Theorem27` |
| 3 | `Thm26` | `Combinator.lean` | **already `Theorem26`** — my own phase-1 commit `9c0718b` did it; the plan's line number was read before that commit |
| 4 | `Thm18` | `PropertyM.lean` | renamed to `Theorem18`, not in the plan |
| 5 | `Thm214` | `JungSFP.lean` | renamed to `Theorem214`, not in the plan |

Left alone and reported rather than changed: `section Cor136` in
`JungCorollary136.lean` and `JungFinite.lean`, and `section Prop134` in
`JungCorollary136.lean`. `Cor` is not one of the three retired abbreviations,
and `Prop134` is a section name, not a declaration; neither was in the plan's
scope. If they should follow the standard as `Corollary136` and
`Proposition134`, say so and it is a two-minute change.

## Consumers outside the Lean sources

A module and namespace rename reaches past `.lean` files. Fixed:

| # | File | What was stale |
| -- | --- | -------------- |
| 1 | `scripts/a6-claims.txt` | 9 claim rows keyed on full constant names (`ScottDomains.LemThirty.Thm29Normal`, `ScottDomains.JungNets.Thm137`, …). This is live data read by `a6-summarize.py`; stale rows would have silently stopped matching and changed the claim counts. |
| 2 | `scripts/a1-r52-claims.txt` | 4 rows under the `LemThirty` namespace |
| 3 | `scripts/a6-query.lean` | one docstring naming `Colimit.Thm29Second` and `LemThirty.Lemma30` |
| 4 | `INDEX.md` | the `Thm18.lean` link (a now-broken path) and 5 declaration names |

Verified end to end: `scripts/a6-env-scan.sh` with `a6-query.lean` runs clean
against the rebuilt environment and now emits
`REFUTEDBY ScottDomains.Lemma30.Lemma30 …` and
`REFUTEDBY ScottDomains.Colimit.Theorem29Second …`, so the roster resolves.
The record histogram moved exactly as the deleted aliases predict and in no
other way: `PROVEDBY` 403 → 346 (−57), `PROPDEF` 120 → 111 (−9, the nine `def`
aliases), and `SIMP` 197, `STRUCT` 25, `REFUTEDBY` 14, `SORRYUSER` 3 all
unchanged. Output in `analyses/a2-r50-env-after.txt`.

**Not fixed, and left for you to route.** `ScottDomains/docs/Status.md`,
`docs/PaperInventory.md`, `docs/PropertiesVsTheorems.md` and
`docs/ScopedClaims.md` still cite retired names, as do roughly thirty
round-specific analysis scripts (`a5-r46-*.lean`, `a3-r47-*.lean`, …). The docs
are yours and were regenerated in r0052; the round-specific scripts are
historical records of the environment as it stood in their round, and rewriting
them would falsify that record. Neither is in this plan's scope and neither
affects the build.

## `sorry`, unchanged

`sorry` stayed at exactly 3 through all 27 builds of this round, and the
transitive `sorryAx` cone measured by `scripts/a1-r52-sorry-cone.lean` is the
same three constants r0052 left, modulo the namespace this round renamed:

    SORRYCONE  ScottDomains.Lemma30.theorem29Normal_unproven
    SORRYCONE  ScottDomains.R49.Agent3.scottHomCRecursive_unproven
    SORRYCONE  ScottDomains.R49.Agent3.strictHomCRecursive_unproven
    SORRYCONECOUNT  3

Measured before phase 2 (`analyses/a2-r50-sorry-cone.txt`, under the old
namespace `LemThirty`) and after phase 3
(`analyses/a2-r50-sorry-cone-final.txt`). No proof body was edited in this
round, so no theorem's axiom footprint could have moved, and it did not.

## Tools added

All in `scripts/`, each with a docstring saying what it decides and on what
authority:

| # | Script | What it does |
| -- | ----- | ------------ |
| 1 | `a2-r50-aliases.py` | inventories the 140 alias statements to a TSV, and deletes them |
| 2 | `a2-r50-fixsites.py` | repoints exactly the sites the elaborator named, at the offsets it named |
| 3 | `a2-r50-phase2.sh` | drives build → fix → build to a fixed point |
| 4 | `a2-r50-retired-defs.py` | the nine `autoImplicit`-masked `def` names |
| 5 | `a2-r50-prose.py` | docstring and comment citations, behind two guards |
| 6 | `a2-r50-leftovers.py` | the census that says whether any retired name survives |
| 7 | `a2-r50-rename-token.py` | one module/namespace token across the package (phase 3) |
