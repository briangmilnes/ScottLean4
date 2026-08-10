---
round: r0050
from: orchestrator
to: orchestrator
subject: numbered-name-standard
date: 2026-0810-14:35
status: pending
related:
  - docs/PaperInventory.md
  - docs/Status.md
---

# r0050 — one naming standard for the numbered results

Every one of Gunter & Scott's 30 numbered results is referred to in Lean by one
of five prefixes. Measured on `main` at `f3d35a5`, over
`ScottDomains/ScottDomains/**/*.lean`:

| # | Prefix | Declarations | Example |
| -- | ----- | -----------: | ------- |
| 1 | `thm` | 50 | `thm11_converse`, `thm22` |
| 2 | `lem` | 36 | `lem17_fun`, `lem9_3` |
| 3 | `lemma` | 24 | `lemma28AtU`, `lemma24_MPair` |
| 4 | `theorem` | 14 | `theorem2`, `theorem7_arrow` |
| 5 | `prop` | 2 | `prop15`, `prop122` |

126 defining declarations across **59 modules**, and roughly 700 reference
sites. The cost of the inconsistency is not cosmetic: `lem24` and
`lemma24_MPair` are **different results from different papers**, and nothing in
either name says so.

## The standard

    theorem_<N>[_<semantic>]        lemma_<N>[_<semantic>]        proposition_<N>[_<semantic>]

`<N>` is Gunter & Scott's printed number. The semantic tail is **kept verbatim**
and simply moves after the number.

| # | Was | Becomes |
| -- | -- | ------- |
| 1 | `thm22` | `theorem_22` |
| 2 | `thm11_converse` | `theorem_11_converse` |
| 3 | `lem17_fun` | `lemma_17_fun` |
| 4 | `lem9_3_printed_false` | `lemma_9_3_printed_false` |
| 5 | `prop15` | `proposition_15` |
| 6 | `theorem7_arrow` | `theorem_7_arrow` |
| 7 | `lemma28AtU` | `lemma_28_atU` |

### Rule 2 — results by other authors carry the author, and the printed dotted number

This is the rule that makes the standard worth doing rather than merely tidy.
`thm137` is **Jung's Theorem 1.37**, not a Theorem 137 of a paper with 30
results, and `lemma24_MPair` is **Gunter 1987's** Lemma 24 while `lem24` is
Gunter & Scott's. Renaming both to `lemma_24_*` would make two different
theorems from two different papers share a stem.

    <author><year?>_<kind>_<N>_<M>[_<semantic>]

| # | Was | Becomes |
| -- | -- | ------- |
| 1 | `thm137` | `jung_theorem_1_37` |
| 2 | `thm137Chains` | `jung_theorem_1_37_chains` |
| 3 | `cor136` | `jung_corollary_1_36` |
| 4 | `prop122` | `jung_proposition_1_22` |
| 5 | `lemma24_MPair` | `gunter87_lemma_24_MPair` |

**Do not guess the attribution.** For every declaration whose number is not in
1–30, read the defining module's docstring and confirm which paper and which
printed number it is before renaming. If the docstring does not say, report the
declaration as unattributed and **leave it alone** — an unattributed name is
better than a confidently wrong one.

### Rule 3 — `Prop`-valued claim `def`s keep UpperCamelCase

`Thm29Normal`, `Lemma30AtV`, `Lem30Arrow`, `StepFunctionsDecidable` are
`Prop`-valued `def`s. Lean's convention is UpperCamelCase for those, and
snake_case would be wrong. Normalize **only the abbreviation**:

    Lem30Arrow → Lemma30Arrow        Thm29Normal → Theorem29Normal

Names already spelled out (`Lemma30AtV`, `Thm29SecondAtDomains` → 
`Theorem29SecondAtDomains`) follow the same single rule: `Thm` → `Theorem`,
`Lem` → `Lemma`, no other change.

### Rule 4 — derivation suffixes use the new short form

`thm18_of_thm137Chains_and_cor136` becomes
`theorem_18_of_jung_theorem_1_37_chains_and_jung_corollary_1_36`. That is long.
Where a name exceeds **60 characters**, drop the `_and_<second>` component and
say the full derivation in the docstring instead — the docstring is where a
reader can afford the words.

## Method — compiler-driven, never string-driven

`CLAUDE.md` forbids string hacking on a programming language, and there is no
Lean CST in `~/projects/CSTs`. So the rename is driven by the **elaborator**,
which is a stronger check than any parser would give: a name is correct exactly
when the package builds.

**Phase 1 — rename the definition, alias the old name. Parallel, no conflicts.**

For each declaration you own:

1. `Edit` the declaration line to the new name.
2. Immediately below it add `alias <oldName> := <newName>`.
3. Build. It must stay at **0 errors, 0 warnings** — every existing reference
   site still resolves, through the alias.

Use a plain `alias`, **not** `@[deprecated] alias`: a deprecated alias emits a
warning at each of ~700 sites, and this project's rule 4 drives warnings to
zero. The alias is scaffolding, deleted in phase 2.

You touch **only the files you own**. You do not edit a single reference site.
That is what makes four agents safe here.

**Phase 2 — delete the aliases; the compiler names every stale site.**

One integrator, after the merge. Delete every `alias` added in phase 1, build,
and the elaborator emits an `unknown identifier` at exactly each remaining
reference. Fix them, rebuild, repeat until 0 errors and 0 warnings. No grep
decides anything; the kernel does.

## Phase 3 — the module filenames

Eight modules carry the retired abbreviations in their own filename. A module
rename cascades further than a declaration rename: every `import` of it, the
package root `ScottDomains.lean`, and any `namespace` inside the file that
repeats the abbreviation.

| # | Module | Becomes | Note |
| -- | ----- | ------- | ---- |
| 1 | `Thm18.lean` | `Theorem18.lean` | |
| 2 | `JungCor136.lean` | `JungCorollary136.lean` | already author-qualified; only the abbreviation changes |
| 3 | `LemThirty.lean` | `Lemma30.lean` | **also a namespace** — `LemThirty.Theorem29Normal`, `LemThirty.Lemma30AtV`. Renaming the namespace touches every qualified reference in the package. **Last, alone.** |

The five `A<n>Thm*.lean` modules are **not** in this round. `A<n>` is the agent
number of whoever wrote the file, and stripping that from all 24 such modules is
r0051's subject; renaming five of them here would leave the other nineteen and
do the work twice.

Run phase 3 **after** phase 2, single-agent, one module at a time: `git mv`, fix
that module's own `import` line in every file the build then names, rebuild to
zero. `LemThirty` is the expensive one and goes **last**, alone, because its
namespace rename reaches the whole package.

## Partition — by defining module

Each agent owns its modules completely: every numbered-result declaration
defined there, and no file outside the list.

| # | Agent | Modules |
| -- | ----- | ------- |
| 1 | agent1 | `Skeleton/**`, `ClosureProperties**`, `Powerdomain/**`, `Kleene/**` |
| 2 | agent2 | `Universality.lean`, `Combinator.lean`, `Atomless.lean`, `Dyadic.lean`, `ContinuousAlgebra.lean`, `Section62.lean`, `UniversalDomain.lean`, `UniformFixedPoint.lean`, `FixedPoint.lean`, `Theorem6.lean`, `IdealCompletion.lean`, `Isomorphism/**` |
| 3 | agent3 | `Jung*.lean`, `Iwamura.lean`, `PropertyM.lean`, `Thm18.lean`, `SFP.lean`, `A5Thm137.lean`, `FinitaryProjectionEmbedding.lean`, `RecursiveDomain.lean` |
| 4 | agent4 | `Effective/**`, `LemThirty.lean`, `BifiniteUniversal.lean`, `PRep*.lean`, `PowerdomainMapRep.lean`, `Lemma28AtU.lean`, `A1*.lean`, `A2*.lean`, `A3*.lean`, `A4*.lean`, `A5Thm29Finite.lean`, `A6*.lean`, `Audit/**` |

## Hard rules

* **No `sorry`.** The package is at 0 and stays at 0.
* **A rename changes a name and nothing else.** No statement, no proof, no
  binder, no docstring claim may change. If a proof breaks, you renamed
  something you should not have.
* Build with `scripts/compile.sh -r r0050`; 0 errors, 0 warnings.
* One shell command per Bash call; never chain; never `cd`. `Edit`/`Write` only,
  never `sed -i`.
* Commit with your worktree's `scripts/gitcp.sh`; **do not push**.

## Deliverable

`reports/r0050-report-from-agentN-to-orchestrator-<subject>.md`: the count
renamed, the count aliased, any declaration left alone as unattributed and why,
and the build's error and warning counts.
