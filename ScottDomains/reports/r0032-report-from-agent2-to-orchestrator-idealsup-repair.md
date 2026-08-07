---
round: r0032
from: agent2
to: orchestrator
subject: idealsup-repair
date: 2026-0806-21:04
started: 2026-0806-20:44
finished: 2026-0806-21:04
related:
  - plans/r0032-plan-from-orchestrator-to-agent2-idealsup-repair.md
  - reports/r0031-report-from-agent2-to-orchestrator-lemma-13.md
---

# r0032 agent2 — `idealSup` repaired; `BoundedComplete` reinstated for `D♭` and `D♯`

## Result

`IdealCompletion.idealSup` now branches on `Order.IsIdeal (genIdeal S)` — the
generated ideal being an ideal — instead of `Order.IsIdeal (⋃₀ S)`. Every
statement in `IdealCompletion.lean` survives verbatim, including both halves of
Theorem 11; three of them (`coe_idealSup_of_isIdeal`, `mem_sSup_iff`,
`idealSup_empty`) survive because the new guard's value provably agrees with the
old one's wherever the old guard held, and `instCompletePartialOrder`'s
`lubOfDirected` proof needed no edit at all. The three refutations
`not_boundedComplete_hoare`, `_smyth`, `_plotkin` are retired; two
`BoundedComplete` instances take their place.

Whole project: **0 errors, 0 warnings, 1 pre-existing `sorry`** (in
`Skeleton/Section6.lean:196`, present at `main`, not in either file I own).

## The exact diff to `idealSup` and its guard

Before (`IdealCompletion.lean`):

```lean
noncomputable def idealSup (S : Set (IdealCompletion A)) : IdealCompletion A :=
  if h : Order.IsIdeal (⋃₀ (SetLike.coe '' S)) then ofIdeal h.toIdeal else ⊥
```

After:

```lean
noncomputable def idealSup (S : Set (IdealCompletion A)) : IdealCompletion A :=
  if h : Order.IsIdeal (genIdeal S) then ofIdeal h.toIdeal else ⊥
```

with the value moved into the shared module, at `[LE A]` — no `Preorder`, no
`OrderBot`:

```lean
def genIdeal (S : Set (IdealCompletion A)) : Set A :=
  {c | ∀ K : IdealCompletion A, (∀ I ∈ S, I ≤ K) → c ∈ K}
```

That is the whole definitional change: one guard, one value. Everything else in
this round is a lemma establishing that the change loses nothing and gains
bounded completeness.

## The agreement lemma

The plan asked for the agreement to be a Lean lemma, not prose. It is
`IdealCompletion.genIdeal_eq_sUnion_of_isIdeal`:

```lean
theorem genIdeal_eq_sUnion_of_isIdeal {S : Set (IdealCompletion A)}
    (h : Order.IsIdeal (⋃₀ (SetLike.coe '' S))) :
    genIdeal S = ⋃₀ (SetLike.coe '' S)
```

`⊇` is `sUnion_subset_genIdeal` (each member of the family lies in every ideal
above it). `⊆` is `genIdeal_subset` instantiated at `K := ofIdeal h.toIdeal`:
under the hypothesis the union *is* an ideal above the family, hence one of the
sets being intersected. Note the hypothesis is the old guard verbatim, so the
statement reads: wherever the old definition fired, the new one computes the
same set. On a nonempty directed family the hypothesis is discharged by the
existing `isIdeal_sUnion`, which is Gunter & Scott's own first proof paragraph.

Consequences, all kernel-checked:

| # | Statement | Status |
| - | --------- | ------ |
| 1 | `coe_idealSup_of_isIdeal` | statement unchanged; reproved via the agreement lemma |
| 2 | `mem_sSup_iff` | statement **and proof** unchanged |
| 3 | `idealSup_empty` | statement unchanged; new proof (see below) |
| 4 | `instCompletePartialOrder` (`lubOfDirected`) | statement **and proof** unchanged |

Row 3 is the one place the two definitions take different branches on the same
input. The old guard *failed* on `∅` (the empty union is not an ideal, being
empty) and the `⊥` came from the negative branch. The new guard *holds* on `∅`:
`genIdeal_empty` proves `genIdeal ∅ = ↓⊥` — every ideal is vacuously above `∅`,
and the intersection of all ideals is `↓⊥` because each contains `⊥` and is
downward closed — so the positive branch returns `↓⊥`, which is `⊥`. Same value,
opposite branch.

## New declarations in `IdealCompletion.lean`

| # | Name | Content |
| - | ---- | ------- |
| 1 | `genIdeal` | the generated ideal, as an intersection; `[LE A]` |
| 2 | `mem_genIdeal`, `subset_genIdeal`, `genIdeal_subset` | its two defining halves (upper bound, least) |
| 3 | `sUnion_subset_genIdeal`, `genIdeal_eq_sUnion_of_isIdeal` | agreement with the union |
| 4 | `coe_idealSup_of_isIdeal_genIdeal` | the positive-branch defining equation |
| 5 | `isLUB_idealSup_of_isIdeal_genIdeal` | `idealSup` is the least upper bound whenever its guard holds |
| 6 | `genIdeal_empty`, `isIdeal_genIdeal_empty` | the empty case |
| 7 | `isIdeal_genIdeal` | moved from `BoundedComplete.lean`; the guard holds on a bounded family when bounded pairs of `A` have least upper bounds |
| 8 | `boundedComplete` | `BoundedComplete (IdealCompletion A)` from that same hypothesis |

Item 5 is the load-bearing one and it is three lines: upper bound by
`subset_genIdeal`, least by `genIdeal_subset`. Item 7 is r0031's proof moved
verbatim except for `IdealCompletion.bot_mem K` becoming `bot_mem K` inside the
namespace; the mathematical content is unchanged — directedness is where
boundedness is spent, and only binary joins of *bounded* pairs are consumed.

## `BoundedComplete`: what now holds, what was retired

Reinstated, as instances in `ScottDomains.PowerdomainBC`:

| # | Instance | Type | Hypotheses on `α` |
| - | -------- | ---- | ----------------- |
| 1 | `instBoundedCompleteHoare` | `BoundedComplete (Hoare.Powerdomain α)` | `[CompletePartialOrder α] [Domain α]` |
| 2 | `instBoundedCompleteSmyth` | `BoundedComplete (Smyth.Powerdomain α)` | `[CompletePartialOrder α] [BoundedComplete α]` |

Each is one application of `IdealCompletion.boundedComplete` to the pair-join
lemma r0031 already proved (`hoare_exists_isLUB_pair`, `smyth_exists_isLUB_pair`);
no new order theory was needed. The hypothesis lists differ from `lem13_hoare`
and `lem13_smyth` deliberately: instance 1 does **not** take `[BoundedComplete α]`
because the Hoare join is the union and exists for every pair — the paper states
the hypothesis, the instance does not need it — and instance 2 does not take
`[Domain α]` because `Smyth.Powerdomain` does not and countability is not used to
build a join. The theorem forms `lem13_hoare` / `lem13_smyth` keep the paper's
own hypothesis lists and are unchanged.

Retired, with everything they depended on:

| # | Retired declaration | Why |
| - | ------------------- | --- |
| 1 | `not_boundedComplete_hoare` | false against the repaired `sSup`; instance 1 above proves its negation |
| 2 | `not_boundedComplete_smyth` | false against the repaired `sSup`; instance 2 above proves its negation |
| 3 | `not_boundedComplete_plotkin` | its proof route (`sSup = ⊥` on a non-directed union) no longer exists |
| 4 | `not_boundedComplete_of_not_directed_pair` | the general refutation the three used |
| 5 | `sSup_eq_bot_of_not_directedOn` | false: `sSup` is no longer `⊥` on a non-directed bounded family |
| 6 | `genIdeal`, `isIdeal_genIdeal` (local copies) | moved into `IdealCompletion.lean` |
| 7 | `smythPt_le_smythPt`, `plotkinPt_le_plotkinPt` | only fed the retired refutations |

**No `BoundedComplete` instance is claimed for `D♮`.** The Egli–Milner order
supplies no join of a bounded pair — `Plotkin.not_single_le_pair` is the standing
kernel-checked reason — so `IdealCompletion.boundedComplete` has no input for the
convex powerdomain, and Lemma 13 does not name it. This is recorded in the
module docstring, not asserted as a theorem: r0032 neither proves nor refutes
bounded completeness of `D♮`.

## The witness, re-checked rather than deleted

The plan asked for a docstring recording the defect and the witness. The module
docstring now carries the full history (defect, r0031 measurement, r0032 repair),
and in addition the witness itself is kept and re-checked in the other direction,
because a docstring cannot detect a regression. Three statements over `P N`,
where `{0}` and `{1}` are incomparable compacts and `{0,1}` bounds both:

| # | Statement | What it measures |
| - | --------- | ---------------- |
| 1 | `bddAbove_hoareWitness` | `{↓{{0}}, ↓{{1}}}` is bounded above by `↓{{0,1}}` in `D♭` |
| 2 | `not_isIdeal_sUnion_hoareWitness` | the **pre-r0032 guard still fails** on it — the union is not an ideal |
| 3 | `isLUB_sSup_hoareWitness` | the repaired `sSup` *is* the least upper bound of that family |
| 4 | `sSup_hoareWitness_ne_bot` | and the value returned is not `⊥`, which the old one gave |

Rows 2 and 3 together are the measurement that the repair is real: the same
family that took the old negative branch now takes the new positive one and gets
its genuine least upper bound. Without row 4, `instBoundedCompleteHoare` could in
principle be satisfied by a `sSup` no bounded family ever reaches. Only the Hoare
reading is carried forward; r0031 recorded `D♯` and `D♮` with the same compacts,
nothing in the repair is specific to the ordering, and `D♮` has no instance to
check against.

## Theorem 11

**Untouched.** `thm11` and `thm11_converse` have byte-identical statements, as do
`instDomain`, `instIsAlgebraic`, `compacts_eq_range_principal`,
`isCompactElement_principal`, `exists_eq_principal_of_isCompactElement` and
`orderIsoIdealCompletionCompacts`. Nothing was weakened and no `sorry`,
`set_option` or linter suppression was introduced. `git diff` confirms the only
non-comment edits below the `### The cpo structure` heading are the `idealSup`
body, the reproof of `coe_idealSup_of_isIdeal` and `idealSup_empty`, and the new
declarations listed above; the `Converse` section is unchanged apart from its
position in the file.

## `#print axioms`

Run at r0032, then removed so the build emits no `info` lines; both files carry
the results as a trailing comment block. **No declaration depends on `sorryAx`.**

`IdealCompletion.lean`:

```
genIdeal                                  [propext, Quot.sound]
genIdeal_eq_sUnion_of_isIdeal             [propext, Quot.sound]
idealSup                                  [propext, Classical.choice, Quot.sound]
coe_idealSup_of_isIdeal_genIdeal          [propext, Classical.choice, Quot.sound]
isLUB_idealSup_of_isIdeal_genIdeal        [propext, Classical.choice, Quot.sound]
coe_idealSup_of_isIdeal                   [propext, Classical.choice, Quot.sound]
idealSup_empty                            [propext, Classical.choice, Quot.sound]
mem_sSup_iff                              [propext, Classical.choice, Quot.sound]
isIdeal_genIdeal                          [propext, Classical.choice, Quot.sound]
boundedComplete                           [propext, Classical.choice, Quot.sound]
instCompletePartialOrder                  [propext, Classical.choice, Quot.sound]
instIsAlgebraic                           [propext, Classical.choice, Quot.sound]
instDomain                                [propext, Classical.choice, Quot.sound]
thm11                                     [propext, Classical.choice, Quot.sound]
thm11_converse                            [propext, Classical.choice, Quot.sound]
compacts_eq_range_principal               [propext, Classical.choice, Quot.sound]
isCompactElement_iff_exists_eq_principal  [propext, Classical.choice, Quot.sound]
orderIsoIdealCompletionCompacts           [propext, Quot.sound]
OrderIso.map_sSup_of_directedOn           [propext, Quot.sound]
```

`Powerdomain/BoundedComplete.lean`:

```
mem_sUnion_coe_iff                        [no axioms]
exists_isLUB_of_bddAbove_idealCompletion  [propext, Classical.choice, Quot.sound]
hoare_exists_isLUB_pair                   [propext, Classical.choice, Quot.sound]
lem13_hoare                               [propext, Classical.choice, Quot.sound]
instBoundedCompleteHoare                  [propext, Classical.choice, Quot.sound]
joinCompact                               [propext, Classical.choice, Quot.sound]
mem_smythJoin                             [propext, Classical.choice, Quot.sound]
smyth_exists_isLUB_pair                   [propext, Classical.choice, Quot.sound]
lem13_smyth                               [propext, Classical.choice, Quot.sound]
instBoundedCompleteSmyth                  [propext, Classical.choice, Quot.sound]
not_isIdeal_sUnion_hoareWitness           [propext, Classical.choice, Quot.sound]
isLUB_sSup_hoareWitness                   [propext, Classical.choice, Quot.sound]
sSup_hoareWitness_ne_bot                  [propext, Classical.choice, Quot.sound]
```

`genIdeal` and its agreement with the union are choice-free: `genIdeal` is a
comprehension and the agreement proof is two subset inclusions. `Classical.choice`
enters `idealSup` and everything downstream of it through the `dite` on
`Order.IsIdeal (genIdeal …)`, which is not a decidable predicate — the same route
as before the repair.

## `sorry` count

- `ScottDomains/ScottDomains/IdealCompletion.lean` — **0**
- `ScottDomains/ScottDomains/Powerdomain/BoundedComplete.lean` — **0**
- whole project — **1**, at `ScottDomains/Skeleton/Section6.lean:196`, present at
  `main` before this round and in neither file I own.

The only textual occurrences of the string `sorry` in my two files are the words
`sorryAx` inside the audit comment blocks.

## Build

`scripts/compile.sh -r r0032` over the whole library,
`ScottDomains/logs/compile-20260806-210233.agent2.log`. Verbatim final `lake
build` line and footer:

```
Build completed successfully (1066 jobs).
--- times ---
Elapsed (wall clock): 0:02.43
Maximum resident set size (kbytes): 1708188
--- build ---
finished:         2026-08-06T21:02:37-07:00
exit status:      0
user cpu:         2.91s
system cpu:       0.74s
cpu use:          150%
peak rss single:  1668 MiB (largest one process, GNU time)
peak pss tree:    1792 MiB (process group, shared pages apportioned)
peak rss tree:    2451 MiB (process group, shared pages counted per process)
jobs:             1066
lean diagnostics: 0
lake errors:      0
sorry decls:      1
other warnings:   0
```

The 210233 run replayed most modules from cache; the preceding full run
`compile-20260806-205916.agent2.log` elaborated every downstream module against
the repaired `idealSup` from scratch — `Powerdomain.Universal`,
`ComputableFunction`, `EffectivePresentation`, `ContinuousConstruction` all
built, 0 diagnostics. The edits between the two runs were comments and the
removal of the temporary `#print axioms` lines. **No file outside the two I own
was touched**, so the plan's stop-and-report condition was never reached.

Cost: `git diff --stat` reports 392 insertions, 290 deletions across the two
files. `IdealCompletion.lean` grew from 491 to 653 lines;
`BoundedComplete.lean` shrank from 571 to 511.

## Rules

| # | Rule | Compliance |
| - | ---- | ---------- |
| 1 | build via `scripts/compile.sh`, no `timeout` prefix | followed; Bash tool timeout raised instead |
| 2 | errors and warnings to zero, no `set_option` | 0 / 0; no linter suppression added |
| 3 | `Edit`/`Write` only | followed; no `sed -i`, no heredoc, no shell redirection into a source file |
| 4 | do not weaken Theorem 11 or any statement in `IdealCompletion.lean` | followed; every pre-existing statement is byte-identical |
| 5 | commit with `scripts/gitcp.sh` on `agent2`, do not push | followed; the push step reports no tracking information, as expected for an agent branch |

## Commits

On branch `agent2`, off `main` at `f4f9b00`. Not pushed, no upstream set.

| # | SHA | Contents |
| - | --- | -------- |
| 1 | `e371ed9` | the repair: `IdealCompletion.lean`, `Powerdomain/BoundedComplete.lean`, and the five `compile` logs |
| 2 | `dd37d49` | this report |
