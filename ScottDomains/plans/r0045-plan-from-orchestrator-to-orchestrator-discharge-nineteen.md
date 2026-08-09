---
round: r0045
from: orchestrator
to: orchestrator
subject: discharge-nineteen
date: 2026-0808-21:20
status: pending
related:
  - analyses/specification-defects.2026-0808-21:05.orchestrator.md
  - reports/r0044-report-from-agent6-to-orchestrator-undischarged-defs.md
  - scripts/a6-claims.txt
---

# r0045 — discharge the 19

r0044 found **19 `Prop`-valued `def`s stating a result of Gunter & Scott or of
Jung that no theorem proves.** They are listed in `scripts/a6-claims.txt`. The
`sorry` count cannot see them: `def Foo : Prop := …` is a complete, well-typed
declaration, and nothing was ever claimed to be proved.

**This round discharges as many as can honestly be discharged.**

## What "discharged" means, exactly

A claim `Foo` is discharged when the package contains

    theorem foo : Foo := …

whose conclusion is `Foo` and which has **zero hypotheses beyond instance
binders**. That is agent6's detection rule, and this round is measured by it.

Three things that are **not** discharge, all of which occur already:

| # | Shape | Why it does not count |
| -- | ---- | --------------------- |
| 1 | `theorem foo (h₁ : A) (h₂ : B) : Foo` | a **reduction** — proves `A → B → Foo`. Six of the 19 already have these; `PRep.Lemma28AtU` has three, assuming 2, 4 and 5 hypotheses |
| 2 | `theorem foo : Foo := sorry` | worse than leaving it — it asserts the claim and propagates `sorryAx` |
| 3 | restating `Foo` more weakly and proving that | that is a new claim, not this one |

**Reductions are still real progress** and Theorem 18 closed by exactly that
route. If you cannot discharge, a reduction with *strictly fewer* hypotheses than
the best existing one is a good result — report it as a reduction, plainly
labelled, and say which hypotheses remain.

## A claim may be false

At least one of the 19 is suspected false as stated. `PaperInventory.md` row 2f
records that `Colimit.Thm29Second` is false without `[Domain E]`, and r0043's
agent5 found the refutation is now the cheapest unclosed item in the project
because it needs an uncountable flat cpo and `Flat ℝ` supplies one.

**A kernel-checked refutation discharges the question and is a first-class
result.** Prove `¬ Foo`, name it, and say so. Do not quietly restate `Foo` with
the missing hypothesis added and call it proved — that is shape 3 above, and
r0044 found nine rows where exactly that had happened without being recorded.

If you conclude a claim is false, **check the paper's printed statement first**.
Nine printed defects are on record in `docs/StatementRecovery.md` and
`PaperInventory.md` row 2c; a tenth is possible but the prior is against it, and
r0044 found one case (Theorem 26) where we had wrongly convicted the paper — the
argument there refutes the paper's *proof*, not its theorem.

## Streams

| # | Agent | Cluster | Claims |
| -- | ----- | ------- | -----: |
| 1 | agent1 | §3.2 effective presentations | 4 |
| 2 | agent2 | §7.3 Lemma 28 and its instantiation at `U` | 2 |
| 3 | agent3 | §7.4 Theorem 29, Lemma 30 | 6 |
| 4 | agent4 | powerdomain-map representability | 4 |
| 5 | agent5 | Jung's Theorem 1.37 and its two weakenings | 3 |

### agent1 — `Effective.{StepFunctionsDecidable, Theorem7ArrowRecursive, Theorem7StrictRecursive, PreservesRecursivePresentation}`

Read `docs/StructuresVsTypeClassesVsPropsInLean4.md` before starting; this
cluster is where the encoding mistake it describes lives.

`EffectivePresentation` carries `DecidablePred` fields, and `Classical.dec`
inhabits them for free, so `nonempty_effectivePresentation` proves *every* domain
has one. Two of r0043's `S+P` rows are vacuous through it. **Do not discharge
these four by routing through that vacuity** — a proof that goes through
`Classical.dec` proves nothing and will be rejected at review.

The honest target is `RecursivePresentation`, which adds `RecursiveLE` and
`RecursiveNormal` and is deliberately uninstantiated. If discharging a claim
requires first constructing a genuine `RecursivePresentation` for some concrete
domain, that construction is the valuable half — do it, and say if the claim then
follows or still does not.

`ComputablePred p ↔ ∃ (_ : DecidablePred p), Computable fun a => decide (p a)`
is the non-free notion. The `Computable` conjunct is not obtainable from
`Classical.choice`.

### agent2 — `PRep.{Lemma28, Lemma28AtU}`

r0043 found `lemma28AtU_of''` restructured the `(·)♯`/`(·)♭` conjuncts from
arity 2 to arity 4, **and all four are still open hypotheses** — so the existing
"proof" moved the obligation rather than reducing it. Check that reading; if the
arity grew without the hypotheses getting weaker, say so.

r0038 identified the missing action of a map on a powerdomain as the blocker.
That is no longer missing — `PowerdomainMap` now has `exists_unique_map`, both
functor laws, and `isProjection_plotkin`. **The blocker on record is stale.**
Re-derive what actually blocks these two now, from the current tree.

Coordinate with agent4: its four claims are about the same operators.

### agent3 — `Colimit.{Thm29Second, Lem30Arrow}`, `LemThirty.{Thm29SecondAtDomains, Thm29Normal, Lemma30, Lemma30AtV}`

The largest cluster and the one most likely to contain a genuine theorem nobody
has proved. `Thm29Normal` is a real mathematical statement — a normal embedding
of `K(E)` into `A∞` for every bifinite `E`.

`Thm29Second` is the suspected-false one; see above. `Flat ℝ` exists now.

`LemThirty.lean:469` says the reduction from `Thm29Normal` to the
embedding–projection pair is "elementary manipulation of ideals, and it is
carried out below". If that is right, discharging `Thm29Normal` discharges more
than one row — establish the dependency order among your six **before** picking
what to attack, and report it as a finding either way.

### agent4 — `PowerdomainMap.Rep.{SmythImageIso, SmythFamilyLUB, HoareImageIso, HoareFamilyLUB}`

Four named obligations, in two symmetric pairs. **Expect the Smyth and Hoare
arguments to be dual**; if you close one, the other should follow by the same
route, and if it does not, that asymmetry is itself the finding.

`FlatPowerdomain` has `hoare_natBot_orderIso_powerset`,
`smyth_natBot_orderIso` and `plotkin_natBot_orderIso` — concrete calculations at
`N⊥` that may show the shape of the general argument.

Note that `smyth_natBot_orderIso`'s docstring is known false: it claims a
directed-supremum clause its statement lacks, where the Hoare one does carry it
(r0044 agent8). Do not take that docstring as a specification.

### agent5 — `JungNets.{Thm137, Thm137Chains}`, `PropertyM.Thm137Omega`

**Most likely to close, and worth doing first.** `Iwamura.lean` already contains
`thm137_of_thm137Chains` (`:614`), `thm137Chains_iff_thm137` (`:619`) and
`thm137Chains_of_wellOrderedInfima` (`:631`), plus Iwamura's lemma
(`exists_chain_directed_cover`) and Markowsky's theorem
(`hasChainSuprema_iff_hasDirectedSuprema`) — all proved, all at footprint
`[propext, Classical.choice, Quot.sound]`.

So the machinery may already be present and only the final composition missing.
**Check that first, in one hour, before doing anything else** — if
`thm137Chains_of_wellOrderedInfima` plus an existing well-ordered-infima result
discharges `Thm137Chains` outright, the round's cheapest win is there.

`docs/AxiomFootprint.md` records why this cluster genuinely needs choice: Iwamura
well-orders a directed set in order type `|D|`. Do not try to avoid choice here.

## Hard rules

**This round writes `.lean` files, unlike r0044.** Performance.md's
declaration-collision limit therefore applies: r0028 produced 2 name clashes
among 5 agents. **Every new declaration goes in your own namespace**
(`ScottDomains.R45.AgentN` or an existing cluster namespace you alone touch), and
new files are prefixed with your stream. The orchestrator runs the composition
check (`scripts/axioms.sh -i`) at merge, which is the only thing that catches a
clash — `lake build` never imports two unrelated modules into one environment.

* **No `sorry`.** The package is at 0 and must stay at 0. A `sorry` is worse than
  leaving the claim undischarged, per the table above.
* **Do not weaken a claim's statement to close it.** If you believe a claim is
  mis-stated, say so and leave it; changing `def Foo` is a specification change
  and belongs to the orchestrator, not to a proving stream.
* Build with `scripts/compile.sh -r r0045`. Zero errors, zero warnings.
* `#print axioms` every theorem you add, via `scripts/axioms.sh`. Report the
  footprint. `sorryAx` in a footprint is a failed round.
* One command per Bash call; never chain; never `cd`. `Edit`/`Write` only — no
  heredocs, no `sed -i`. Commit with your worktree's `scripts/gitcp.sh`; do not
  push.

## Evidence rules, carried forward because they worked

* **A negative result is a result.** r0043's agent5 moved zero rows and produced
  that round's sharpest finding. If a claim is genuinely open, the valuable
  output is *why* — what is missing, and what would supply it.
* **Do not inflate.** r0044's agent6 had 55 available and reported 19.
* **Correct the other streams, the plan, and the orchestrator.** Four r0044
  agents corrected me and all four were right. **The plan is not evidence** — if
  this plan asserts something about the tree that is false, that is a finding.
* **Check against the built `.olean`**, not a source line. r0044 found 218 sites
  where cited names do not resolve, 40 of them in live docstrings, so a
  docstring is not a specification.

## Deliverable

`reports/r0045-report-from-agentN-to-orchestrator-discharge-<cluster>.md`: per
claim, its status after your work — **discharged** (name the theorem and its
axiom footprint), **refuted** (name the theorem), **reduced** (state the
remaining hypotheses and how many fewer than before), or **open** (state what is
missing and what would supply it).

## Orchestrator steps

1. Commit this plan; fast-forward all worktrees **before** launching — r0044's
   agents started from branches that did not contain their own plan, which was my
   error and cost agent8 a restart.
2. Merge, then run the composition check across all five namespaces.
3. Re-run agent6's detector (`scripts/a6-*`). **The round's measure is the count
   of remaining undischarged claims**, and it must be re-derived, not subtracted.
4. Update `PaperInventory.md` row 2j and `analyses/` with the measured figure.
