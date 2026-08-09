---
round: r0044
from: agent3
to: orchestrator
subject: vacuity-effective
date: 2026-0808-17:35
started: 2026-0808-17:10
finished: 2026-0808-17:35
related:
  - plans/r0044-plan-from-orchestrator-to-orchestrator-specification-defects.md
  - docs/AxiomFootprint.md
  - analyses/property-coverage-remeasure.2026-0808-16:55.orchestrator.md
---

# r0044 agent3 — Class 2 vacuity sweep of `Effective/`, `Kleene/`, `Isomorphism/`, `Skeleton/`

Area: 20 `.lean` files in four module trees, **309 declarations** after excluding
auto-generated ones (466 constants). No `.lean` file in the package was edited.

## The count

| # | Class | Theorems | Binders | Impugns `S+P`? |
| -- | ----- | -------: | ------: | -------------- |
| 1 | **Vacuous** — hypothesis dead in the proof term *and* absent from the statement | **2** | 4 | **yes** |
| 2 | **Statement-vacuous, proof honest** — hypothesis consumed by the proof, but the statement is provable without it | **1** | 2 | no — see row 2 below |
| 3 | **Over-hypothesized** — redundant instance binder; theorem proved is *stronger* than the one stated | **8** | 15 | no — opposite sign |
| 4 | Instance binder derivable from the remaining binders (§4 of the instrument) | **0** | 0 | — |

**The vacuity count for this area is 2**, and both were already known. The sweep
found no third instance. That is the headline: the mechanical instrument, run
over all 309 declarations with no name-based filtering, reproduces exactly the
two instances the plan named and adds none.

## The list

### Class 1 — vacuous (2 theorems, 4 dead hypotheses)

| # | Declaration | Site | Dead binders | Paper row |
| -- | ---------- | ---- | ------------ | --------- |
| 1 | `Effective.theorem7_strict` | `Effective/FunctionSpace.lean:256` | `(_d : EffectivePresentation α)`, `(_e : EffectivePresentation β)` | Theorem 7, third sentence (`D ⊸ E` effectively presented) |
| 2 | `Effective.operator_preserves_effectivePresentation` | `Effective/FunctionSpace.lean:280` | `(_d : EffectivePresentation α)`, `(_e : EffectivePresentation β)` | §3.2's closing claim, "all of these operators preserve the property of having an effective presentation" |

Both proofs are `nonempty_effectivePresentation _`. The hypotheses occur in
neither the elaborated statement nor the proof term, so each theorem is exactly
its own conclusion with the hypotheses stripped. Machine-checked in
`scripts/a3-delete.lean`: the deleted-hypothesis forms elaborate, kernel-accepted.

These are the two the plan named. The instrument confirms them independently and
by occurrence, not by reading the docstrings that already flag them.

### Class 2 — statement-vacuous, proof honest (1 theorem, 2 hypotheses)

| # | Declaration | Site | Binders | Paper row |
| -- | ---------- | ---- | ------- | --------- |
| 3 | `Effective.theorem7_arrow` | `Effective/FunctionSpace.lean:243` | `(d : EffectivePresentation α)`, `(e : EffectivePresentation β)` | Theorem 7, second sentence — the plan's row 13 |

**The plan is right that row 13 is not vacuous, and the instrument refines why.**
`d` and `e` *are* consumed: the proof is `⟨scottHom d e⟩`, and `scottHom`'s
enumeration is the paper's step-function enumeration, indexed through
`d.enum`/`e.enum` with surjectivity supplied by `d.enum_surjective` and
`e.enum_surjective`. So it is not vacuous in the sense of class 1.

What the instrument nevertheless establishes is that neither hypothesis occurs in
the *statement*: the conclusion is `Nonempty (EffectivePresentation (ScottHom α β))`,
which mentions neither. And `Domain (ScottHom α β)` is a registered instance
(`FunctionSpaceCountable.lean:122`), so this elaborates and is kernel-accepted:

    example : Nonempty (EffectivePresentation (ScottHom α β)) :=
      nonempty_effectivePresentation _

with `d` and `e` deleted. The theorem's *statement* therefore buys nothing over
`nonempty_effectivePresentation`; its *proof* does the paper's work. Row 13
should stay `S+P` — the label is about the paper's sentence being stated and
proved, and the proof is the paper's — but the row deserves the same footnote
`AxiomFootprint.md` already carries: at the `DecidablePred` rendering, the
sentence it states is true for free, and the version that is not is
`Theorem7ArrowRecursive`, which remains open. This is a distinction of
proof-strength, not a defect to be counted, and I have **not** counted it in the
vacuity total.

### Class 3 — over-hypothesized (8 theorems, 15 redundant instance binders)

Every hit is an instance binder, never a stated hypothesis:

| # | Declaration | Site | Dead binders |
| -- | ---------- | ---- | ------------ |
| 4 | `lem10_prod` | `Skeleton/Lemma10.lean:69` | `[Domain α]`, `[Domain β]` |
| 5 | `lem10_lift` | `Skeleton/Lemma10.lean:174` | `[Domain α]` |
| 6 | `lem10_strict` | `Skeleton/Lemma10.lean:211` | `[Domain α]`, `[BoundedComplete α]`, `[Domain β]` |
| 7 | `lem10_sum` | `Skeleton/Sum.lean:120` | `[Domain α]`, `[Domain β]` |
| 8 | `lem17_prod` | `Skeleton/Lemma17.lean:98` | `[Domain α]`, `[Domain β]` |
| 9 | `lem17_lift` | `Skeleton/Lemma17.lean:200` | `[Domain α]` |
| 10 | `lem17_sum` | `Skeleton/Sum.lean:553` | `[Domain α]`, `[Domain β]` |
| 11 | `lem17_smash` | `Skeleton/Sum.lean:911` | `[Domain α]`, `[Domain β]` |

**These are not vacuity and must not be added to the vacuity count.** A theorem
with a redundant hypothesis proves *more* than it claims; a vacuous theorem
proves less. Lemma 10 for products holds for every bounded-complete cpo, not only
for domains. The substantive hypotheses of these theorems are live in every case:
`lem17_prod`'s `(_h₁ : IsBifinite α)` and `(_h₂ : IsBifinite β)` are consumed at
`Lemma17.lean:110-111` and are correctly not flagged.

One of the eight is machine-checked rather than argued: `scripts/a3-delete.lean`
restates `lem10_prod` with both `[Domain _]` binders deleted and closes it with
the original proof script verbatim, kernel-accepted. The other seven follow by
the same strengthening step — a binder occurring in neither the type nor the
value is removable in the calculus — which is what Batteries' `unusedArguments`
is documented to detect and what my independent implementation recomputes.

`Domain` is not itself freely inhabited: it is a `Prop`-valued class carrying
`IsAlgebraic` plus `Set.Countable (compacts α)` (`Domain.lean:128`), and
`Classical.dec` supplies neither. This is the check that class 3 is a different
failure mode from `EffectivePresentation`'s and not the same one twice.

### Class 4 — trivially-inhabited structures (the plan's method 3)

Only **two** data structures/inductives are declared in this area:

| # | Structure | Theorem data-binders of that type | Freely inhabited? |
| -- | -------- | --------------------------------: | ----------------- |
| 12 | `Kleene.NatBot` | 7 | inhabited, but parameterless — quantifying over it is quantifying over a fixed carrier, not over an assumption, so no theorem is weakened by it |
| 13 | `Effective.RecursivePresentation` | 1 | **no** — deliberately uninstantiated; it adds `RecursiveLE` and `RecursiveNormal`, genuine `ComputablePred` claims |

`EffectivePresentation` itself is declared outside this area
(`EffectivePresentation.lean`, agent5's) but is the type of every class-1 and
class-2 hypothesis above. Its free inhabitedness is re-checked here:
`nonempty_effectivePresentation γ` for every `[CompletePartialOrder γ] [Domain γ]`,
elaborated in `scripts/a3-delete.lean`.

So the answer to "find the others" is: **in this area there are none.**

## WHAT THE INSTRUMENT DOES NOT MEASURE

Two distinct defects exist and sections 1–3 of the instrument find only the first:

1. **hypothesis unused by the proof term** — the proof never touches the binder.
   Decidable by inspecting the term. This is what my count above measures.
2. **hypothesis used but unnecessary** — the proof consumes it, yet a different
   proof of the same statement does not need it. No inspection of the existing
   term can see this; only reproving can.

agent1's `Kleene.sSup_recoverAt` is the standing counterexample: `[BoundedComplete β]`
is genuinely consumed, so `unusedArguments` and my section 1 both report it clean,
and agent1 nevertheless deleted the binder and reproved the statement from
`IsAlgebraic β`'s `directedOn_compactsBelow`, kernel-accepted at footprint
`[propext, Quot.sound]`. **My count of 2 is a count of unused hypotheses, a
strict subset of unnecessary ones.** The rest of class 2 in my area is unmeasured,
by this instrument and by any instrument in this round.

Section 4 is a sound but partial attack on defect 2: an instance binder that the
*remaining* binders already synthesize is unnecessary whatever the proof does with
it. It found **0** in this area, with both controls passing (below), so where the
missing argument is instance resolution the area is clean. Where the missing
argument is mathematics — agent1's case, and agent2's finding that Lemma 17's
`[BoundedComplete β]` is by contrast genuinely needed at `Lemma17.lean:408` — only
reproving decides, and this round did not do that systematically.

## The instruments, in the order the plan asked for them

### 1. Lean's own linters — `#lint only unusedArguments` — **works, with one catch**

The negative result the plan asked to have reported precisely, then the positive one.

**First attempt returned "Found 0 errors in 0 declarations".** The cause is not the
linter. `Batteries.Tactic.Lint.getDeclsInPackage` selects declarations by
module-name prefix, and the package root `ScottDomains.lean` **imports only
Mathlib** — it declares nothing and pulls in none of the package's own modules. A
driver file whose only import is `ScottDomains` therefore has 2336 modules in
scope, exactly one of them named `ScottDomains`, and 0 of 235 432 imported
constants mapping into it. Measured with `scripts/a3-diag.lean`.

**The fix is a literal import block naming all 100 modules**, generated from the
file tree by `scripts/a3-gen.sh`. With that, `#lint only unusedArguments in
ScottDomains` runs over 2609 declarations and reports **18 unused arguments**
package-wide in about 20 seconds. It works. The other two vacuity streams should
use it — but must generate the import block, not `import ScottDomains`.

**The catch, and why it is not sufficient on its own.** `unusedArguments` exempts
any binder whose user name begins with `_`. Both known instances name their dead
hypotheses `_d` and `_e`, so **the linter reports `theorem7_strict` and
`operator_preserves_effectivePresentation` as clean.** Of the 18 it does report,
every one is an instance binder — the class-3 population above. Used alone it
would have found zero vacuous theorems in this area and reported the class-3
finding as the whole result.

### 2. Hypothesis deletion — `scripts/a3-delete.lean` — **works, and is the evidence**

Four `example`s restate candidates with the hypothesis deleted and prove them.
All four elaborate, zero errors. This is what turns a static occurrence report
into a machine-checked claim, and it is what settles row 3 (`theorem7_arrow`)
and row 4 (`lem10_prod`).

### 3. Trivially-inhabited structures — **section 3 of `a3-vacuity`, works**

Enumerates every `structure`/`inductive`/`class` declared in the filtered modules
whose sort is not `Prop`, with the number of theorem data-binders of that type.
Two hits in this area, neither harmful (table above). `Prop`-valued classes are
excluded deliberately: for `Domain` or `BoundedComplete`, inhabitedness is the
mathematics, not an encoding artifact.

### 4. Proofs closed by one tactic — **run, and it is worthless here**

A grep for proofs that are exactly `rfl`, `by rfl`, `by simp`, `by trivial` or
`by decide` returns **24 sites** in this area: 6 `decide`-closed `example`s in
`Effective/Powerset.lean`, 17 definitional-unfolding lemmas mostly tagged
`@[simp]` (`liftExtendFun_bot`, `smashVal_bot`, `compFun_apply`, `bot_eq`,
`Smash`'s four `Equiv` fields, …), and 1 `have … := rfl` inside `lem10_prod`'s
proof, which is not a declaration at all. Not one is substantive-looking, and the
six `example`s exist *precisely to demonstrate that the two decision procedures
run in the kernel* — the opposite of a vacuity signal. The proxy's hit list and
the defect population are disjoint here. Recommend the other two streams not
spend time on it.

## The instrument as a reusable script — does it generalize?

**Yes, and it is already parameterized for it.** `scripts/a3-vacuity.lean` takes a
comma-separated list of module-name prefixes from `A3_ARGS`:

    scripts/a3-run-lean.sh a3-vacuity ScottDomains.Flat,ScottDomains.Powerdomain     # agent4
    scripts/a3-run-lean.sh a3-vacuity ScottDomains.IdealCompletion,ScottDomains.Thm18 # agent5
    scripts/a3-run-lean.sh a3-vacuity                                                 # whole package

An empty filter means the whole package. Nothing in the instrument is specific to
`Effective/`, `EffectivePresentation`, or this area.

I ran the whole-package pass once so the other streams need not; it costs about
90 seconds. **These are handoff numbers, not my verdict** — the areas are agent4's
and agent5's to rule on, and rows outside my four trees are unexamined by me:

* SECTION 1 (dead binders): **35** package-wide, of which 19 are mine.
  Outside my area: `Audit.Powerdomains.ext_principal_eq`,
  `ClosureProperties.isBifinite_idealCompletion`, `Dyadic.thm27`,
  `IsBifinite.bot_mem_of_normal` (`_h`, an explicit hypothesis — worth a look),
  `PRep.hoareOp_eq`, `PRepFun.domain_range_{smash,strictArrow}Family`,
  `PRepFun.{extendHomP,restrictHomP,smashMap_bot}`,
  `PowerdomainBC.{lem13_hoare,lem13_smyth,instBoundedCompleteHoare}`,
  `Section62.HasGreatestStableNormal`.
* SECTION 2 (statement-invisible data binders of theorems): **21** package-wide,
  3 of them `EffectivePresentation` — the third being
  `EffectivePresentation.countable_compacts` at `EffectivePresentation.lean:88`,
  **agent5's area and the same failure mode as my rows 1–3**. Its own docstring
  concedes the point ("a consistency check on the definition rather than new
  information"); `Domain.countable_compacts` is the unconditional form. The other
  18 are `OrderBot` and `OrderIso` binders, which are ordinary.
* SECTION 4: **0** package-wide, both controls passing.

## Controls — why the zeros are measurements

A zero from a check that silently throws is not a result. Section 4 carries two:

* **positive control** — 459 of 459 instance binders in this area are recovered by
  `synthInstance` *with* the binder in context. The check runs.
* **erased-context control** — after erasing binder `i`, a different instance
  binder still in context is recovered in 426 of 428 attempts. The erasure does
  not break resolution generally; it removes exactly the one binder. (The 2
  failures are where the erased binder is the superclass the other needs.)

So "section 4 found 0" means no instance binder in these 309 declarations is
derivable from its siblings, not that the check failed to run.

## Corrections to the plan and to other streams

1. **The plan's method 1 needs a caveat it does not carry.** "`#lint` carries
   `unusedArguments` … the cheapest complete answer available" — it is cheap and
   it works, but it is **not complete**: the `_`-prefix exemption hides exactly
   the two instances the plan itself names. Any stream that runs `#lint` and
   reports zero has measured nothing about underscore-named binders.
2. **`import ScottDomains` does not import ScottDomains.** Any driver file in
   `scripts/` must generate the 100-line import block. This will silently produce
   "0 declarations" otherwise, which reads like a clean result.
3. **Row 13 is correctly not vacuous, and the plan's reason is the right one.**
   Refined above: it is statement-vacuous but proof-honest, and should keep `S+P`.
4. **agent2 is right about the underscore convention, and this area confirms it
   independently.** `lem17_prod (_h₁ : IsBifinite α) (_h₂ : IsBifinite β)` names
   both hypotheses with a leading underscore and uses both. My instrument flags
   only that theorem's `[Domain α]` and `[Domain β]` and neither `_h₁` nor `_h₂`,
   because it computes occurrence in the proof term and never reads a binder's
   name. The `(underscored)` marker in its output annotates a hit already
   established by occurrence; it never causes one.
5. **The 8 Skeleton rows are a finding this round has no label for.** They are
   over-hypothesized, not vacuous. If `PaperInventory.md` gains a vacuity row it
   should not absorb them; they belong with agent1's `sSup_recoverAt` under
   "hypothesis stronger than the proof needs", which is a defect of statement
   fidelity to the paper rather than of proof strength.

## Reproduction

    scripts/a3-gen.sh                       # regenerate the three driver files from the module tree
    scripts/a3-lint.sh                      # instrument 1: Batteries unusedArguments, whole package
    scripts/a3-run-lean.sh a3-vacuity ScottDomains.Effective,ScottDomains.Kleene,ScottDomains.Isomorphism,ScottDomains.Skeleton
    scripts/a3-run-lean.sh a3-vacuity       # same, whole package
    scripts/a3-run-lean.sh a3-delete        # instrument 2: the four hypothesis-deletion examples
    scripts/a3-run-lean.sh a3-diag          # the environment diagnostic behind finding 2 above

Sources, all in `scripts/`:

| # | File | Role |
| -- | ---- | ---- |
| 1 | `a3-vacuity-body.lean` | the instrument (sections 1–4); **edit this**, not the generated file |
| 2 | `a3-delete-body.lean` | the hypothesis-deletion examples; **edit this** |
| 3 | `a3-gen.sh` | prepends the generated 100-module import block, writing `a3-vacuity.lean`, `a3-delete.lean`, `a3-lint.lean` |
| 4 | `a3-run-lean.sh` | `lake env lean` wrapper; passes its trailing arguments as `A3_ARGS`, logs per the project logging standard |
| 5 | `a3-lint.sh` | instrument 1 runner |
| 6 | `a3-diag.lean` | the environment diagnostic |

Generated files (`a3-vacuity.lean`, `a3-delete.lean`, `a3-lint.lean`) are
committed so a reader can run them without regenerating, and carry a
do-not-edit header. None is part of the lake target.

Logs written this round, under `ScottDomains/logs/`:
`a3-lint-20260808-171603.agent3.log`, `a3-vacuity-20260808-172505.agent3.log`
(area), `a3-vacuity-20260808-172323.agent3.log` (package),
`a3-delete-20260808-172614.agent3.log`, `a3-diag-20260808-171317.agent3.log`.

## Build verification

No `.lean` file in the package was edited; every file added is under `scripts/`
and outside the lake target.

    scripts/counts.sh   → modules 100 · lines 37300 · theorems 1773 · sorry 0
    scripts/compile.sh  → 1339 jobs · 0 lake errors · 0 warnings · sorry 0
                          (logs/compile-20260808-172625.agent3.log)

Both match the plan's required invariants exactly.
