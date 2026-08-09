---
round: r0044
from: agent5
to: orchestrator
subject: vacuity-core
date: 2026-0808-20:40
started: 2026-0808-17:08
finished: 2026-0808-20:40
related:
  - plans/r0044-plan-from-orchestrator-to-orchestrator-specification-defects.md
---

# r0044 Class 2 — the vacuity sweep over `IdealCompletion`, `PropertyM`, `Thm18` and the rest

**Area.** Everything outside agent3's (`Effective/`, `Kleene/`, `Isomorphism/`,
`Skeleton/`) and agent4's (`Flat*`, `Powerdomain*`, `ContinuousAlgebra`,
`Plotkin`): `IdealCompletion`, `Universality`, `RecursiveDomain`, `Morphism`,
`JungCor136`, `PropertyM`, `Iwamura`, `Thm18`, `Closure`, `JungBicomplete`,
`PRep`, `PRepFun`, `PRepSum`, `Dyadic`, `Section62`, `ClosureProperties`,
`Combinator`, `Colimit`, `Atomless`, `JungFinite`, `JungSFP`, `JungNets`,
`SFP`, `Theorem6`, `Projection`, `FinitaryProjection*`, `Bifinite*`,
`EffectivePresentation`.

Both instruments run over the **whole package**, so the package-wide numbers are
reported and then split by area. Nothing outside my area is adjudicated; those
rows are handed to whoever owns them.

## Headline

| # | Question | Answer |
| -- | -------- | -----: |
| 1 | Theorems whose hypotheses the **proof term never mentions** (package) | **18 declarations, 27 binders** |
| 2 | …of those, in agent5's area | **6 declarations, 6 binders** |
| 3 | `Prop` hypotheses that are **used but free** — derivable from the instances the theorem already carries (package) | **14 binders on 12 declarations** |
| 4 | …of those, in agent5's area | **13 binders on 11 declarations** |
| 5 | Adjudicated **vacuous** in agent5's area — establishes nothing, with no compensating unconditional form | **4** |
| 6 | Free-but-**staged** — the unconditional form is a library theorem, so the conditional one is history, not a defect | **8** |
| 7 | **Over-hypothesized** — proves *more* than it claims; opposite sign, not counted as vacuity | **6** |
| 8 | Structures in the package that `Classical.dec` inhabits freely, in agent5's area | **0** |
| 9 | Does Theorem 18's supporting chain survive? | **Yes** — see §6 |

**The single most important number is row 5, and it is 4, not 0.** Three of the
four are one pattern.

## 1. The instruments, and which class each measures

Two defects are being conflated in the round's framing, and they need different
tools. agent1's `Kleene.sSup_recoverAt` is the proof of the distinction: its
`[BoundedComplete β]` **is consumed by the current proof**, and is still
removable, because a different proof does without it.

| # | Class | Definition | Instrument here | Measured? |
| -- | ----- | ---------- | --------------- | --------- |
| 2a | **unused** | the proof term does not mention the binder | `unusedArguments` (`scripts/a5-lint.sh`) | yes, completely |
| 2b-i | **used but free** | binder is consumed, yet derivable from the instances already present | free-hypothesis detector (`scripts/a5-freehyp.lean`) | yes, for package-internal providers |
| 2b-ii | **used but unnecessary** | binder is consumed, and *some other proof* avoids it | reproof only | **no — unmeasured** |

Row 2b-ii is not measured in my area and I make no claim about its size. It is
the class agent1 demonstrated and the class only reproving each declaration can
reach.

### Instrument 1 — `#lint only unusedArguments in ScottDomains`

Works, and is the cheapest complete answer for class 2a. **It does not work out
of the box, and the linter is not at fault.** `ScottDomains.lean`, the package
root, imports five Mathlib modules and none of the development's own 100, so
`import ScottDomains` presents an environment with zero package declarations and
the linter reports

    -- Found 0 errors in 0 declarations (plus 0 automatically generated ones)
       in ScottDomains with 1 linters
    -- All linting checks passed!

— a false pass, recorded in `logs/a5-lint-20260808-171155.agent5.log`. With a
driver that imports all 100 modules by name the same command scans **2609
declarations in about 4 seconds** and reports 18. `scripts/a5-gen-driver.sh`
derives the import block from the file tree so it cannot drift.

What the linter actually tests, from `Batteries/Tactic/Lint/Misc.lean:31`: it
opens the type with `forallTelescope`, applies the stored value — for a
`theorem`, the proof term — to all the binders, appends the conclusion and every
binder's type and let-value, and collects the free variables of that one
expression. A binder whose fvar does not occur is used neither in the proof, nor
in the conclusion, nor in any other hypothesis's type. **That is a proof of
term-level removability, not a heuristic**: the identical term typechecks with
the binder gone, so no rebuild is needed to conclude it.

Two limits, both stated because they change how the number reads:

* It measures class 2a only, per the table above.
* It **exempts binders whose user name is internal**, which includes the
  `_`-prefixed convention (`!ldecl.userName.isInternal`, line 57). `(_h : P)` is
  never reported however dead it is. The exemption makes the linter
  **under-report, never over-report** — so 18 is a lower bound, and the two
  known `_d`/`_e` cases in `Effective/` are invisible to it. It cannot be a
  source of false positives from binder naming, which answers agent2's warning:
  no instrument of mine reads a binder's name.

### Instrument 3 — trivially-inhabited structures

Enumerated from the built environment, not from source text
(`scripts/a5-structures.lean`; output in
`logs/a5-lint-20260808-203620.agent5.log`): the package declares **22**
structures and classes. A column-0 `grep '^structure\|^class'` is not a reliable
census here — ten of its hits are docstring **prose** lines that happen to begin
with the word "structure" — which is why the count is read from the environment. Exactly **one** has `Decidable`-family fields —
`EffectivePresentation`, with `decidableLE` and `decidableNormal`, both
`DecidablePred`, both fillable by `Classical.dec` — and one inherits it,
`Effective.RecursivePresentation`. Both are agent3's.

**In agent5's area the count of `Classical.dec`-inhabitable structures is zero,
and that is a measurement, not an absence of effort**: every structure's field
types were read off the elaborated declaration and inspected. The claim-carrying
`Type`-valued structures in my area are `Combinator.LambdaModel` (an `app`/`lam`
retraction — not free), `FixedPointOperator`, `BifiniteUniversal.MPair` and
`Cpo`; the last three are inhabited, but each is quantified over universally
(`theorem3` says *every* fixed-point operator is Kleene's), which is a statement
about all of them, not a hypothesis that costs nothing.

### Instrument 4 — the free-hypothesis detector (new)

This is the one that finds the `EffectivePresentation` mechanism, and
`unusedArguments` cannot: there the hypothesis **is** used, it is merely free.

Generalized: theorem `T` has an explicit binder `h : P`, and the package contains
a declaration `D` whose conclusion unifies with `P` — by `isDefEq`, **in `T`'s own
local context**, with every remaining metavariable either fixed by that
unification or discharged by `synthInstance` from `T`'s own instances. Then `h`
costs nothing.

Both halves are load-bearing. A first cut matched on head constant alone and
scored **644** hits, because `Flat.instDomain` "provides" `Domain α` by head
symbol while proving it only at `Flat α`. Requiring real unification in the real
context is what makes the test decisive; the count fell to 14.

Two further corrections were needed, and both are worth recording because each
was a silent false negative:

* Restricting providers to those with **zero explicit binders** rejected
  `Effective.nonempty_effectivePresentation`, which takes `α` explicitly — so the
  instrument was **silent on the very structure the plan cites**. Removing the
  restriction and letting unification decide fixed it; a type argument gets
  assigned from the goal, a *proof* argument does not, so the gate is exact.
* `forallTelescopeReducing` **unfolds a `Prop`-valued `def` in a provider's
  conclusion** into further binders, so a provider of
  `FixedPointOfCompactDeflationIsCompact α` presented its unfolded body and never
  matched a binder written at the folded name. Switching to the non-reducing
  telescope surfaced six further hits including the whole `Thm18` family.

`Type`-valued and `Prop`-valued binders are reported separately. `Type` binders
are usually ordinary quantifiers — `idHom` inhabits `ScottHom D D` without making
any statement about Scott-continuous maps vacuous — so of 145 such rows only the
structure-hypothesis ones mean anything; they are listed but not counted.

## 2. Class 2a — the 18, and the 6 that are mine

`logs/a5-lint-20260808-203322.agent5.log`. All 27 flagged binders are
**instance-implicit**; not one is an explicit hypothesis.

Per the standing discipline point, an unused instance binder is **not vacuity**.
The theorem proves *more* than it claims — it holds without the instance — which
is the opposite sign of the defect. Reported as its own category.

| # | Declaration | Unused binder | Verdict |
| -- | ---------- | ------------- | ------- |
| 1 | `ClosureProperties.isBifinite_idealCompletion` | `[Countable P]` | over-hypothesized; deleted and reproved |
| 2 | `Dyadic.thm27` | `[BoundedComplete D]` | **deliberate and documented** — `Dyadic.lean:638` says "Bounded completeness of `D` is not used — it is spent in the hypothesis" |
| 3 | `PRep.hoareOp_eq` | `[Domain D.carrier]` | over-hypothesized, **and it contradicts its own file** — see below |
| 4 | `PRepFun.domain_range_strictArrowFamily` | `[Domain U]` | over-hypothesized; deleted and reproved |
| 5 | `PRepFun.domain_range_smashFamily` | `[Domain U]` | over-hypothesized; deleted and reproved |
| 6 | `Section62.HasGreatestStableNormal` | `[Domain α]` | a `def`, not a theorem; the body uses only `compacts`, `stableCompacts` and `◁`, none of which need `Domain` |

Row 3 is the one worth the orchestrator's attention. `PRep.lean:110–124` argues
at length — and correctly — that `(·)♭` is definable at a bare cpo and that
`[Domain D]` is *not* where the work goes, "spent exactly once, on `Countable A`,
and only to make the *result* a domain". It then states the agreement lemma
`hoareOp_eq` under a `[Domain D.carrier]` it never uses. The statement is weaker
than what the file itself proves, and weaker than what the file's own argument
claims. That is a specification defect of the mild kind, and it is mine.

Row 1 **agrees exactly with agent4's independent finding** on the same
declaration — two instruments, two agents, same binder.

### Deletion probes (class 2a, confirmations)

`scripts/a5-delete.lean`, `logs/a5-lint-20260808-203228.agent5.log`. Four
declarations restated with the flagged binder removed and reproved; all four
kernel-accepted, footprint `[propext, Classical.choice, Quot.sound]`, no
`sorryAx`:

`A5Probe.hoareOp_eq`, `A5Probe.domain_range_smashFamily`,
`A5Probe.domain_range_strictArrowFamily`, `A5Probe.isBifinite_idealCompletion`.

These are confirmations, not discoveries — `unusedArguments`' criterion already
entails them. They are run anyway because a claim about a declaration should be
checked against the kernel.

## 3. Class 2b-i — the 14 free `Prop` hypotheses

`logs/a5-lint-20260808-172257.agent5.log`. Twelve declarations. Every row below
is **kernel-confirmed** by re-deriving the conclusion with the provider supplied
in place of the hypothesis (`scripts/a5-controls.lean`,
`logs/a5-lint-20260808-203240.agent5.log`).

### 3a. Vacuous — count **4**

| # | Declaration | Free hypothesis | Why it is free |
| -- | ---------- | --------------- | -------------- |
| 1 | `EffectivePresentation.countable_compacts` | `(d : EffectivePresentation α)` | `[Domain α]` already gives `Domain.countable_compacts`; `d` buys nothing |
| 2 | `ClosureProperties.lemma17` | `(h₂ : IsBifinite β)` | `prop15` : `[Domain β] [BoundedComplete β] → IsBifinite β` |
| 3 | `ClosureProperties.lem17_strictFun` | `(h₂ : IsBifinite β)` | same |
| 4 | `ClosureProperties.exists_finite_projection_fixing` | `(h₂ : IsBifinite β)` | same |

Row 1 is agent3's handoff lead and it is confirmed. Its **own docstring concedes
it**: "which the `Domain` class already required, so this is a consistency check
on the definition rather than new information." `A5Control.countable_compacts`
re-proves the conclusion from `[Domain α]` alone and **depends on no axioms at
all**.

Rows 2–4 are one pattern, and it is the round's most interesting finding in my
area. Lemma 17's Lean statements carry `[BoundedComplete β]` on the **codomain**,
which the paper's Lemma 17 does not impose. agent2 verified that
`[BoundedComplete β]` is genuinely consumed (`Lemma17.lean:408`) — that is not in
dispute. The consequence is: once `[Domain β] [BoundedComplete β]` are present,
`prop15` makes `IsBifinite β` **free**, so the theorem's second stated hypothesis
establishes nothing. The added instance is a Class-1 `S≠` divergence; its
Class-2 consequence is a redundant hypothesis. Handing the Class-1 half to
agents 1 and 2.

**A fifth instance of the same pattern, `ScottDomains.lem17_fun` at
`Skeleton/Lemma17.lean:403`, is in agent3's area, not mine.** Its `(_h₂ :
IsBifinite β)` is free by the identical route, kernel-confirmed here
(`lem17_fun h₁ prop15` accepted). Note the underscore: agent2 is right that
`_h₂` **is used** (line 423) — used and free are compatible, and this row shows
why the two questions must not be run together. Not counted in my 4.

### 3b. Free but staged — count **8**, not defects

The hypothesis is free, and the library **already carries the unconditional
form**, so the conditional statement records the reduction's history rather than
overstating a result.

| # | Declaration | Free hypothesis | Unconditional form in the library |
| -- | ---------- | --------------- | --------------------------------- |
| 1 | `Dyadic.thm27` | `IsNormallyRepresented ↥(compacts D)` | `Atomless.thm27`, same instances, no hypothesis |
| 2 | `PropertyM.thm18_of_cor136` | `FixedPointOfCompactDeflationIsCompact D` | `ScottDomains.thm18` |
| 3 | `Thm18.thm18_of_thm137Chains_and_cor136` | same | `ScottDomains.thm18` |
| 4 | `Thm18.thm18_of_thm137_and_cor136` | same | `ScottDomains.thm18` |
| 5 | `Thm18.thm18_viaProjections_of_thm137_and_cor136` | same | `ScottDomains.thm18` |
| 6 | `JungFinite.lemma22` | same | — (intermediate step) |
| 7 | `JungFinite.thm18_of_propertyM` | same | — (intermediate step) |
| 8 | `PRepSum.lemma28AtU_of` | 3 of its 5 hypotheses | — (see below) |

`hcor` is free because `JungCor136.fixedPointOfCompactDeflationIsCompact` proves
it from `[IsAlgebraic (ScottHom α α)]`, which `[Domain (ScottHom α α)]` supplies.
That is r0042's result and the development records it at `Skeleton/Section6.lean:199`
("Both are discharged as of r0042").

Row 8 needs a correction to my own instrument's presentation: the detector
flagged three hypotheses, but `PRepSum.lemma28AtU_of` takes **five**. Three —
`→`, `⇸`, `⊗` — are proved outright in `Lemma28AtU` and are free; the remaining
two, the Smyth `♯` and Hoare `♭` conjuncts, are **open**, and they are what keeps
the theorem conditional and honest. Reporting "three free hypotheses" without the
denominator would have been the discovery-count-as-measurement error.

## 4. Class 2b-ii — used but unnecessary: **unmeasured**

No instrument here reaches it, and I do not report a number for it. What can be
said in my area:

* `PropertyM.hasCompleteMub_pair`'s `hAlgF : IsAlgebraic (ScottHom D D)` and
  `hCount : (compacts (ScottHom D D)).Countable` are consumed by the proof
  (instrument 1 clean) and are **not free** (instrument 4 clean, and the negative
  control in §5 shows the binder was tested and rejected, not skipped).
* Whether a *different* proof could avoid them is not measured. For `hCount` the
  development gives a mathematical reason it cannot: `Thm18.lean:47–50` records
  that without countability of `K(D → D)` Theorem 18 is **false**, the algebraic
  L-domains being the counterexamples (Abramsky & Jung 4.3.4 vs 4.3.5). That is
  an argument for necessity, not a measurement, and it is the right kind of
  evidence for this class.

## 5. Controls

A zero is only a measurement if the instrument is shown to fire and to stay
silent. `scripts/a5-controls.lean`, `logs/a5-lint-20260808-203240.agent5.log`.

| # | Control | Expected | Observed |
| -- | ------- | -------- | -------- |
| 1 | **Positive** — instrument 4 recovers the known `EffectivePresentation` case | fires | 14 rows across `Effective/` and `EffectivePresentation`, including both r0038 cases |
| 2 | **Positive** — `EffectivePresentation.countable_compacts` re-derived without `d` | accepted | accepted, **no axioms** |
| 3 | **Positive** — `lem17_fun h₁ prop15` | accepted | accepted |
| 4 | **Positive** — `Dyadic.thm27 D (Atomless.isNormallyRepresented _)` | accepted | accepted |
| 5 | **Positive** — `PropertyM.thm18_of_cor136 JungCor136.fixedPointOfCompactDeflationIsCompact` | accepted | accepted |
| 6 | **Negative** — `PropertyM.hasCompleteMub_pair` with `hAlgF` by `inferInstance` | **must fail** | fails: `failed to synthesize IsAlgebraic (ScottHom D D)` |
| 7 | **Cross-check** — `isBifinite_idealCompletion`'s `[Countable P]` against agent4 | agree | agree |
| 8 | **Coverage** — instrument 4 scanned `PropertyM` | scanned | 1870 non-auto theorems scanned package-wide; 882 explicit binders had a candidate provider and were unified against it |

Control 6 is the one that makes §4's claim a measurement rather than a shrug:
`IsAlgebraic` has eleven hypothesis-free providers in the package, so
`hAlgF` was a **tested** binder that every candidate failed to discharge.

## 6. Does Theorem 18's supporting chain survive? **Yes.**

Read off the built `.olean`, not the source:

    @thm18 : ∀ {α} [CompletePartialOrder α] [Domain α] [Domain (ScottHom α α)], IsBifinite α
    'ScottDomains.thm18' depends on axioms: [propext, Classical.choice, Quot.sound]

No `sorryAx`. `PropertyM.thm18_of_cor136` and
`JungCor136.fixedPointOfCompactDeflationIsCompact` carry the same footprint.

* `PropertyM` — 1008 lines, **zero** class-2a hits and **zero** free `Prop`
  hypotheses other than `thm18_of_cor136`'s `hcor`, which is discharged
  in-library at `Skeleton/Section6.lean:219`. `hAlgF` and `hCount` are load-bearing
  by both instruments and by control 6.
* `Thm18.lean` — its three theorems each carry a free `hcor`, and each is
  strictly subsumed by `ScottDomains.thm18`. Not defects; they are the reduction
  written down. Worth a docstring line saying so, since a reader meeting
  `thm18_of_thm137_and_cor136` first would not know a hypothesis-free form exists
  two files away.
* `IdealCompletion`'s `dite` — the plan's lead. `idealSup` branches on
  `Order.IsIdeal (genIdeal S)` and falls back to `⊥`. **It makes nothing vacuous.**
  The guard is satisfiable and is satisfied where it is used: `isIdeal_sUnion` for
  nonempty directed families, `isIdeal_genIdeal_empty` for `∅`, and
  `isIdeal_genIdeal` under bounded completeness. Every theorem about `idealSup` is
  conditioned on the guard holding rather than being true by the negative branch.
  The negative branch is totality, not a vacuity source. **Negative result,
  reported as a result.**

## 7. Corrections to other streams and to the plan

1. **To the plan.** The plan's Class-2 definition — "a theorem whose hypotheses
   go unused" — merges two defects that need different tools (§1). `#lint` alone
   answers only the first, and the second is where the `EffectivePresentation`
   mechanism actually lives.
2. **To agent3's instrument advice.** Its caveat that `unusedArguments` exempts
   `_`-prefixed binders is right, and the consequence is that the linter
   **under-reports**; it cannot produce a false positive from naming. No
   instrument here reads binder names.
3. **To agent2.** `lem17_fun`'s `_h₂` is used, as agent2 says. It is also
   **free**. Used and free are compatible, and conflating them would have lost the
   pattern in §3a.
4. **To agent4.** Agreement on `isBifinite_idealCompletion`'s `[Countable P]`,
   reached independently.
5. **A row handed back.** `ScottDomains.lem17_fun` (`Skeleton/Lemma17.lean:403`)
   is agent3's area and carries the §3a pattern.

## 8. Reproduction

No `.lean` file in the package was edited. Every driver lives in `scripts/`,
outside `ScottDomains/ScottDomains/`, so `scripts/counts.sh` and `lake build`
never see it.

    scripts/a5-gen-driver.sh scripts/a5-body-lint.lean     scripts/a5-lint-unused.lean
    scripts/a5-gen-driver.sh scripts/a5-body-freehyp.lean  scripts/a5-freehyp.lean
    scripts/a5-gen-driver.sh scripts/a5-body-delete.lean   scripts/a5-delete.lean
    scripts/a5-gen-driver.sh scripts/a5-body-controls.lean scripts/a5-controls.lean
    scripts/a5-gen-driver.sh scripts/a5-body-verify.lean   scripts/a5-verify.lean
    scripts/a5-gen-driver.sh scripts/a5-body-structures.lean scripts/a5-structures.lean

    scripts/a5-lint.sh                             # instrument 1 — 18 hits, exit 1
    scripts/a5-lint.sh scripts/a5-freehyp.lean     # instrument 4 — 14 PROP hits
    scripts/a5-lint.sh scripts/a5-structures.lean  # instrument 3 — 22 structures
    scripts/a5-lint.sh scripts/a5-verify.lean      # elaborated types + axioms
    scripts/a5-lint.sh scripts/a5-delete.lean      # deletion probes — exit 0
    scripts/a5-lint.sh scripts/a5-controls.lean    # controls — exit 1 by design

`scripts/a5-lint.sh` writes `ScottDomains/logs/a5-lint-YYYYMMDD-HHMMSS.agent5.log`
per `LoggingStandard.md`; the role slot comes from the worktree path.

## 9. Tree unchanged

    scripts/counts.sh    modules: 100 · lines: 37300 · theorems: 1773 · sorry: 0
    scripts/compile.sh   jobs 1339 · diagnostics 0 · lake errors 0 · sorry 0 · other warnings 0
