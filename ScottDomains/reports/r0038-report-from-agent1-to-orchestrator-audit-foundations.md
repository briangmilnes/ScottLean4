---
round: r0038
from: agent1
to: orchestrator
subject: audit-foundations
date: 2026-0808-09:54
started: 2026-0808-08:52
finished: 2026-0808-09:54
related:
  - plans/r0038-plan-from-orchestrator-to-orchestrator-theorem-audit.md
  - docs/PropertiesVsTheorems.md
  - docs/PaperInventory.md
---

# r0038 — `Audit.Foundations`: 123 declarations classified

## 1. What was counted, and the two numbers that differ from the plan

`scripts/module-counts.sh` reports **123** theorem-ish declarations across the
nineteen modules of this stream, not the plan's estimate of ~131. The counting
rule is `counts.sh`'s, so this number sums into the development total.

| # | Module | Lines | Declarations counted | Live | Commented out (r0020) |
| -- | ------ | ----- | -------------------- | ---- | --------------------- |
| 1 | `WayBelow.lean` | 117 | 7 | 7 | 0 |
| 2 | `Domain.lean` | 227 | 13 | 11 | 2 |
| 3 | `Powerset.lean` | 110 | 2 | 2 | 0 |
| 4 | `ScottHom.lean` | 304 | 16 | 14 | 2 |
| 5 | `StepFunction.lean` | 156 | 10 | 9 | 1 |
| 6 | `FunctionSpaceDomain.lean` | 129 | 3 | 3 | 0 |
| 7 | `CompactFunction.lean` | 156 | 7 | 7 | 0 |
| 8 | `FunctionSpaceCountable.lean` | 142 | 5 | 5 | 0 |
| 9 | `Product.lean` | 119 | 2 | 2 | 0 |
| 10 | `Currying.lean` | 150 | 1 | 1 | 0 |
| 11 | `Lift.lean` | 100 | 4 | 4 | 0 |
| 12 | `StrictHom.lean` | 103 | 3 | 3 | 0 |
| 13 | `Smash.lean` | 199 | 8 | 8 | 0 |
| 14 | `CoalescedSum.lean` | 438 | 19 | 19 | 0 |
| 15 | `FixedPoint.lean` | 117 | 10 | 10 | 0 |
| 16 | `UniformFixedPoint.lean` | 175 | 5 | 5 | 0 |
| 17 | `EffectivePresentation.lean` | 100 | 3 | 3 | 0 |
| 18 | `ComputableFunction.lean` | 158 | 5 | 5 | 0 |
| 19 | `ExistingTheories.lean` | 28 | 0 | 0 | 0 |
| — | **total** | **3028** | **123** | **118** | **5** |

**`module-counts.sh` counts declarations inside block comments.** r0020 commented
out six declarations in place; five of them are in this stream, and each still
begins a line with `theorem` or `@[simp] theorem`, so the script's regular
expression matches them. The `simp` column has the same defect: `ScottHom.lean`
is reported as carrying two `@[simp]` lemmas and **both are commented out**, so
the module has zero live `simp` lemmas. Of the 10 `@[simp]` declarations the
script attributes to this stream, **7 are live and 3 are inside comments**.

The five are listed once here and excluded from the six-label totals, because
they are not declarations:

| # | Declaration | Module:line | `@[simp]` | Why r0020 retired it |
| -- | ---------- | ----------- | --------- | -------------------- |
| 1 | `mem_compacts` | `Domain.lean:67` | yes | `compacts` is only ever used as a set, never unfolded |
| 2 | `sSup_compactsBelow` | `Domain.lean:144` | no | every proof works with `IsLUB`, which needs no `SupSet` |
| 3 | `toFun_eq_coe` | `ScottHom.lean:94` | yes | nothing touches `.toFun`; every proof goes through the coercion |
| 4 | `coe_const` | `ScottHom.lean:113` | yes | `const` is used as a term, never rewritten through this equation |
| 5 | `step_mono` | `StepFunction.lean:129` | no | every use goes through `step_le_iff`, which is more general |

## 2. How each label was decided

- **`P`** — checked against the rendered PDF (`scripts/pdf-section.sh` over
  `ScottDomains/papers/Gunter Scott 1990.pdf`), not against the docstring or
  `PaperInventory.md`. Section 3 below records three places where the check
  changed the answer.
- **`S`** — measured by `scripts/agent1-citations.sh` (added this round), which
  reports for every declaration in the stream its total whole-word occurrence
  count, its in-file uses, its out-of-file uses, and the citing files. Names
  whose final component collides across namespaces (`le`, `trans`, `ext`,
  `monotone`, `scottContinuous`, `countable_compacts`) were re-measured with a
  namespace-qualified `grep`; every one of them was over-reported, and two of
  them turned out to be uncited.
- **`A`** — a declaration whose content is a projection, a coercion equation, an
  extensionality lemma, or the defining equation of an `if`/`dite` with the case
  split discharged. **Tie-break:** where a declaration is both API-shaped and
  cited, `A` wins over `S`, because `A` is the more specific description; the
  citing site is still named in the evidence column so nothing is lost. Class
  field *unbundlers* (`Domain.isLUB_sSup_of_bddAbove`) are counted `S`, not `A`:
  they carry a mathematical fact rather than a rewrite equation.
- **`U`** — zero occurrences anywhere in the tree except the declaration itself
  and, in several cases, a module docstring naming it in prose. Docstring
  mentions were read individually and do not count as citations.
- **`D`** — kernel-checked. `ScottDomains/Audit/Foundations.lean` (added this
  round, imported by nothing) derives each duplicate from the general form by
  application alone, and discharges one pair by `Iff.rfl`.
- **`W`** — no row in this stream earns it; section 6 gives the near misses and
  says why each falls short.

## 3. Three corrections to the paper-property baseline

These are the results of checking `P` claims against the paper rather than
accepting them, and they move `docs/PropertiesVsTheorems.md` §1's total.

**3.1 `PaperInventory.md`'s prose claim 8 is not a claim the paper makes.**
Row 8 of the twelve unnumbered prose claims reads "every compact function is a
*finite* join of step functions | Thm 7 proof, implicit". The proof's full text
on printed page 12 is: "These are called step functions and it is possible to
show that they form a basis for `D → E`. The proof that the poset of step
functions has decidable ordering and finite normal subposets is tedious, but not
difficult…". There is no finiteness claim about the join. The finiteness is what
"basis" has to mean for the countability argument to run, but the paper does not
say it, and the row's own word "implicit" concedes as much.
`exists_finite_isLUB_of_isCompactElement` is therefore labelled `S` here, not
`P`. **Prose claims: 12 → 11.**

**3.2 §4.1 states two prose claims the inventory does not list.** Printed page
12, immediately before the cpo conclusion: "If a subset `L ⊆ D × E` is directed,
then `M = fst(L) = {x | ∃y ∈ E. (x, y) ∈ L}` and `N = snd(L) = {y | ∃x ∈ D. (x, y)
∈ L}` are directed." That is two atomic assertions, and they are
`Product.directedOn_fst_image` and `Product.directedOn_snd_image` verbatim. Both
are labelled `P`. **Prose claims: 11 → 13.**

Net effect on `PropertiesVsTheorems.md` §1 row 20: **12 → 13**, and the paper
property total **99 → 100**.

**3.3 The paper does not define the way-below relation.** `PaperInventory.md`
line 474 records "3.1 | Def | — | **way-below** `≪` … ✓ `ScottDomains.WayBelow`".
`scripts/pdf-find-page.sh` over the whole PDF returns **zero pages** containing
the string "way below", and printed pages 8–9 — where §3 introduces finite
approximation — define *compact element* and nothing else. `WayBelow.lean` is
entirely the formalization's own scaffolding. That is not a defect (the module
docstring says so, and `wayBelow_self_iff_isCompactElement` being `Iff.rfl` is
the payoff), but the inventory row overstates the paper.

**3.4 Theorem 7 has three sentences and only the first is formalized.** The
printed statement is: "**Theorem 7** If `D` and `E` are bounded complete domains,
then `D → E` is also a bounded complete domain. **Moreover, if `D` and `E` have
effective presentations, then `D → E` has an effective presentation as well.
Similar facts hold for `D →⊥ E`.**" `isBoundedCompleteDomain_scottHom` proves the
first sentence. The second and third are formalized nowhere. This is the
explanation for the largest `U` cluster in the stream — see section 5.3.

## 4. The table — one row per declaration

Evidence names a file and, where it exists, a line. "own" = a citing site inside
the declaring file; "extern" = outside it.

### 4.1 `WayBelow.lean` (7)

| # | Declaration | Module | Label | Evidence |
| -- | ---------- | ------ | ----- | -------- |
| 1 | `WayBelow.le` | `WayBelow.lean` | S | cited by `WayBelow.trans` at `WayBelow.lean:83` (`hxy.le`). Not `P`: "way below" occurs on 0 pages of the paper (§3.3) |
| 2 | `LE.le.trans_wayBelow` | `WayBelow.lean` | S | cited by `WayBelow.trans` (`:83`) and `Domain.wayBelow_of_isCompactElement` (`Domain.lean:78`) |
| 3 | `WayBelow.trans_le` | `WayBelow.lean` | S | cited by `Domain.wayBelow_of_isCompactElement` (`Domain.lean:79`). The 12 apparent externs are `trans_le` collisions |
| 4 | `WayBelow.trans` | `WayBelow.lean` | **U** | qualified `grep` for `WayBelow.trans` finds only the declaration and its own docstring. The 215 apparent externs are `.trans` collisions. Written to complete the `≪` order calculus; no proof ever chains two `≪`s |
| 5 | `bot_wayBelow` | `WayBelow.lean` | S | cited by `Domain.isCompactElement_bot` (`Domain.lean:105`) |
| 6 | `wayBelow_self_iff_isCompactElement` | `WayBelow.lean` | S | cited by `Domain.wayBelow_of_isCompactElement` (`:79`) and `Domain.isCompactElement_bot` (`:105`). The module's `Iff.rfl` payoff |
| 7 | `wayBelow_iff_sSup` | `WayBelow.lean` | **U** | total occurrences 2: the declaration and `WayBelow.lean:27`'s docstring. Written "for use downstream"; no downstream appeared |

### 4.2 `Domain.lean` (11 live)

| # | Declaration | Module | Label | Evidence |
| -- | ---------- | ------ | ----- | -------- |
| 8 | `mem_compactsBelow` | `Domain.lean` | A | `@[simp]`; `Iff.rfl` membership unfolding. Named at `Domain.lean:158`, `Powerdomain/Universal.lean` |
| 9 | `wayBelow_of_isCompactElement` | `Domain.lean` | S | cited by `wayBelow_iff_exists_compact` (`Domain.lean:161`) — its only consumer, itself a `U` (row 14) |
| 10 | `isCompactElement_of_isLUB_pair` | `Domain.lean` | S | 15 external citers, e.g. `FunctionSpaceDomain.lean:76`, `Powerdomain/BoundedComplete.lean:236`, `Section62.lean` |
| 11 | `isCompactElement_bot` | `Domain.lean` | S | 25 external citers, e.g. `IdealCompletion.lean:474`, `SFP.lean:437`, `JungFinite.lean:219` |
| 12 | `bot_mem_compactsBelow` | `Domain.lean` | S | cited by `compactsBelow_nonempty` (`:113`), `PRepFun.lean:934`, `PRepSum.lean:351` |
| 13 | `compactsBelow_nonempty` | `Domain.lean` | S | 13 external citers, e.g. `FunctionSpaceDomain.lean:103`, `JungSFP.lean:149`, `ContinuousAlgebra.lean:937` |
| 14 | `wayBelow_iff_exists_compact` | `Domain.lean` | **U** | total occurrences 2: the declaration and `Domain.lean:74`'s docstring. The characterization of `≪` in an algebraic cpo; nothing in the development ever needs `≪` (§3.3) |
| 15 | `isLUB_sSup_of_bddAbove` | `Domain.lean` | S | unbundles the `BoundedComplete` field; 36 external citers, e.g. `CompactFunction.lean:97`, `FunctionSpaceDomain.lean:74`, `Skeleton/Lemma10.lean:80` |
| 16 | `exists_isLUB_of_bddAbove` | `Domain.lean` | **U** | total occurrences 2: the declaration and `Domain.lean:42`'s docstring. Written "for readers checking the class against the paper's English" — it restates §3.2's *definition* of bounded complete, and definitions are excluded from the property count |
| 17 | `isAlgebraic_of_forall_isCompactElement` | `Domain.lean` | S | cited by `instance : Domain Prop` (`:221`), `FinitaryProjectionEmbedding.lean:159`, `SFP.lean:226` |
| 18 | `isCompactElement_prop` | `Domain.lean` | S | cited by `instance : Domain Prop` (`Domain.lean:221`) |

### 4.3 `Powerset.lean` (2)

| # | Declaration | Module | Label | Evidence |
| -- | ---------- | ------ | ----- | -------- |
| 19 | `isCompactElement_iff_finite` | `Powerset.lean` | **P** | §3, printed p. 9: "the collection `P N` of subsets of `N`, ordered by subset inclusion is a domain whose compact elements are just the finite subsets of `N`." Prose claim 1 of the inventory's list; verified against the PDF. Also cited 4× externally (`Powerdomain/Plotkin.lean:316`) |
| 20 | `compacts_set_eq` | `Powerset.lean` | A | `@[simp]`; set-level restatement of row 19. Cited by `instance [Countable X] : Domain (Set X)` (`Powerset.lean:89`) |

### 4.4 `ScottHom.lean` (14 live)

| # | Declaration | Module | Label | Evidence |
| -- | ---------- | ------ | ----- | -------- |
| 21 | `ext` | `ScottHom.lean` | A | `@[ext]`, not `@[simp]`; 20 qualified citers, e.g. `ClosureProperties/StrictFunction.lean:146`, `PRepFun.lean:226`, `UniversalDomain.lean:665` |
| 22 | `scottContinuous` | `ScottHom.lean` | A | projection of the structure field through `FunLike`; e.g. `FunctionSpaceDomain.lean:103`, `Currying.lean:96` |
| 23 | `monotone` | `ScottHom.lean` | A | projection; e.g. `Currying.lean:73`, `StepFunction.lean:117` |
| 24 | `le_def` | `ScottHom.lean` | A | defining equation of the pointwise order; `SFP.lean:459`, `Skeleton/Lemma17.lean:444`, `ClosureProperties/StrictFunction.lean:292` |
| 25 | `directedOn_eval_image` | `ScottHom.lean` | S | 12 external citers, e.g. `StepFunction.lean:146`, `PRep.lean`, `Section62.lean` |
| 26 | `bddAbove_eval_image` | `ScottHom.lean` | S | cited by `scottContinuous_pointwiseSup_of_bddAbove` (`:190`) and the `BoundedComplete` instance (`:292`, `:296`) |
| 27 | `scottContinuous_pointwiseSup_of_forall_isLUB` | `ScottHom.lean` | S | cited by `:182`, `:189`, and `UniversalDomain.lean:407` — three genuinely different instantiations, so the generality is consumed |
| 28 | `scottContinuous_pointwiseSup` | `ScottHom.lean` | S | cited by `coe_sSup_of_directed` (`ScottHom.lean:228`) |
| 29 | `scottContinuous_pointwiseSup_of_bddAbove` | `ScottHom.lean` | S | cited by `coe_sSup_of_bddAbove` (`ScottHom.lean:234`) |
| 30 | `coe_sSup_of_continuous` | `ScottHom.lean` | A | the `dite` positive branch discharged; `:228`, `:234`, `StrictHom.lean:69`, `UniversalDomain.lean` |
| 31 | `sSup_eq_const_bot` | `ScottHom.lean` | A | the `dite` negative branch; cited by `StrictHom.isStrict_sSup` (`StrictHom.lean:74`) |
| 32 | `coe_sSup_of_directed` | `ScottHom.lean` | A | defining equation; 8 external citers, e.g. `StepFunction.lean:145`, `Skeleton/Section6.lean` |
| 33 | `coe_sSup_of_bddAbove` | `ScottHom.lean` | A | defining equation; cited by the `BoundedComplete` instance (`:291`, `:295`) |
| 34 | `isLUB_eval_image_of_isLUB` | `ScottHom.lean` | S | 25 external citers, e.g. `Currying.lean:122`, `CombinatorRep.lean`, `Combinator.lean` |

### 4.5 `StepFunction.lean` (9 live)

| # | Declaration | Module | Label | Evidence |
| -- | ---------- | ------ | ----- | -------- |
| 35 | `stepFun_of_le` | `StepFunction.lean` | A | `if` positive branch; 6 external citers, e.g. `FunctionSpaceDomain.lean:113`, `CompactFunction.lean:133` |
| 36 | `stepFun_of_not_le` | `StepFunction.lean` | A | `if` negative branch; `ClosureProperties/StrictFunction.lean`, `Skeleton/Lemma17.lean` |
| 37 | `stepFun_self` | `StepFunction.lean` | A | `@[simp]`; cited by `step_self` (`:100`) and `step_le_iff` (`:111`) |
| 38 | `monotone_stepFun` | `StepFunction.lean` | S | cited by `scottContinuous_stepFun` (`StepFunction.lean:80`) |
| 39 | `scottContinuous_stepFun` | `StepFunction.lean` | **P** | Theorem 7's proof, printed p. 12: "the function `step(s) : D → E` given by `step(s)(x) = ⨆{s(y) | y ∈ N ∩ ↓x}` is continuous". **Caveat:** proved only at `N = {k}`; the paper's `step(s)` ranges over finite `N` with monotone `s : N → K(E)`. One instance of the claim, not the claim |
| 40 | `coe_step` | `StepFunction.lean` | A | `@[simp]` coercion equation; `CompactFunction.lean:133`, `FunctionSpaceDomain.lean:113` |
| 41 | `step_self` | `StepFunction.lean` | A | `@[simp]`; **its only named occurrence outside the declaration is inside r0020's commented-out `step_mono`** (`StepFunction.lean:131`). No live citer; whether the tag fires is unmeasured |
| 42 | `step_le_iff` | `StepFunction.lean` | S | the adjunction, and the module's stated workhorse; 9 external citers, e.g. `FunctionSpaceDomain.lean:110`, `ContinuousConstruction.lean`, `JungSFP.lean` |
| 43 | `isCompactElement_step` | `StepFunction.lean` | **P** | Theorem 7's proof, printed p. 12: "… and compact in the ordering on `D → E`". Same singleton caveat as row 39. Also cited 6× externally |

### 4.6 `FunctionSpaceDomain.lean` (3)

| # | Declaration | Module | Label | Evidence |
| -- | ---------- | ------ | ----- | -------- |
| 44 | `directedOn_image` | `FunctionSpaceDomain.lean` | S | 5 external citers, e.g. `CompactFunction.lean:126`, `PRepFun.lean`, `ContinuousConstruction.lean` |
| 45 | `directedOn_compactsBelow_scottHom` | `FunctionSpaceDomain.lean` | S | cited by `instance : IsAlgebraic (ScottHom α β)` (`:122`). Half of prose claim 7; the claim is carried by the instance, which is not a theorem |
| 46 | `isLUB_compactsBelow_scottHom` | `FunctionSpaceDomain.lean` | S | cited by `instance : IsAlgebraic (ScottHom α β)` (`:123`) and named in `CompactFunction.lean:22,114` prose. The other half of prose claim 7 |

### 4.7 `CompactFunction.lean` (7)

| # | Declaration | Module | Label | Evidence |
| -- | ---------- | ------ | ----- | -------- |
| 47 | `le_of_mem_stepsBelow` | `CompactFunction.lean` | S | cited `:70`, `:95`, `:96` |
| 48 | `le_of_mem_finiteJoinsBelow` | `CompactFunction.lean` | S | cited by `isLUB_finiteJoinsBelow` (`:116`) and `exists_finite_isLUB_of_isCompactElement` (`:149`) |
| 49 | `bot_mem_finiteJoinsBelow` | `CompactFunction.lean` | S | cited by `finiteJoinsBelow_nonempty` (`:78`) |
| 50 | `finiteJoinsBelow_nonempty` | `CompactFunction.lean` | S | cited by `exists_finite_isLUB_of_isCompactElement` (`:146`) |
| 51 | `directedOn_finiteJoinsBelow` | `CompactFunction.lean` | S | cited by `exists_finite_isLUB_of_isCompactElement` (`:147`) |
| 52 | `isLUB_finiteJoinsBelow` | `CompactFunction.lean` | S | cited by `exists_finite_isLUB_of_isCompactElement` (`:147`) |
| 53 | `exists_finite_isLUB_of_isCompactElement` | `CompactFunction.lean` | S | cited by `FunctionSpaceCountable.exists_ofPairs_of_isCompactElement` (`FunctionSpaceCountable.lean:95`), `Skeleton/Lemma17.lean`, `ClosureProperties/StrictFunction.lean`. **Not `P`** — see §3.1: the paper makes no finiteness claim |

### 4.8 `FunctionSpaceCountable.lean` (5)

| # | Declaration | Module | Label | Evidence |
| -- | ---------- | ------ | ----- | -------- |
| 54 | `isStepPair_stepPairOf` | `FunctionSpaceCountable.lean` | S | cited `:79`, `:83`, `:98` |
| 55 | `stepsOf_image_stepPairOf` | `FunctionSpaceCountable.lean` | S | cited by `exists_ofPairs_of_isCompactElement` (`:100`) |
| 56 | `exists_ofPairs_of_isCompactElement` | `FunctionSpaceCountable.lean` | S | cited by `countable_compacts_scottHom` (`:118`) |
| 57 | `countable_compacts_scottHom` | `FunctionSpaceCountable.lean` | **P** | Theorem 7's countable-basis conjunct: §3 defines *domain* as an algebraic cpo with `K(D)` countable, and Theorem 7 concludes "bounded complete domain". Cited by `instance : Domain (ScottHom α β)` (`:124`) |
| 58 | `isBoundedCompleteDomain_scottHom` | `FunctionSpaceCountable.lean` | **P** | **Theorem 7**, printed p. 12, first sentence verbatim. Terminal by design — total occurrences 2, the second being `FunctionSpaceCountable.lean:35`'s docstring. Two measured gaps: proved under weaker hypotheses than the paper states (bounded completeness of `D` is never used), and Theorem 7's second and third sentences are formalized nowhere (§3.4) |

### 4.9 `Product.lean` (2)

| # | Declaration | Module | Label | Evidence |
| -- | ---------- | ------ | ----- | -------- |
| 59 | `directedOn_fst_image` | `Product.lean` | **P** | §4.1, printed p. 12 verbatim: "If a subset `L ⊆ D × E` is directed, then `M = fst(L) = {x | ∃y ∈ E. (x,y) ∈ L}` … [is] directed." A prose claim `PaperInventory.md` does not list (§3.2). Also cited by `Currying.lean:108`, `Skeleton/Lemma17.lean`, `ContinuousAlgebra.lean` |
| 60 | `directedOn_snd_image` | `Product.lean` | **P** | the `N = snd(L)` half of the same sentence. Also cited by `Currying.lean:109` and the same three modules |

### 4.10 `Currying.lean` (1)

| # | Declaration | Module | Label | Evidence |
| -- | ---------- | ------ | ----- | -------- |
| 61 | `scottContinuous_pairLeft` | `Currying.lean` | S | cited by `ScottHom.curryApply` (`Currying.lean:63`) and `Universality.lean`. Related to §4.1's "f is continuous iff continuous in each argument individually", which the paper leaves as an exercise, but states the tool rather than the claim. Lemma 8.4 itself is `scottHomCurry`, a `def`, so it carries no row here |

### 4.11 `Lift.lean` (4)

| # | Declaration | Module | Label | Evidence |
| -- | ---------- | ------ | ----- | -------- |
| 62 | `coe_mem_of_mem_liftBase` | `Lift.lean` | S | 10 external citers, e.g. `Skeleton/Lemma10.lean`, `Isomorphism/Lift.lean`, `CombinatorRep.lean`. The earliest (r0023) of a triplicated statement — see rows 69, 77 |
| 63 | `directedOn_liftBase` | `Lift.lean` | S | cited `:79` and `Skeleton/Lemma17.lean`, `Isomorphism/Lift.lean`, `CombinatorRep.lean`. Earliest of a triplicated statement — see rows 70, 78 |
| 64 | `liftSup_of_nonempty` | `Lift.lean` | A | `if` positive branch; cited `:81`, `Skeleton/Lemma10.lean:187` |
| 65 | `liftSup_of_empty` | `Lift.lean` | A | `if` negative branch; cited `:91`, `Skeleton/Lemma10.lean` |

### 4.12 `StrictHom.lean` (3)

| # | Declaration | Module | Label | Evidence |
| -- | ---------- | ------ | ----- | -------- |
| 66 | `sSup_eq_bot_of_forall_eq_bot` | `StrictHom.lean` | S | cited by `isStrict_sSup` (`StrictHom.lean:70`). Strictly subsumes `CoalescedSum.sSup_empty_eq_bot` (row 84) |
| 67 | `isStrict_const_bot` | `StrictHom.lean` | S | cited by `strictHomCpo` (`:82`) |
| 68 | `isStrict_sSup` | `StrictHom.lean` | S | cited by `strictHomCpo` (`:81`) and `Skeleton/Lemma10.lean`. The mathematical content of §2.1's "the poset of strict continuous functions `D →⊥ E` is also a cpo" (prose claim 12), which is carried by the instance, not by a theorem |

### 4.13 `Smash.lean` (8)

| # | Declaration | Module | Label | Evidence |
| -- | ---------- | ------ | ----- | -------- |
| 69 | `coe_mem_of_mem_smashBase` | `Smash.lean` | **D** | duplicate of `Lift.coe_mem_of_mem_liftBase` (row 62) at `γ := NonBotPair α β`. Kernel evidence: `Audit/Foundations.lean` derives this statement from `coe_mem_withBotBase` by application alone. Cited 8× externally, so retiring it means replacing all six copies by one general lemma, not deleting it |
| 70 | `directedOn_smashBase` | `Smash.lean` | **D** | duplicate of `Lift.directedOn_liftBase` (row 63) at `γ := NonBotPair α β`; same kernel evidence. The proof script is `directedOn_liftBase`'s, verbatim. Cited by `PRepFun.lean`, `Skeleton/Sum.lean` |
| 71 | `directedOn_val_smashBase` | `Smash.lean` | **D** | duplicate of `UniformFixedPoint.directedOn_val_image_subtype` (row 106) at `p := fun p : α × β => p.1 ≠ ⊥ ∧ p.2 ≠ ⊥`. Kernel evidence: `Audit/Foundations.lean` closes it with `directedOn_val_image_subtype ht`. The two modules are in disjoint import cones, which is why neither cites the other |
| 72 | `sSup_ne_bot_of_nonempty` | `Smash.lean` | S | cited by `smashSup_of_directed` (`:137`, `:139`) |
| 73 | `smashSup_of_ne_bot` | `Smash.lean` | A | `dite` positive branch; cited `:139`, `Skeleton/Lemma10.lean` |
| 74 | `smashSup_of_directed` | `Smash.lean` | S | r0027's compatibility statement; cited by `smashCpo` (`:169`), `Skeleton/Lemma10.lean`, `PRepFun.lean` |
| 75 | `sSup_val_smashBase_eq_bot` | `Smash.lean` | S | cited by `smashSup_of_empty` (`:157`). Its three-line proof repeats `CoalescedSum.sSup_empty_eq_bot`'s (row 84); `Set.image_empty ▸ sSup_empty_eq_bot` would serve |
| 76 | `smashSup_of_empty` | `Smash.lean` | A | `dite` negative branch; cited `:190`, `Skeleton/Lemma10.lean` |

### 4.14 `CoalescedSum.lean` (19)

| # | Declaration | Module | Label | Evidence |
| -- | ---------- | ------ | ----- | -------- |
| 77 | `coe_mem_of_mem_sumBase` | `CoalescedSum.lean` | **D** | duplicate of `Lift.coe_mem_of_mem_liftBase` (row 62) at `γ := NonBotSum α β`; kernel evidence in `Audit/Foundations.lean`. Cited 12× externally |
| 78 | `directedOn_sumBase` | `CoalescedSum.lean` | **D** | duplicate of `Lift.directedOn_liftBase` (row 63) at `γ := NonBotSum α β`; same kernel evidence. Cited by `Isomorphism/Copair.lean`, `Skeleton/Sum.lean` |
| 79 | `sameSide_of_directedOn` | `CoalescedSum.lean` | S | cited by `sumCpo` (`:423`, `:431`) |
| 80 | `directedOn_leftParts` | `CoalescedSum.lean` | S | cited `:197`, `:427`, and `Skeleton/Sum.lean` |
| 81 | `directedOn_rightParts` | `CoalescedSum.lean` | S | cited `:207`, `:435`, and `Skeleton/Sum.lean` |
| 82 | `sSup_leftParts_ne_bot` | `CoalescedSum.lean` | **U** | total occurrences 1 — the declaration. `isLUB_sumSup_left` proves the same non-bottomness inline at `:319` from the `IsLUB` hypothesis, which needs no directedness. Written as part of the "base is closed under nonempty directed suprema" pair the module docstring announces |
| 83 | `sSup_rightParts_ne_bot` | `CoalescedSum.lean` | **U** | total occurrences 1. Mirror of row 82; `isLUB_sumSup_right` inlines it at `:372` |
| 84 | `sSup_empty_eq_bot` | `CoalescedSum.lean` | S | cited by `sumCandidate_of_empty_base` (`:274`). Strictly subsumed by `StrictHom.sSup_eq_bot_of_forall_eq_bot` (row 66), whose hypothesis is vacuous on `∅`; the two modules are in disjoint import cones |
| 85 | `leftParts_empty` | `CoalescedSum.lean` | A | `@[simp]`; cited by `sumCandidate_of_empty_base` (`:274`) |
| 86 | `rightParts_empty` | `CoalescedSum.lean` | A | `@[simp]`; cited by `sumCandidate_of_empty_base` (`:272`) |
| 87 | `sumCandidate_of_right` | `CoalescedSum.lean` | A | `if` positive branch; cited by `isLUB_sumSup_right` (`:369`) |
| 88 | `sumCandidate_of_left` | `CoalescedSum.lean` | A | `if` negative branch; cited `:274`, `:316` |
| 89 | `sumSup_of_isNonBotSum` | `CoalescedSum.lean` | A | `dite` positive branch; cited `:320`, `:373` |
| 90 | `sumSup_of_not_isNonBotSum` | `CoalescedSum.lean` | A | `dite` negative branch; cited by `sumSup_of_empty` (`:278`) |
| 91 | `sumCandidate_of_empty_base` | `CoalescedSum.lean` | S | cited by `sumSup_of_empty` (`:279`) |
| 92 | `sumSup_of_empty` | `CoalescedSum.lean` | S | cited by `isLUB_sumSup_of_empty_base` (`:286`) |
| 93 | `isLUB_sumSup_of_empty_base` | `CoalescedSum.lean` | S | cited by `sumCpo` (`:436`) and `Skeleton/Sum.lean` |
| 94 | `isLUB_sumSup_left` | `CoalescedSum.lean` | S | cited by `sumCpo` (`:427`) and `Skeleton/Sum.lean:152`, where Lemma 10's sum conjunct `lem10_sum` consumes it at bounded-completeness strength |
| 95 | `isLUB_sumSup_right` | `CoalescedSum.lean` | S | cited by `sumCpo` (`:435`) and `Skeleton/Sum.lean:164` |

### 4.15 `FixedPoint.lean` (10)

| # | Declaration | Module | Label | Evidence |
| -- | ---------- | ------ | ----- | -------- |
| 96 | `mem_kleeneChain` | `FixedPoint.lean` | S | cited `:45`, `:61`, `:68`, `:89` |
| 97 | `kleeneChain_nonempty` | `FixedPoint.lean` | S | cited by `map_kleeneFix` (`:76`) |
| 98 | `monotone_iterate_bot` | `FixedPoint.lean` | S | cited by `directedOn_kleeneChain` (`:61`, `:62`). Is the paper's own proof step ("By an induction on `n` using the monotonicity of `f` … `fⁿ(⊥) ⊑ fⁿ⁺¹(⊥)`"), but a proof step is not a property |
| 99 | `directedOn_kleeneChain` | `FixedPoint.lean` | S | cited `:68`, `:75`, `:102` |
| 100 | `le_kleeneFix` | `FixedPoint.lean` | S | cited by `map_kleeneFix` (`:81`) |
| 101 | `map_kleeneFix` | `FixedPoint.lean` | S | cited `:109`, `:115`, and `UniformFixedPoint.lean:123,133`, `Combinator.lean`, `RecursiveDomain.lean` |
| 102 | `iterate_bot_le` | `FixedPoint.lean` | S | cited by `kleeneFix_le` (`:104`). The paper's own proof step ("for each `n`, `fⁿ(⊥) ⊑ fⁿ(x) = x`") |
| 103 | `kleeneFix_le` | `FixedPoint.lean` | S | cited `:109`, `:115` |
| 104 | `theorem1` | `FixedPoint.lean` | **P** | **Theorem 1 (Fixed Point)**, §2.1, printed p. 4 verbatim: "there is a point `fix(f) ∈ D` such that `fix(f) = f(fix(f))` and `fix(f) ⊑ x` for any `x ∈ D` such that `x = f(x)`." Rendered `IsLeast {a | f a = a} (kleeneFix f)`. Cited by `theorem3` (`UniformFixedPoint.lean:166`) |
| 105 | `isLeast_kleeneFix_le` | `FixedPoint.lean` | **U** | total occurrences 1. Docstring: "The same statement for pre-fixed points, which is what recursion arguments usually need." No such recursion argument appeared in eight rounds since r0017 |

### 4.16 `UniformFixedPoint.lean` (5)

| # | Declaration | Module | Label | Evidence |
| -- | ---------- | ------ | ----- | -------- |
| 106 | `directedOn_val_image_subtype` | `UniformFixedPoint.lean` | S | cited `:66`, `:94`, `:98`, `:141`, `:148`. The general form of `Smash.directedOn_val_smashBase` (row 71); the generality over the predicate `p` is not exercised anywhere in this module |
| 107 | `sSup_val_image_le` | `UniformFixedPoint.lean` | S | cited `:93`, `:140` |
| 108 | `coe_IicSup_of_le` | `UniformFixedPoint.lean` | A | `dite` positive branch of `IicSup`; cited `:93`, `:97`, `:140` |
| 109 | `theorem3` | `UniformFixedPoint.lean` | **P** | **Theorem 3**, §2.3, printed p. 7 verbatim: "`fix` is the unique uniform fixed point operator." Cited by `eq_kleeneOperator_op` (`:173`) |
| 110 | `eq_kleeneOperator_op` | `UniformFixedPoint.lean` | **D** | duplicate of `theorem3` (row 109). **Kernel evidence:** `Audit.Foundations.theorem3_statement_eq_eq_kleeneOperator_op_statement` discharges the equivalence of the two statements by `Iff.rfl` — they are the *same proposition*, because `kleeneOperator.op D f` reduces to `kleeneFix ⇑f`. The existing proof term is already `theorem3 F hF D f`. Also `U` by citation: total occurrences 1 |

### 4.17 `EffectivePresentation.lean` (3)

| # | Declaration | Module | Label | Evidence |
| -- | ---------- | ------ | ----- | -------- |
| 111 | `enum_mem` | `EffectivePresentation.lean` | **U** | total occurrences 1. Restates the `enum_mem_compacts` field as set membership in `compacts α`; no caller |
| 112 | `range_enum` | `EffectivePresentation.lean` | S | cited by `countable_compacts` (`:95`) — its only consumer, itself a `U` (row 113) |
| 113 | `countable_compacts` | `EffectivePresentation.lean` | **U** | qualified `grep` finds no use; the 43 apparent externs are collisions with the `Domain.countable_compacts` class field. Its own docstring says it is "a consistency check on the definition rather than new information" |

### 4.18 `ComputableFunction.lean` (5)

| # | Declaration | Module | Label | Evidence |
| -- | ---------- | ------ | ----- | -------- |
| 114 | `rePred_comp` | `ComputableFunction.lean` | S | cited `:118`, `:135` |
| 115 | `IsUniformlyComputable.isComputable` | `ComputableFunction.lean` | **U** | total occurrences 2: the declaration and `ComputableFunction.lean:47`'s docstring. Written to relate the paper's non-uniform reading to the uniform one; nothing consumes either |
| 116 | `isUniformlyComputable_of_enumMap` | `ComputableFunction.lean` | S | cited by rows 117 and 118 (`:149`, `:156`) — both of which are themselves `U`, so this is transitively dead |
| 117 | `isUniformlyComputable_id` | `ComputableFunction.lean` | **U** | total occurrences 1. Docstring: "The identity is computable with respect to any presentation whose ordering is recursive." A closure property for a computability theory that has no theorems |
| 118 | `isUniformlyComputable_const` | `ComputableFunction.lean` | **U** | total occurrences 1. Same |

## 5. Totals

| # | Label | Count | Share of 118 live |
| -- | ----- | ----- | ----------------- |
| 1 | `P` — states a paper property | **9** | 7.6% |
| 2 | `S` — support, something cites it | **65** | 55.1% |
| 3 | `A` — projection / `simp` / defining-equation API | **26** | 22.0% |
| 4 | `U` — uncited, not a paper property, not API | **12** | 10.2% |
| 5 | `D` — duplicate of another declaration | **6** | 5.1% |
| 6 | `W` — proved at a strength nothing consumes | **0** | 0% |
| — | live total | **118** | 100% |
| — | already commented out in place (r0020) | 5 | — |
| — | **counted by `module-counts.sh`** | **123** | — |

`U` + `D` = **18 of 118, 15.3%**. r0020's rate over the then-37 modules was 6 of
~199, about 3%. The difference is not a change in discipline; it is that r0020
had no `D` label and did not count the §3.2 stack, which is 6 of the 18 on its
own. `U` alone is 12 of 118, **10.2%**.

**The `P` count understates the stream's paper coverage, and by a measurable
amount.** The plan expected `P` density to be higher here because Theorem 7 lives
in this stream. It does, but a paper property is discharged by whatever Lean
construct fits it, and only some of those are `theorem`s:

| # | Construct | Paper properties it carries here | Rows in §4 |
| -- | -------- | -------------------------------- | ---------- |
| 1 | `theorem` | Thm 1; Thm 3; Thm 7 (whole); Thm 7's countability conjunct; prose 1, 5, 6; §4.1's two new claims | 9 |
| 2 | `instance` | prose 2 (`Domain (Set X)`), 3 (`CompletePartialOrder (ScottHom α β)`), 4 (`BoundedComplete (ScottHom α β)`), 7 (`IsAlgebraic (ScottHom α β)`), 12 (`strictHomCpo`) | 0 |
| 3 | `def` | Lemma 8 parts 1–4 (`prodComm`, `prodAssoc`, `scottHomProd`, `scottHomCurry`) | 0 |

So **nine** further paper properties are discharged in these nineteen modules and
produce no row in the table, because `counts.sh` counts neither `instance` nor
`def` as theorem-ish. Counting by numbered-result conjunct and prose claim rather
than by Lean construct, the stream discharges **20** paper properties: 10
numbered-result conjuncts (Thm 1, Thm 3, Thm 7 ×4, Lem 8 ×4) and 10 prose claims
(the baseline's 1–7 and 12, plus §3.2's two new ones). Note that the baseline's
own arithmetic double-counts three of these — prose claims 3, 4 and 7 *are* three
of Theorem 7's four conjuncts — so the distinct count is **17**.

## 6. The `U`, `D` and `W` rows called out

### 6.1 `U` — 12 declarations, in four groups

| # | Declaration | Module | Why it was written | Group |
| -- | ---------- | ------ | ------------------ | ----- |
| 1 | `WayBelow.trans` | `WayBelow.lean` | completing the `≪` order calculus | ≪ |
| 2 | `wayBelow_iff_sSup` | `WayBelow.lean` | "derives the `sSup` form once … for use downstream" (docstring) | ≪ |
| 3 | `wayBelow_iff_exists_compact` | `Domain.lean` | the characterization of `≪` in an algebraic cpo | ≪ |
| 4 | `exists_isLUB_of_bddAbove` | `Domain.lean` | "for readers checking the class against the paper's English" (docstring) | doc |
| 5 | `sSup_leftParts_ne_bot` | `CoalescedSum.lean` | the "base closed under nonempty directed suprema" pair | inlined |
| 6 | `sSup_rightParts_ne_bot` | `CoalescedSum.lean` | ditto | inlined |
| 7 | `isLeast_kleeneFix_le` | `FixedPoint.lean` | "what recursion arguments usually need" (docstring) | speculative |
| 8 | `enum_mem` | `EffectivePresentation.lean` | field restated as set membership | §3.2 |
| 9 | `countable_compacts` | `EffectivePresentation.lean` | "a consistency check on the definition" (docstring) | §3.2 |
| 10 | `IsUniformlyComputable.isComputable` | `ComputableFunction.lean` | relating the paper's reading to the uniform one | §3.2 |
| 11 | `isUniformlyComputable_id` | `ComputableFunction.lean` | closure property | §3.2 |
| 12 | `isUniformlyComputable_const` | `ComputableFunction.lean` | closure property | §3.2 |

**The ≪ group (3).** `WayBelow.lean` has 7 declarations; three of them are
uncited and the other four exist only to serve `Domain.lean`'s two `≪`
statements, which are themselves one `S` and one `U`. Across the whole
development the symbol `≪` appears in a **statement** in exactly two places, both
in `Domain.lean`; every other occurrence is docstring prose. The module is
retained regardless — `wayBelow_self_iff_isCompactElement` being `Iff.rfl` is
what lets `IsCompactElement` be used with the paper's vocabulary — but it is
carrying three declarations no proof reaches.

**The §3.2 group (5) is the largest single cluster, and it has a cause.**
`ComputableFunction.lean` is imported by **no module**; `EffectivePresentation.lean`
is imported only by `ComputableFunction.lean`. Between them, eight theorems have
zero consumers outside the two files. The reason is §3.4: the theorem that would
consume them is **Theorem 7's second sentence** — "if `D` and `E` have effective
presentations, then `D → E` has an effective presentation as well" — which the
paper calls "tedious, but not difficult" and which the development has never
attempted. These five are not speculative API in r0020's sense; they are the
*near* side of a bridge whose far side is unproved. The recommendation is
therefore not to comment them out but to record that decision: either prove
Theorem 7's second sentence, or mark the §3.2 stack as a recorded stub the way
r0031 marked the composition gap.

**The inlined pair (2) and the speculative one (1)** are r0020's population 3
exactly. `sSup_leftParts_ne_bot` / `sSup_rightParts_ne_bot` were superseded
within their own file — `isLUB_sumSup_left`/`right` prove the same non-bottomness
from `IsLUB` alone, needing no directedness. `isLeast_kleeneFix_le` has waited
since r0017.

### 6.2 `D` — 6 declarations, three pairs, all kernel-checked

The evidence is `ScottDomains/ScottDomains/Audit/Foundations.lean`, added this
round in namespace `ScottDomains.Audit.Foundations` and imported by nothing.

| # | Duplicate | Of | Kernel evidence | Citers of the duplicate |
| -- | -------- | -- | --------------- | ----------------------- |
| 1 | `Smash.coe_mem_of_mem_smashBase` | `Lift.coe_mem_of_mem_liftBase` | derived from `coe_mem_withBotBase` by application | 8 extern |
| 2 | `CoalescedSum.coe_mem_of_mem_sumBase` | `Lift.coe_mem_of_mem_liftBase` | ditto | 12 extern |
| 3 | `Smash.directedOn_smashBase` | `Lift.directedOn_liftBase` | derived from `directedOn_withBotBase` by application | 2 extern |
| 4 | `CoalescedSum.directedOn_sumBase` | `Lift.directedOn_liftBase` | ditto | 4 extern |
| 5 | `Smash.directedOn_val_smashBase` | `UniformFixedPoint.directedOn_val_image_subtype` | closed by `directedOn_val_image_subtype ht` | 2 extern |
| 6 | `UniformFixedPoint.eq_kleeneOperator_op` | `UniformFixedPoint.theorem3` | `Iff.rfl` — the same proposition | 0 |

Rows 1–4 are one structural finding, not four. `Lift`, `Smash` and
`CoalescedSum` each build `WithBot γ` over a base type (`α`, `NonBotPair α β`,
`NonBotSum α β`), each defines "the non-bottom part of a set" (`liftBase`,
`smashBase`, `sumBase` — three `def`s that are one `def`), and each then proves
the same two lemmas about it. `Audit/Foundations.lean` states the definition and
the two lemmas once at `[Preorder γ]` and derives all six existing statements by
application alone, no tactic. **The recommended action is a merge, not a
deletion**: 26 external call sites depend on these names, so the change is to
replace six declarations and three definitions with two and one, and repoint the
call sites. That is a follow-on round's work, and it touches agent3's
`Skeleton/` and agent5's `PRepFun`/`PRepSum`, so it is the orchestrator's to
schedule.

Row 6 is the cheapest to act on: `eq_kleeneOperator_op` is `theorem3` under a
different name, has no callers, and the `Iff.rfl` proves the statements are
definitionally identical rather than merely equivalent.

### 6.3 `W` — 0, and the four near misses

No declaration in this stream is proved at a strength nothing consumes. The four
that came closest, and why each falls short:

| # | Declaration | Why it is not `W` |
| -- | ---------- | ----------------- |
| 1 | `ScottHom.scottContinuous_pointwiseSup_of_forall_isLUB` | stated for an arbitrary `IsLUB` hypothesis rather than directedness, and **three different instantiations consume it** — directed (`:182`), bounded (`:189`), complete-lattice (`UniversalDomain.lean:407`). The generality is spent |
| 2 | `UniformFixedPoint.directedOn_val_image_subtype` | general over an arbitrary predicate `p`, and every call site inside its module uses `p := (· ∈ Set.Iic a)`. But the generality is exactly what makes `Smash.directedOn_val_smashBase` a duplicate of it, so the general form is the one to keep |
| 3 | `CompactFunction.isLUB_finiteJoinsBelow` | sits in a section without `[BoundedComplete β]`, which its only consumer does require. That is not over-strength but a deliberate record of where each hypothesis is spent, which the module docstring states |
| 4 | `FunctionSpaceCountable.isBoundedCompleteDomain_scottHom` | proved under **weaker** hypotheses than the paper states (bounded completeness of `D` is unused) — the opposite of `W`, and a strengthening of Theorem 7 |

`W`'s absence here is expected rather than surprising: r0032 and r0034 found it
at *paper-level* theorems (`thm25`, `thm12`), and this stream contains only four
paper-level theorems, two of which (`theorem1`, `theorem3`) are stated at exactly
the paper's hypotheses and one of which is row 4 above.

## 7. What was added, and the count delta

Two files, both listed here so the orchestrator can reconcile step 5 of the plan.

| # | Path | Effect on `counts.sh` |
| -- | ---- | --------------------- |
| 1 | `ScottDomains/ScottDomains/Audit/Foundations.lean` | modules 72 → 73, lines 27892 → 28032, theorems 1308 → 1311 |
| 2 | `scripts/agent1-citations.sh` | none |

The theorem delta is **+3** — `coe_mem_withBotBase`, `directedOn_withBotBase`,
`theorem3_statement_eq_eq_kleeneOperator_op_statement` — plus one `def`
(`withBotBase`) and seven `example`s, which `counts.sh` does not count. This is
the round's permitted exception (plan, deliverable 3); no other `.lean` file was
touched and nothing was deleted.

Build after the addition, `logs/compile-20260808-095133.agent1.log`:

    compile: exit 0 · wall 0:10.47 · mem 1839 MiB single · jobs 1224
             · diagnostics 0 · lake errors 0 · sorry 1 · other warnings 0

`sorry` is **1**, at `Skeleton/Section6.lean:197` (`thm18`) — unchanged. No
existing proof was modified.

## 8. Recommended edits to the shared documents

For the orchestrator, since agents do not write `analyses/` or edit
`docs/PaperInventory.md` in an audit round:

| # | Document | Edit |
| -- | ------- | ---- |
| 1 | `PaperInventory.md`, prose-claim table | drop row 8 (finiteness of the join is not a claim the paper makes); add two rows for §4.1's `fst(L)`/`snd(L)` directedness, mapped to `Product.directedOn_fst_image` / `directedOn_snd_image`. Row 3 count 12 → 13 |
| 2 | `PaperInventory.md`, line 474 | qualify the way-below row: the paper never uses the term, and `WayBelow` is the formalization's own construction |
| 3 | `PaperInventory.md`, line 485 (Thm 7) | record that only the **first** of Theorem 7's three sentences is formalized; the effective-presentation sentence and the `D →⊥ E` sentence are not |
| 4 | `PropertiesVsTheorems.md` §1 | row 20 unnumbered prose claims 12 → 13; paper properties total 99 → 100 |
| 5 | `PropertiesVsTheorems.md` §4 | note that `module-counts.sh` and `unused-theorems.sh` both count declarations inside block comments, so the 139 `@[simp]` figure and the 1308 total each include r0020's six retired declarations |
