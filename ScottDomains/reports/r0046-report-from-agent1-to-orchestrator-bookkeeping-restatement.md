---
round: r0046
from: agent1
to: orchestrator
subject: bookkeeping-restatement
date: 2026-0809-11:32
started: 2026-0808-23:12
finished: 2026-0809-11:32
related:
  - plans/r0046-plan-from-orchestrator-to-orchestrator-zero-props-zero-false-prose.md
  - ScottDomains/reports/r0045-report-from-agent1-to-orchestrator-discharge-effective.md
  - ScottDomains/ScottDomains/A1R46.lean
  - scripts/a6-query.lean
  - scripts/a6-summarize.py
---

# r0046 — agent1: rows 1, 2, 3 (bookkeeping) and row 6 (restatement)

## Headline

| # | Measurement | Value |
| -- | ----------- | ----: |
| 1 | Goal A before, re-measured by me on the unchanged instrument | **10** |
| 2 | Goal A after, re-measured by me on the corrected instrument | **7** |
| 3 | claims moved from open to refuted | **3** |
| 4 | `StepFunctionsDecidable` discharged? | **no** — restated, still open |
| 5 | claims the corrected instrument shows are **under**-counted | **1** |
| 6 | plan predictions I could not meet | 1 — the plan says 10 → 6; the honest number is 7 |
| 7 | new declarations, all in `ScottDomains.R46.Agent1` | 3 |
| 8 | build | 1345 jobs, 0 errors, 0 warnings, 0 `sorry` |
| 9 | `sorryAx` in any new or changed footprint | 0 |

**The plan's "10 to 6" assumed row 6 would discharge. It did not, and could not
this round.** Rows 1–3 are bookkeeping and closed; row 6 is a statement fix, and
a fixed statement is still an open statement. 10 − 3 = 7.

## Per-claim status

| # | Claim | Status | Evidence |
| -- | ---- | ------ | -------- |
| 1 | `Colimit.Thm29Second` | **refuted** | `R45.Agent3.not_thm29Second`, now read out of the environment |
| 2 | `PRep.Lemma28` | **refuted** | `R45.Agent2.not_forall_lemma28` (+ `_bcd`, `not_lemma28_flatEmpty`) |
| 3 | `LemThirty.Lemma30` | **refuted** | `R46.Agent1.not_forall_lemma30` — new this round |
| 4 | `Effective.Theorem7ArrowRecursive` | **reduced**, unchanged in strength | now reduced to the *claim's own universal closure* rather than to a hand-strengthened variant |
| 6 | `Effective.StepFunctionsDecidable` | **restated, open** | blocking fact named below and in the module docstring |

## 1–3. Bookkeeping: the instrument changed, not the statements

The detector's test for "undischarged" is `uncond == 0` — no package theorem
concludes the definition with no proof hypothesis. A refutation concludes `¬ D`,
whose head after `forallTelescope` is `Not`, so it never increments that counter.
A claim proved **false** therefore read exactly like a claim nobody had touched,
and would have done so forever.

I changed the instrument rather than any of the three `def`s, per the plan's
preference. Two new records in `scripts/a6-query.lean`:

* `REFUTEDBY <propdef> <theorem>` — a **closed refutation**: a theorem with no
  binders at all whose type is `¬ e`, where `e` after stripping binders is headed
  by that definition.
* `a6-summarize.py` splits the claim count into refuted (resolved) and open, and
  names the refuting theorem for each. **Goal A is the open count.**

Why the criterion is exactly "no binders, conclusion `¬ e`", stated in the
script's own docstring so it is auditable: if `¬ e` holds and `e` is
`∀ xs, hyps → D args`, the universal closure of `D` fails, because that closure
would give `D args` for every `args` and hence `e`. So refuting an *instance*
(`¬ D c`) and refuting a *weakened form* (`¬ ∀ U, Domain U → D U`) are both
sound witnesses, and both occur here. Requiring zero binders is what rules out
the unsound reading: `[Subsingleton U] → ¬ Lemma28 U` refutes nothing until some
`U` is exhibited, and `R45.Agent2` contains exactly that theorem next to the
closed one. The instrument accepts the closed ones and ignores that one.

No `def` was deleted. Each of the three now cites its refutation in its own
docstring, per the plan's condition:

| # | `def` | Docstring now names |
| -- | ---- | ------------------- |
| 1 | `Colimit.lean:1043` | `R45.Agent3.not_thm29Second`, and why `Thm29SecondAtDomains` survives |
| 2 | `PRep.lean:267` | `R45.Agent2.not_forall_lemma28`, `_bcd`, and `UniversalForBCD` as the missing content |
| 3 | `LemThirty.lean:226` | `R46.Agent1.not_forall_lemma30`, and that `Lemma30AtV` is the surviving claim |

### Row 3 was argued but never proved; now it is

The plan describes `Lemma30` as "a parameterized family whose universal closure
is false". Nothing in the package proved that. It is now one line:

    theorem ScottDomains.R46.Agent1.not_forall_lemma30 :
        ¬ ∀ (W : Type) (inst : CompletePartialOrder W), @LemThirty.Lemma30 W inst

by `LemThirty.lemma30_iff_lemma28_and_plotkin` (Lemma 30 is Lemma 28's nine
conjuncts plus `(·)♮`) and `R45.Agent2.not_forall_lemma28`. Footprint
`[propext, Classical.choice, Quot.sound]`.

Two things it does **not** say, both recorded in its docstring because the
opposite reading is easy: it is not a defect in the paper, whose Lemma 30 is
stated over §7.4's own `V`; and it is not news about `(·)♮`, whose conjunct is
not used in the proof. The carrier is a parameter only so that the proposition
and its instantiation are separate declarations.

## 6. The restatement

### The printed sentence, checked against the PDF

Theorem 7's proof sketch, **printed p. 12** of Gunter & Scott, *Semantic
Domains* (`ScottDomains/papers/Gunter Scott 1990.pdf`; the running head "12
Carl A. Gunter and Dana S. Scott" opens the page and Theorem 7 is the first
display on it):

> The proof that the poset of step functions has decidable ordering and finite
> normal subposets is tedious, but not difficult, **using the effective
> presentations of `D` and `E`**.

and §3.2's Definition, **printed p. 11**, which fixes the term:

> Let `D` be a domain and suppose `d : N → K(D)` is a surjection. Then `d` is an
> effective presentation of `D` if (1) the set `{(m,n) | dₘ ⊑ dₙ}` is effectively
> decidable, and (2) for any finite set `u ⊆ N`, it is decidable whether
> `{dₙ | n ∈ u} ◁ K(D)`.

"Effectively decidable", in a section about computability, is *recursive*. In
this development that is `Effective.IsRecursive` — `RecursiveLE ∧
RecursiveNormal` — and **not** the `EffectivePresentation` structure, whose two
`Decidable` fields may be `Classical.dec`; `nonempty_effectivePresentation`
proves every domain has one of those. So "`D` and `E` have effective
presentations" is `IsRecursive d` and `IsRecursive e`.

### Old statement, new statement, and why the old one was wrong

    -- through r0045
    def StepFunctionsDecidable (d) (e) : Prop := IsRecursive (scottHom d e)

    -- r0046
    def StepFunctionsDecidable (d) (e) : Prop :=
      IsRecursive d → IsRecursive e → IsRecursive (scottHom d e)

The old form dropped the printed sentence's own qualification. As written it
asserted that the step-function presentation of `D → E` is recursive for
*arbitrary* `d` and `e`, including the `Classical.dec` presentations every domain
has. No sentence of the paper asserts that.

### The three conditions the plan set, and how each is met

1. **Printed sentence and page quoted in the docstring** — both sentences, both
   pages, verbatim, at `Effective/FunctionSpace.lean:406`.
2. **Old statement recorded, with why it was wrong** — recorded in the docstring,
   and kept as a Lean declaration, `R46.Agent1.StepFunctionsDecidableUnconditional`,
   so it can be cited rather than paraphrased. Its own docstring says it is a
   **rejected transcription and not a claim of the paper**, and `scripts/a6-claims.txt`
   now says not to add it.
3. **Stronger or equal at the paper's intent** — this is the condition that needs
   an argument, because as a *proposition* the change is a strict weakening. Two
   checks, one of them by the kernel:

   * `R46.Agent1.stepFunctionsDecidable_of_unconditional : old → new` — the
     kernel confirms that exactly two hypotheses were added and nothing else
     changed.
   * The bar itself did not move. `Effective.Theorem7ArrowRecursive`, the
     transcription of the sentence this claim serves, **already** carried
     `IsRecursive d → IsRecursive e →` and is untouched by this round. The claim
     now carries exactly the hypotheses its consumer always had. That is the test
     for "no silent weakening": if the restatement had lowered a bar, the
     consumer would have had to be weakened too, and it was not.

   A third, weaker check, reported as such: r0045's agent1 gave a three-step
   refutation sketch for the old form. It is **not** kernel-checked and the case
   for restating does not rest on it — a transcription that drops a printed
   antecedent is defective whether or not the over-strong reading is also false.

### Consumers changed

Two, both forced, both in the direction of less hidden strength:

* `Effective.exists_isRecursive_of_stepFunctionsDecidable` now takes `hd :
  IsRecursive d` and `he : IsRecursive e` explicitly instead of extracting an
  unconditional conclusion from an over-strong hypothesis.
* `R45.Agent1.theorem7ArrowRecursive_of_stepFunctionsDecidable`'s hypothesis is
  now the **claim's own universal closure**, `∀ … (d) (e), StepFunctionsDecidable
  d e`, where in r0045 it had to be the hand-strengthened `∀ … , IsRecursive d →
  IsRecursive e → StepFunctionsDecidable d e`. Same proposition, spelled once
  instead of twice; the reduction of `Theorem7ArrowRecursive` is not stronger or
  weaker than it was, but it is now checkable by inspection.

### Did it discharge? No. What blocks it — measured, not assumed

Both obstructions on record in `Effective/FunctionSpace.lean` are **real** and
**neither blocks this claim**. Measured against the installed Mathlib:

| # | Recorded obstruction | Re-measured | Does it block rows 2–3? |
| -- | ------------------- | ----------- | ----------------------- |
| 1 | no `Primrec`/`Computable` fact about `Nat.bitwise`, `Nat.lor`, `Nat.testBit` | **real**: 0 files under `Mathlib/Computability/` mention any of them; 0 files in all of `Mathlib/` co-mention them with `Primrec`/`Computable` | **no** — it obstructs *constructing* a recursive presentation of `P N`; rows 2–3 take `IsRecursive d`, `IsRecursive e` as hypotheses and construct none |
| 2 | `REPred` closed under neither `∧` nor `∃` | **real**: `REPred` occurs in exactly 2 Mathlib files (`Computability/RE.lean`, `Computability/Halting.lean`), and the 5 + 2 declarations mentioning it are `of_eq`, `Partrec.dom_re`, `ComputablePred.to_re`, `computable_iff_re_compl_re`, `computable_iff_re_compl_re'`, `halting_problem_re`, `halting_problem_not_re` — no closure lemma | **no** — rows 2–3 are about `IsRecursive`, which is `ComputablePred` on both conjuncts and names `REPred` nowhere. The missing closure obstructs `IsComputable` / `IsUniformlyComputable` |

This matters for agent3's message: it converges on row 6, but the two
obstructions it names are not what stands in row 6's way. What does:

| # | Needed for `IsRecursive (scottHom d e)` | State |
| -- | -------------------------------------- | ----- |
| 1 | `ofPairs P ≤ g` as a finite condition | **half available** — `ScottHom.step_le_iff` with `sSup_le` gives `ofPairs P ≤ g ↔ ∀ (a,b) ∈ P, b ≤ g a`; unstated but immediate |
| 2 | `ofPairs Q` evaluated pointwise, to apply row 1 at `g := ofPairs Q` | **missing**, and it is row 3 in disguise: `sSup` on `ScottHom` is pointwise only on directed sets and `stepsOf Q` is not directed |
| 3 | a decision procedure for `IsCompactElement (ofPairs Q)` — the boundedness test `scottHomEnum` performs classically | **missing**; this is the paper's own "tedious" step, and condition 2 of `e` is exactly what it is for |
| 4 | `IsNormalIn` for a finite set of compact functions, in terms of `d` and `e` (this is `RecursiveNormal`) | **missing**; `R45.Agent1.isNormalIn_compacts_flat_iff` is the flat case only, and it reduces to row 3 as well — a mub of step functions is a bounded join |
| 5 | `Primrec` facts for the `Denumerable (Finset (ℕ × ℕ))` coding | **missing but known feasible** — r0045 proved the `Finset ℕ` analogue after this file's "`Primcodable (Finset ℕ)` does not exist" was refuted by `Primcodable.ofDenumerable` |

**The single blocking fact is row 3: whether a finite set of step functions named
by index pairs is bounded above.** Rows 2 and 4 reduce to it; rows 1 and 5 are
available or known feasible. So row 6 — and with it `Theorem7ArrowRecursive`, and
per agent3 `Theorem7StrictRecursive` — is blocked on **domain theory, not
recursion theory**. That is a materially better-posed problem than "two Mathlib
gaps", and it is one lemma, not a research programme. The obstruction paragraph
in `Effective/FunctionSpace.lean` has been rewritten to say this; the two
recorded obstructions are kept, with their re-measurement and with the note that
they are real but out of scope for these rows.

## A correction to the instrument that goes the other way

While re-measuring I found the detector also **under**-counts, and the same
`uncond` test is the cause. It scores any zero-proof-hypothesis theorem headed by
the claim as a discharge, including one that fills a parameter slot with a
particular value or with another binder — r0044's dominant defect mode, and the
one the plan warns about.

`PROVEDBY` now carries a `generic` field: true when the conclusion applies the
definition to pairwise-distinct binders of the theorem itself, false otherwise.
`a6-summarize.py` prints the claims counted resolved whose every unconditional
proof is non-generic. Measured over the whole package: **exactly one.**

    !! counted resolved but every unconditional proof is at a parameter instance: 1
       ScottDomains.Effective.PreservesRecursivePresentation
         by R45.Agent1.preservesRecursivePresentation_id,
            R45.Agent1.preservesRecursivePresentation_natBot

Both are the schema at `γ := α` and `γ := Flat ℕ`; r0045's agent1 flagged them in
prose and this now measures them. The other eight claims scored resolved are
genuinely generic — the diagnostic clears them.

**So the two honest numbers are:**

* **Goal A = 7** under the criterion the plan's baseline of 10 was taken with,
  refutation-aware. This is the apples-to-apples number.
* **Goal A = 8** under the strict criterion, adding `PreservesRecursivePresentation`.

I did not change the headline count to 8. The defect is in the *statement* of
`PreservesRecursivePresentation`, not in its status — r0045's agent1 recommended
one `def` per operator — and rewriting that `def` is outside this round's narrow
authorization, which named row 6 only. Your call.

## Declarations added and changed, with footprints

All new declarations in `ScottDomains.R46.Agent1`, in
`ScottDomains/ScottDomains/A1R46.lean`.

| # | Declaration | Kind | Footprint |
| -- | ----------- | ---- | --------- |
| 1 | `not_forall_lemma30` | new | `[propext, Classical.choice, Quot.sound]` |
| 2 | `StepFunctionsDecidableUnconditional` | new `def` (rejected transcription) | — |
| 3 | `stepFunctionsDecidable_of_unconditional` | new | `[propext, Classical.choice, Quot.sound]` |
| 4 | `Effective.StepFunctionsDecidable` | **restated** | — |
| 5 | `Effective.exists_isRecursive_of_stepFunctionsDecidable` | signature changed | `[propext, Classical.choice, Quot.sound]` |
| 6 | `R45.Agent1.theorem7ArrowRecursive_of_stepFunctionsDecidable` | hypothesis simplified | `[propext, Classical.choice, Quot.sound]` |

Docstring-only edits: `Colimit.Thm29Second`, `PRep.Lemma28`, `LemThirty.Lemma30`
(refutation citations, required by the plan); `Effective/FunctionSpace.lean`'s
module docstring (the obstruction paragraph, replaced by the measured one);
`Effective/A1FlatRecursive.lean`'s module docstring (one paragraph, to match the
changed hypothesis). No statement outside row 6 was changed.

Instrument edits: `scripts/a6-query.lean` (REFUTEDBY records, `generic` field),
`scripts/a6-summarize.py` (refuted/open split, parameter-instance diagnostic),
`scripts/a6-claims.txt` (comments only — no line added or removed).

## Corrections to the plan

* **"10 to 6" is not attainable by rows 1, 2, 3 and 6.** Three of those four are
  bookkeeping and give 10 → 7; the fourth is a statement fix, and a fixed
  statement is still open. The measured result is 7.
* **The plan calls rows 1–3 "not proof work".** Row 3 was not: `Lemma30`'s
  universal closure had been argued in prose and never proved false, so retiring
  the row without proving it would have been the same kind of unchecked prose
  Goal B exists to remove. It is one line, but it had to be written.
* **`Lemma30`'s `def` should be kept, not dropped.** The plan says "drop the row,
  keep the `def` if it is used". It is used — four references — and with the
  refutation recorded the row leaves the count on its own, so there is nothing to
  drop by hand.
* **The detector's error is two-sided.** The plan treats rows 1–3 as the
  instrument's only error. The same test also scores one claim resolved that is
  not, and a future round that fixes only the over-count will report a number
  that is too low.

## What I would do next, in cost order

1. **The boundedness test**: decide `IsCompactElement (ofPairs Q)` for a finite
   `Q` of compact pairs, from `d` and `e`. One lemma, and it is simultaneously
   rows 2, 3 and 4 of the blocking table — that is, it is the whole of
   `StepFunctionsDecidable`, of `Theorem7ArrowRecursive`, and (per agent3) of
   `Theorem7StrictRecursive`. Three of the seven remaining Goal A rows.
2. **Restate `PreservesRecursivePresentation`**, one `def` per operator, shaped
   like `Theorem7ArrowRecursive`. Removes the one under-count, and it is the same
   class of defect row 6 was.
3. The `Finset (ℕ × ℕ)` singleton-coding `Primrec` fact — needed for step 1's
   recursion-theoretic half, and known feasible.
