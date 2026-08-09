---
round: r0047
from: agent5
to: orchestrator
subject: unfinished-proofs
date: 2026-0809-12:24
started: 2026-0809-12:05
finished: 2026-0809-12:24
related:
  - plans/r0047-plan-from-orchestrator-to-orchestrator-close-the-seven.md
  - analyses/a5-r47-conditional.txt
  - ScottDomains/A5Unfinished.lean
  - scripts/a5-r47-conditional.sh
  - scripts/a5-r47-stale.lean
---

# r0047, agent5 — the unfinished proofs: the `S+H` rows re-measured

## 1. The answer

**The real count is 12, not 16.** Four of the sixteen are stale, and all twelve
survivors are in §7. They have **exactly two missing inputs** between them: ten
follow from `Thm29Normal`, and two are Lemma 30's arrow conjuncts.

Build after this stream's changes: **1357 jobs, 0 errors, 0 warnings, `sorry` 0**.
Five theorems added, every one `[propext, Classical.choice, Quot.sound]` and no
`sorryAx`.

## 2. Derivation of the count

`PaperInventory.md` carries 16 = r0040's 15 (14 in §7, 1 in §6) + r0043's 1. No
round between r0040 and this one re-measured the label: **r0043 re-checked only
the `N` rows and r0044 only the `S≠` rows.** Each of the sixteen was re-derived
here from the current tree, and the three reclassifications were confirmed by the
kernel via `scripts/a5-r47-stale.lean`, not by reading a source file.

| # | Row (r0040 numbering) | Was | Is | Evidence |
| -- | --------------------- | --- | --- | -------- |
| 1 | §6 row 14 — **Theorem 18** | `S+H` | **`S+P`** | `ScottDomains.thm18 : ∀ {α} [CompletePartialOrder α] [Domain α] [Domain (ScottHom α α)], IsBifinite α`. r0040's two open steps, `JungNets.Thm137` and `JungFinite.FixedPointOfCompactDeflationIsCompact`, are both gone from the signature. The binders are the paper's own sentence — **no added instance binder** |
| 2 | §7 row 20 — **Lemma 28, `(·)♯`** | `S+H` | **`S+P`** | `R45.Agent4.repSmythAtU : IsPRepresentable Dyadic.U smythOp`, arity 0 |
| 3 | §7 row 21 — **Lemma 28, `(·)♭`** | `S+H` | **`S+P`** | `R45.Agent4.repHoareAtU`, arity 0; and `R45.Agent4.lemma28AtU : PRep.Lemma28AtU` discharges the whole nine-fold conjunction with no hypothesis |
| 4 | r0043's +1 — **`StepFunctionsDecidable`** | `S+H` | **not an `S+H` row** | a `Prop`-valued `def` nobody attempted. r0043's own §4 item 3 recorded it as "the nearest fit" and said the taxonomy conflates a genuinely open `Prop` with a `sorry`. The plan's brief for this stream draws the same line: an `S+H` row is "a real Lean statement with an open proof, **not a `def` nobody attempted**" |

16 − 4 = **12**.

Rows 1–3 were already recorded as closed elsewhere — r0043's merge note moved
Theorem 18, and r0046's analysis lists Lemma 28 as refuted-and-resolved — but the
`S+H` tally was never decremented. This is the same staleness r0044 found in the
Class 1 assignment.

## 3. The twelve, per row

All twelve are §7. `reduced` means a kernel-checked theorem concludes the
property from a named open input, with **no added instance binder**.

| # | Row | Property | Status | Missing input |
| -- | --- | -------- | ------ | ------------- |
| 1 | 23 | Thm 29, sentence 2 at "bifinite **domain**" | reduced | `Thm29Normal` |
| 2 | 24 | Lem 30, `→` | **open** | a route to `Domain (ScottHom V V)` not through `[BoundedComplete V]` |
| 3 | 25 | Lem 30, `⇸` | **open** | same |
| 4 | 26 | Lem 30, `×` | reduced | `Thm29Normal` |
| 5 | 27 | Lem 30, `⊗` | reduced | `Thm29Normal` |
| 6 | 28 | Lem 30, `+` | reduced | `Thm29Normal` |
| 7 | 29 | Lem 30, `⊕` | reduced | `Thm29Normal` |
| 8 | 30 | Lem 30, `(·)⊥` | reduced | `Thm29Normal` |
| 9 | 31 | Lem 30, `(·)♯` | reduced | `Thm29Normal` |
| 10 | 32 | Lem 30, `(·)♭` | reduced | `Thm29Normal` |
| 11 | 33 | Lem 30, `(·)♮` | reduced | `Thm29Normal` |
| 12 | prose 28 | `R♮(p) = Ψ♮ ∘ (p♮) ∘ Φ♮` represents `(·)♮` | reduced | `Thm29Normal` |

**Zero of the twelve are open because nobody tried**, and **zero are false as
stated**. Ten are reduced to one published lemma; two are blocked by a structural
defect in the development, not in the paper.

`R47.Agent5.nine_props_ten_rows` is the kernel's record of the first column:
`Thm29Normal → (Thm29SecondAtDomains ∧ eight Lemma-30 conjuncts)`. Nine
propositions cover ten rows because rows 33 and prose-28 are the same Lean
proposition — Lemma 30's tenth conjunct and the sentence naming its conjugating
formula. The hypothesis is `Thm29Normal` **exactly as stated**.

## 4. No `S+H` row has appeared in §§2–6 since r0040

This was the measurement nobody had made, and it is the reason the stream was
worth running even though §7 turned out to be fully mined.

With `sorry` at 0, an open proof cannot appear as a hole — it appears as a
**conditional theorem**, one whose hypothesis list contains a claim the
development has not discharged. So the mechanical detector for `S+H` is: find
every declaration that takes an open or refuted claim as a hypothesis.
`scripts/a5-r47-conditional.sh` does that over the eight open claims and three
refuted ones of r0046's census; output in `analyses/a5-r47-conditional.txt`.

**Result: the entire conditional surface of the package is five files** —
`Colimit.lean`, `LemThirty.lean`, `A3Thm29.lean`, `A3Lemma30Schemes.lean` and
`Effective/FunctionSpace.lean`. Six rounds of edits since r0040 added **no** new
`S+H` row anywhere in §§2–6. The label was stale in the direction of
over-counting only.

## 5. What this stream proved

Five theorems in `ScottDomains/A5Unfinished.lean`, namespace
`ScottDomains.R47.Agent5`.

| # | Theorem | Content | Axioms |
| -- | ------- | ------- | ------ |
| 1 | `nine_props_ten_rows` | ten of the twelve rows from `Thm29Normal`, hypothesis used exactly as stated | `propext, Classical.choice, Quot.sound` |
| 2 | `not_thm29SecondAtDomains_and_boundedComplete_V` | `¬ (Thm29SecondAtDomains ∧ BoundedComplete V)` | same |
| 3 | `not_boundedComplete_idealCompletion` | an ideal completion whose base has two distinct minimal upper bounds over one pair is not bounded complete | same |
| 4 | `not_boundedComplete_V_of_two_mubs` | the same at `Ainf`, giving `¬ BoundedComplete V` | same |
| 5 | `no_boundedComplete_instance_V_of_two_mubs` | the instance form, `IsEmpty (BoundedComplete V)` | same |

### 5.1 Rows 24 and 25 are not merely open — their route is contradictory

`LemThirty.retracts_fun_of_boundedComplete` and
`retracts_strictFun_of_boundedComplete` are the development's only route to
Lemma 30's conjuncts 1 and 2. They take **two** hypotheses and both are dead:

1. `Colimit.Thm29Second` is **refuted** (`R45.Agent3.not_thm29Second`), so both
   declarations are vacuous as they stand. Seven declarations in `LemThirty.lean`
   take that refuted claim; three of them (`retracts_smash`, `retracts_sepSum`,
   `retracts_coalSum`) were given non-vacuous successors in `A3Thm29.lean` in
   r0045, and **these two were not**.
2. Repairing them to the live `Thm29SecondAtDomains`, which is exactly what
   r0045 did for `⊗`, `+` and `⊕`, **would not help**. Theorem 2 above is the
   kernel's record: `{Thm29SecondAtDomains, BoundedComplete V}` is a
   contradictory hypothesis set. `A3Thm29.lean:356-363` states this consequence
   in prose; it is now a theorem.

So conjuncts 1 and 2 need a route **replaced**, not repaired. That is agent4's
stream, and this is the kernel-checked reason it cannot be short-cut.

### 5.2 The most valuable thing located: `¬ BoundedComplete V`, reduced to a finite check

`R45.Agent3.not_boundedComplete_V` gives `¬ BoundedComplete V` only **under** the
open `Thm29SecondAtDomains`. An *unconditional* `¬ BoundedComplete V` would kill
the conjunct-1/2 route regardless of how Theorem 29 turns out — a grade-A
negative result in r0046's terms, since it refutes the hypothesis-free statement
rather than reporting a failed reproof.

Theorem 3 reduces it to one purely order-theoretic fact, with no domain theory in
the statement: an ideal completion fails bounded completeness as soon as its base
carries **one pair with two distinct minimal upper bounds**. `V` is
`IdealCompletion Ainf` (`Colimit.lean:770`), so Theorem 4 is that at `Ainf`.

**The missing input, named exactly: two elements of `Colimit.Ainf` with two
distinct minimal upper bounds.** This is finite arithmetic, not domain theory —
the stages `Stg n` are finite (`instFiniteStg`) and normal in `Ainf`
(`isNormalIn_range_incl`), and a normal subposet preserves minimal upper bounds,
which is what `◁` is for, so a witness inside one stage transports.

Measured by hand, and labelled as such in the module docstring rather than
asserted as checked: the configuration does **not** occur at `Stg 1` (two
elements) or `Stg 2` (five, after `MPair.equiv_of_upper_eq` identifies
`(a,{a})` with `(a,{a,b})`; the order is `⊥` below all, `q ≤ r ≤ s`, and `p`
above nothing but `⊥`, in which every bounded pair has a least upper bound). So
the witness, if it exists, is at `Stg 3` or later.

## 6. Corrections to the plan

1. **The plan's 16 is 12.** Its own instruction to re-derive is what found it;
   the plan is not evidence, and rows closed in r0043 and r0045 were never
   decremented from this tally.
2. **`StepFunctionsDecidable` is not an `S+H` row** by the plan's own definition,
   and it is already agent2's stream. Counting it in both places double-counts.
3. **My first plan for this stream was wrong and I dropped it.** I identified
   Lemma 30's conjuncts 8 and 9 as "four lines away" from `R45.Agent4.rep_smyth`
   and `LemThirty.retracts_smyth`. That is correct, and **r0046's agent3 already
   wrote those four lines** (`A3Lemma30Schemes.repSmythAtV`, `repHoareAtV`), plus
   the `(·)♮` scheme. Checking before writing cost one file read and saved a
   duplicate declaration in a round where namespace collisions are the stated
   risk. Recording it because the plan asked each stream to re-derive rather than
   trust the record, and here the record was *ahead* of the plan, not behind it.

## 7. What I did not do

I did not attempt Lemma 30's conjuncts 1 and 2 themselves — that is agent4's
stream and duplicating it would have produced a second `[BoundedComplete V]`
binder, the development's dominant defect mode. I did not search for the `Stg 3`
witness; it is a bounded finite computation and it is stated here as a named,
located input rather than padded into a claim.

No claim's or property's statement was changed.
