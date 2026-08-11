---
round: r0053
from: orchestrator
to: agent2
subject: stricthomc-recursive
date: 2026-0810-18:40
status: pending
related: reports/r0052-report-from-agent1-to-orchestrator-unproven-claims-as-sorry.md
---

# r0053 / agent2 — root hole 2: collapse `StrictHomCRecursive` onto root 1, or discharge it

## 0. Setup

Work in `/home/milnes/projects/ScottLean4-agent2` on branch `agent2`. That branch
is an ancestor of `main`, so start by resetting onto it:

    git -C /home/milnes/projects/ScottLean4-agent2 reset --hard main

Build only through `scripts/compile.sh -r r0053`. Never call `lake build`
directly, never chain shell commands, never `cd`, never `sed -i`. Anything
needing more than one command becomes a script in `scripts/`.

## 1. The hole

`ScottDomains/ScottDomains/Effective/A3StepDecidable.lean:386`

```lean
theorem strictHomCRecursive_unproven [Domain (StrictHom α β)]
    (d : EffectivePresentation α) (e : EffectivePresentation β) :
    StrictHomCRecursive d e :=
  sorry
```

with, at line 371,

```lean
def StrictHomCRecursive [Domain (StrictHom α β)] (d : EffectivePresentation α)
    (e : EffectivePresentation β) : Prop :=
  IsRecursive d → IsRecursive e → IsRecursive (strictHomC d e)
```

It is the `⊸` counterpart of `ScottHomCRecursive`, and r0052 recorded it as a
**separate** root for a specific reason: the development's only route to
countability of `K(D ⊸ E)`, `PRepFun.strictHomDomain`, is an injection into
`K(D → E)` that names no enumeration, so no proved reduction carries
recursiveness across it. It is the hypothesis of
`theorem_7_strictRecursive_of_residue` and the root of
`R49.Agent3.StrictStepFunctionsDecidable` and
`Effective.Theorem7StrictRecursive`.

## 2. Goal A — the collapse, and try this before anything else

**Prove `StrictHomCRecursive d e` from `ScottHomCRecursive d e`.** If it lands,
the development drops from three roots to two, and agent1's round closes this one
too. That is a larger result than a second copy of agent1's recursion theory, so
spend the first part of the round here.

What to establish:

| # | Step | Note |
| - | ---- | ---- |
| 1 | `PRepFun.strictHomDomain`'s injection `K(D ⊸ E) ↪ K(D → E)` is *computable in the codings* — i.e. it carries the index of a `strictConsistentEnum` code to the index of a `consistentEnum` code | this is exactly what r0052 says is missing; it is the whole content of goal A |
| 2 | strictness of a step-function join is decidable from `d` and `e` alone | the image of the injection is a recursive subset, not merely a subset |
| 3 | `RecursiveLE` and `RecursiveNormal` both transport along a computable order-embedding with recursive image | state and prove this as a standalone transport lemma — it is reusable and it is the honest shape of the argument |

If step 1 or 2 is false or not reachable, say so with the counterexample or the
precise obstruction, and move to goal B. Do not fake the transport by assuming
the conclusion.

## 3. Goal B — the direct route, if the collapse does not land

Mirror agent1's decomposition over `⊸`. `Effective.IsRecursive` is
`RecursiveLE d ∧ RecursiveNormal d` (`Effective/FunctionSpace.lean:415`), so:

1. `RecursiveLE (strictHomC d e)` — the `⊸` analogue of §5 of
   `A3StepDecidable.lean`. Note that §5's reduction (`consistentEnum_le_iff`,
   `consistentEnum_apply_of_consistent`) is stated for `scottHomC` only; the
   strict half of that file (§6) has `isStrictStepEnumeration_strictHomC` and
   `strictStepJoin_empty` but **no order-test reduction**. Proving the strict
   order-test reduction is itself a worthwhile deliverable.
2. `RecursiveNormal (strictHomC d e)` — a characterization of `IsNormalIn` for a
   finite set of compact strict functions in terms of `d` and `e`.

Leverage: `R46.Agent3.strictHom`, `R46.Agent3.strictStepJoin`,
`R46.Agent3.strictPairsOf`, `strictConsistentEnum`,
`isStrictStepEnumeration_strictHom`, `strictStepFunctionsDecidable_of_strictHom`,
`R47.Agent2.bddAbove_stepsOf_iff`, `R47.Agent2.isNormalIn_joinClosure`.

## 4. Where the code goes

Write a new module
`ScottDomains/ScottDomains/Effective/StrictHomCRecursive.lean`, named for its
content per r0051, importing `Effective/A3StepDecidable.lean`.
**Do not edit `A3StepDecidable.lean`.** agent1 is working the `→` half of that
same file this round; the orchestrator does the one-line rewire of
`strictHomCRecursive_unproven` at merge time. Editing it would be the round's
only merge conflict and it is avoidable.

Name the transport lemma of goal A step 3 for what it says, and name the final
theorem `strictHomCRecursive` or `strictHomCRecursive_of_scottHomC` according to
which route closed it — the name must say whether it is unconditional.

## 5. Honesty conditions

- **Never** discharge by `axiom`, by `Classical.propDecidable` standing in for a
  decision procedure, by weakening the `def`, or by taking a hypothesis that is
  the claim. `IsRecursive` asks for a total recursive decision
  (`Effective/FunctionSpace.lean:85`).
- `strictHomCRecursive_of_scottHomC` is a **conditional** result. It collapses
  two roots into one; it does not close a hole. Report it as such — the `sorry`
  count only falls when something is proved unconditionally.
- If neither goal closes, the deliverable is the proved fragments plus the exact
  remaining Lean goals.

## 6. Acceptance criteria

| # | Criterion |
| - | --------- |
| 1 | `scripts/compile.sh -r r0053` reports 0 errors and 0 warnings other than `sorry` |
| 2 | the `sorry` count does not rise |
| 3 | every new theorem's `#print axioms` shows no `sorryAx` |
| 4 | `A3StepDecidable.lean` is byte-identical to `main` |
| 5 | committed with `scripts/gitcp.sh` on branch `agent2`; the push step reporting "no tracking information" is expected — do not push |
| 6 | report written to `ScottDomains/reports/r0053-report-from-agent2-to-orchestrator-stricthomc-recursive.md` with `started:`/`finished:` frontmatter |

The report states, quantitatively: whether goal A closed and if not exactly
which of its three steps failed and why; what of goal B closed; the Lean
statement and axiom footprint of each new theorem; the build log path; the root
count after the round (3, or 2 if the collapse landed).
