---
round: r0053
from: orchestrator
to: agent1
subject: scotthomc-recursive
date: 2026-0810-18:40
status: pending
related: reports/r0052-report-from-agent1-to-orchestrator-unproven-claims-as-sorry.md
---

# r0053 / agent1 — discharge root hole 1: `ScottHomCRecursive`

## 0. Setup

Work in `/home/milnes/projects/ScottLean4-agent1` on branch `agent1`. That branch
is an ancestor of `main`, so start by resetting onto it:

    git -C /home/milnes/projects/ScottLean4-agent1 reset --hard main

Build only through `scripts/compile.sh -r r0053`. Never call `lake build`
directly, never chain shell commands, never `cd`, never `sed -i`. Anything
needing more than one command becomes a script in `scripts/`.

## 1. The hole

`ScottDomains/ScottDomains/Effective/A3StepDecidable.lean:200`

```lean
theorem scottHomCRecursive_unproven (d : EffectivePresentation α)
    (e : EffectivePresentation β) : ScottHomCRecursive d e :=
  sorry
```

with, at line 184,

```lean
def ScottHomCRecursive (d : EffectivePresentation α) (e : EffectivePresentation β) :
    Prop :=
  IsRecursive d → IsRecursive e → IsRecursive (scottHomC d e)
```

`Effective.IsRecursive` (`Effective/FunctionSpace.lean:415`) is the conjunction
`RecursiveLE d ∧ RecursiveNormal d`. So the goal splits into exactly two
obligations, and they are of very different difficulty:

| # | Obligation | State |
| - | ---------- | ----- |
| 1 | `Computable.RecursiveLE (scottHomC d e)` | reduced to a finite condition already, by §5 of the same file |
| 2 | `Effective.RecursiveNormal (scottHomC d e)` | open; `Effective/FunctionSpace.lean:128` records the missing ingredient |

This is 49 conditional consumers' lower bound in part: `ScottHomCRecursive` is
the root for `Effective.StepFunctionsDecidable` (via
`stepFunctionsDecidable_of_scottHomC`) and `Effective.Theorem7ArrowRecursive`
(via `R47.Agent2.theorem_7_arrowRecursive_of_scottHomC`).

## 2. What is already proved and must be used, not re-derived

Read `Effective/A3StepDecidable.lean` end to end before writing anything.
Named leverage, all kernel-checked:

| # | Lemma | What it gives |
| - | ----- | ------------- |
| 1 | `consistentEnum_le_iff` (§5, line 264) | the order test `consistentEnum d e m ≤ consistentEnum d e n` as a condition with every quantifier over the two decoded finite index sets |
| 2 | `consistentEnum_apply_of_consistent` / `_of_not_consistent` | pointwise value of the enumeration, guard split into two lemmas so no classical `Decidable` enters the statement |
| 3 | `R47.Agent2.bddAbove_stepsOf_iff` | `Consistent` is exactly existence of the join |
| 4 | `R47.Agent2.bddAbove_iff_exists_normal` | deciding `Consistent` reduces to a search over finite normal subposets |
| 5 | `R47.Agent2.isNormalIn_joinClosure` | that search terminates |
| 6 | `isStepEnumeration_scottHomC` (line 120) | `scottHomC` is a step-function enumeration — already proved, do not touch |
| 7 | `Effective/A4Recursion.lean:714` and neighbours | `RecursiveLE d`, `RecursiveLE e` decide `≤` between basis elements with no unbounded search |
| 8 | `R45.Agent1.isNormalIn_compacts_flat_iff` | the flat-cpo case of obligation 2 — the shape the general case must take |

## 3. Order of attack

1. **Obligation 1 first, in full.** Prove
   `RecursiveLE (scottHomC d e)` from `RecursiveLE d` and `RecursiveLE e`, going
   through `consistentEnum_le_iff`. The remaining work is the recursion theory:
   `Primrec`/`Computable` facts for the `Denumerable (Finset (ℕ × ℕ))` coding,
   a decision procedure for `Consistent (Effective.pairsOf d e Q)`, and one for
   `b ⊑ ⨆{values below a}` in `E`. Verify: the theorem elaborates and
   `#print axioms` on it shows no `sorryAx`.
2. **Then obligation 2.** `RecursiveNormal (scottHomC d e)` is
   `ComputablePred fun n => basisSet (scottHomC d e) n ◁ compacts (ScottHom α β)`
   (`Effective/A4Recursion.lean:307`). `Effective/FunctionSpace.lean:128` names
   what is missing: a characterization of `IsNormalIn` for a finite set of
   compact functions in terms of `d` and `e`, needing mub-closure in
   `K(D → E)`; it reduces further, since a mub of step functions is a bounded
   join. Prove that characterization as a standalone lemma first, then feed it
   to the `ComputablePred`.
3. **Only if both land**, conclude `ScottHomCRecursive d e` unconditionally.

## 4. Where the code goes

Write a new module `ScottDomains/ScottDomains/Effective/ScottHomCRecursive.lean`,
named for its content per r0051, importing `Effective/A3StepDecidable.lean`.
**Do not edit `A3StepDecidable.lean`.** agent2 is working in that same file's
`⊸` half this round, and the orchestrator does the one-line rewire of
`scottHomCRecursive_unproven` at merge time. Add the module to the package root
import list if this project keeps one — check how other modules are reached
before assuming.

Name the final theorem `scottHomCRecursive` (no `_unproven` suffix), and name
intermediate results for what they say.

## 5. Honesty conditions — these are the point of the round

The three sorried roots survived 52 rounds. A round that reports one closed when
it is not is worse than a round that closes nothing.

- **Never** discharge by `axiom`, by `Classical.choice` standing in for a
  decision procedure, by weakening the `def`, or by adding a hypothesis that is
  the claim. `Effective.IsRecursive` asks for a *total recursive decision*, not
  a Lean `Decidable` instance obtained from `Classical.propDecidable` — r0049
  already recorded that trap (`Effective/FunctionSpace.lean:85`).
- If you prove only obligation 1, say exactly that: state the proved theorem,
  leave the root `sorry` where it is, and report obligation 2 with the precise
  Lean goal that remains.
- Partial progress in named, proved lemmas is the deliverable when the whole
  does not close. Do not restate the goal in a more provable form and present it
  as the result.

## 6. Acceptance criteria

| # | Criterion |
| - | --------- |
| 1 | `scripts/compile.sh -r r0053` reports 0 errors and 0 warnings other than `sorry` |
| 2 | the `sorry` count does not rise; it falls by 1 if and only if the root is genuinely proved |
| 3 | every new theorem's `#print axioms` shows no `sorryAx` |
| 4 | `A3StepDecidable.lean` is byte-identical to `main` |
| 5 | committed with `scripts/gitcp.sh` on branch `agent1`; the push step reporting "no tracking information" is expected — do not push |
| 6 | report written to `ScottDomains/reports/r0053-report-from-agent1-to-orchestrator-scotthomc-recursive.md` with `started:`/`finished:` frontmatter |

The report states, quantitatively: which of the two obligations closed, the Lean
statement of each new theorem, the axiom footprint of each, the build log path,
and — if the root is still open — the exact remaining goal and the reason it did
not close.
