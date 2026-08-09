/-!
Instrument 1 of the r0044 Class-2 vacuity sweep: Batteries' `unusedArguments`
environment linter, run over every declaration in the `ScottDomains` package.

The linter's test, from `Batteries/Tactic/Lint/Misc.lean:31`, is hypothesis
deletion done semantically. It opens the declaration's type with
`forallTelescope`, applies the stored value — for a `theorem`, the proof term —
to all the binders, appends the conclusion type and every binder's type and
let-value, and collects the free variables of that single expression. A binder
whose fvar does not occur is used neither in the proof, nor in the conclusion,
nor in any other hypothesis's type. That is a *proof* of term-level
removability, not a heuristic: the same term typechecks with the binder gone.

Two limits, both load-bearing for how the result may be read.

1. It measures **unused by the current proof**, not **unnecessary**. A hypothesis
   the proof does consume may still be removable by a different proof; this
   linter is blind to that class by construction.
2. It **exempts binders whose user name is internal**, which includes the
   `_`-prefixed convention (`!ldecl.userName.isInternal`, line 57). So `(_h : P)`
   is never reported however dead it is. The exemption makes the linter
   under-report, never over-report.

Run with: scripts/a5-lint.sh
-/

open Batteries.Tactic.Lint

#lint only unusedArguments in ScottDomains
