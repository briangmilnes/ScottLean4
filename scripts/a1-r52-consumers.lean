/- a1-r52-consumers.lean — body for `scripts/a6-env-scan.sh`: count the package
declarations that take one of round r0052's open claims as a hypothesis and that
could therefore now be made unconditional by applying a sorried root.

r0052 sorries two root statements and deliberately leaves every consumer
conditional: a theorem that silently routes through `sorryAx` is exactly what the
`Prop`-valued-`def` convention existed to prevent. This measures the size of what
was declined, so the report states it as a number rather than an impression.

A declaration counts once, however many of the claims it assumes. The claim set
is the eight open claims plus their r0050 aliases; all eight are derivable from
the two sorried roots by reductions already proved in the package
(`theorem_29_secondAtDomains_of_thm29Normal`, `lemma_30_atV_of_thm29Normal`,
`lemma_30_arrow_of_lemma30AtV`, `stepFunctionsDecidable_of_scottHomC`,
`theorem_7_arrowRecursive_of_scottHomC`) except the two strict ones, whose own
root `StrictHomCRecursive` is not sorried — those are reported separately.

Output:
    CONSUMER <name> <claim>      one line per (declaration, claim assumed) pair
    CONSUMERCOUNT <n>            distinct declarations
-/

open Lean Meta Elab Command

namespace A1R52

def isPkgModule (m : Name) : Bool :=
  m == `ScottDomains || (`ScottDomains).isPrefixOf m

def claims : Array Name :=
  #[`ScottDomains.LemThirty.Theorem29Normal, `ScottDomains.LemThirty.Thm29Normal,
    `ScottDomains.LemThirty.Theorem29SecondAtDomains,
    `ScottDomains.LemThirty.Thm29SecondAtDomains,
    `ScottDomains.LemThirty.Lemma30AtV,
    `ScottDomains.Colimit.Lemma30Arrow, `ScottDomains.Colimit.Lem30Arrow,
    `ScottDomains.R49.Agent3.ScottHomCRecursive,
    `ScottDomains.Effective.StepFunctionsDecidable,
    `ScottDomains.Effective.Theorem7ArrowRecursive,
    `ScottDomains.Effective.Theorem7StrictRecursive,
    `ScottDomains.R49.Agent3.StrictStepFunctionsDecidable,
    `ScottDomains.R49.Agent3.StrictHomCRecursive]

def conclHead (t : Expr) : MetaM (Option Name) :=
  forallTelescope t fun _ body => do
    match body.getAppFn with
    | .const n _ => return some n
    | _          => return none

def hypHeads (t : Expr) : MetaM (Array Name) :=
  forallTelescope t fun xs _ => do
    let mut acc : Array Name := #[]
    for x in xs do
      if let some h ← conclHead (← inferType x) then acc := acc.push h
    return acc

run_cmd liftTermElabM do
  let env ← getEnv
  let mut n := 0
  for (nm, ci) in env.constants.toList do
    let some m := env.getModuleFor? nm | continue
    unless isPkgModule m do continue
    if nm.isInternal then continue
    let hs ← hypHeads ci.type
    let hit := claims.filter hs.contains
    if hit.isEmpty then continue
    n := n + 1
    for c in hit do
      IO.println s!"CONSUMER\t{nm}\t{c}"
  IO.println s!"CONSUMERCOUNT\t{n}"

end A1R52
