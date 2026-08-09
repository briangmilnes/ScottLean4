/-
a4-verify-claims.lean — r0046 agent4: check every sentence the sweep flagged, and
every sentence the corrections will assert, against the BUILT environment.

Run with the same driver as the declaration dump:

    scripts/a6-env-scan.sh <out> scripts/a4-verify-claims.lean

The round's evidence rule is that a correction is checked against the `.olean`,
never against a source line. `#check` is that check: it elaborates the constant's
type in the environment the kernel actually accepted, so a name that has been
renamed, a binder that has been added, or a conclusion that differs from what the
docstring says all show up here and nowhere in a grep.
-/

open Lean Meta Elab Command

run_cmd Command.liftTermElabM do
  let env ← getEnv
  -- Lemma 28's nine conjuncts: does a generic scheme exist for each operator?
  let schemes : Array Name := #[
    `ScottDomains.PRepFun.rep_arrow, `ScottDomains.PRepFun.rep_strictArrow,
    `ScottDomains.PRep.rep_prod, `ScottDomains.PRepFun.rep_smash,
    `ScottDomains.PRepSum.rep_sepSum, `ScottDomains.PRepSum.rep_coalSum,
    `ScottDomains.PRep.rep_lift, `ScottDomains.R45.Agent4.rep_smyth,
    `ScottDomains.R45.Agent4.rep_hoare]
  IO.println "=== Lemma 28's nine schemes ==="
  for n in schemes do
    match env.find? n with
    | none => IO.println s!"MISSING\t{n}"
    | some ci => IO.println s!"OK\t{n}\t: {← ppExpr ci.type}"
  -- The claims the sweep flagged, and the declarations that bear on them.
  let others : Array Name := #[
    `ScottDomains.R45.Agent4.lemma28AtU,
    `ScottDomains.PRep.Lemma28AtU,
    `ScottDomains.R45.Agent3.not_thm29Second,
    `ScottDomains.Colimit.Thm29Second,
    `ScottDomains.LemThirty.thm29SecondAtDomains_of_thm29Normal,
    `ScottDomains.R45.Agent3.not_thm29NormalWithoutDomain,
    `ScottDomains.PRepFun.strictHomDomain,
    `ScottDomains.PRepFun.smashDomain,
    `ScottDomains.PowerdomainMap.map,
    `ScottDomains.PowerdomainMap.exists_unique_map]
  IO.println "=== declarations the corrections cite ==="
  for n in others do
    match env.find? n with
    | none => IO.println s!"MISSING\t{n}"
    | some ci => IO.println s!"OK\t{n}\t: {← ppExpr ci.type}"
