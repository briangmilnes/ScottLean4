/-
r0044 / agent3 — diagnostic for instrument 1.

`#lint only unusedArguments in ScottDomains` reported "0 errors in 0
declarations", i.e. `Batteries.Tactic.Lint.getDeclsInPackage` selected an empty
declaration set.  This file checks, separately, (a) how many imported modules
carry the `ScottDomains` prefix and (b) how many imported constants
`Environment.const2ModIdx` maps into them, so the negative result above can be
attributed to the right cause.
-/
import ScottDomains

open Lean

run_cmd do
  let env ← Lean.getEnv
  let mods := env.header.moduleNames
  let ours := mods.filter (`ScottDomains).isPrefixOf
  Lean.logInfo m!"imported modules total: {mods.size}"
  Lean.logInfo m!"imported modules with prefix ScottDomains: {ours.size}"
  let mut imported : Nat := 0
  let mut inOurs : Nat := 0
  let mut noIdx : Nat := 0
  for (declName, _) in env.constants.map₁.toList do
    imported := imported + 1
    match env.const2ModIdx[declName]? with
    | none => noIdx := noIdx + 1
    | some idx =>
      if (`ScottDomains).isPrefixOf mods[idx.toNat]! then inOurs := inOurs + 1
  Lean.logInfo m!"imported constants: {imported}"
  Lean.logInfo m!"…with no const2ModIdx entry: {noIdx}"
  Lean.logInfo m!"…mapped into a ScottDomains module: {inOurs}"
  let local2 : Nat := env.constants.map₂.toList.length
  Lean.logInfo m!"constants in current module (map₂): {local2}"
  let sample := ours.toList.take 5
  Lean.logInfo m!"first ScottDomains module names: {sample}"
