/-! r0046 / agent5 — diagnostic for the dependency probe. Decides WHY
`ConstantInfo.value?` returned `none` for an imported theorem, and whether an
async-aware lookup recovers the proof term. -/

open Lean

def ctorName : ConstantInfo → String
  | .axiomInfo _  => "axiomInfo"
  | .defnInfo _   => "defnInfo"
  | .thmInfo _    => "thmInfo"
  | .opaqueInfo _ => "opaqueInfo"
  | .quotInfo _   => "quotInfo"
  | .inductInfo _ => "inductInfo"
  | .ctorInfo _   => "ctorInfo"
  | .recInfo _    => "recInfo"

#eval show CoreM Unit from do
  let env ← getEnv
  for n in [`ScottDomains.R45.Agent4.smythImageIso,
            `ScottDomains.R45.Agent4.nonempty_orderIso_range_of_section,
            `ScottDomains.Kleene.recoverAt] do
    match env.find? n with
    | none => IO.println s!"{n}: NOT FOUND"
    | some ci => IO.println s!"{n}: {ctorName ci}, value? = {ci.value?.isSome}"

-- The async-aware lookup: `getConstInfo` goes through `MonadEnv` and awaits.
#eval show CoreM Unit from do
  let ci ← getConstInfo `ScottDomains.R45.Agent4.smythImageIso
  IO.println s!"getConstInfo: {ctorName ci}, value? = {ci.value?.isSome}"

-- Direct theorem-value access, if `thmInfo` is what we have.
#eval show CoreM Unit from do
  let env ← getEnv
  match env.find? `ScottDomains.R45.Agent4.smythImageIso with
  | some (.thmInfo v) =>
      IO.println s!"thmInfo.value used constants: {v.value.getUsedConstants.size}"
  | some ci => IO.println s!"not a thmInfo: {ctorName ci}"
  | none => IO.println "not found"
