/-!
Instrument 3 of the r0044 Class-2 vacuity sweep: the structure census.

Enumerates, from the *built environment* rather than from source text, every
`structure` and `class` declared in the `ScottDomains` package, with its
parameter telescope and its field types. A structure that `Classical.dec` — or
any other free construction — inhabits for every type makes every theorem
quantifying over it uninformative; `EffectivePresentation` is the known case, and
its `decidableLE` / `decidableNormal` fields are what make it one. The field
types decide the question, and they must be read off the elaborated declaration,
not off the `structure` line.

Reading from the environment also answers a second question: how many structures
a column-0 `grep '^structure'` misses.

Run with: scripts/a5-lint.sh scripts/a5-structures.lean
-/

open Lean Elab Command Meta

-- Print every structure/class declared in a module whose name starts with
-- `ScottDomains`, with its parameters and its field types. A `/-- … -/` doc
-- comment cannot be attached to `run_cmd`, so this is a line comment.
run_cmd liftTermElabM do
  let env ← getEnv
  let mods := env.header.moduleNames
  let mut names : Array Name := #[]
  for (n, _) in env.constants.map₁.toList do
    if let some i := env.const2ModIdx[n]? then
      if (`ScottDomains).isPrefixOf mods[i]! then
        if isStructure env n then
          names := names.push n
  names := names.qsort (fun a b => a.toString < b.toString)
  IO.println s!"-- structures/classes in package ScottDomains: {names.size}"
  for n in names do
    let ci ← getConstInfo n
    let kind := if isClass env n then "class" else "structure"
    IO.println s!"\n### {kind} {n}"
    IO.println s!"    type: {← Meta.ppExpr ci.type}"
    for f in getStructureFields env n do
      let some proj := getProjFnForField? env n f | continue
      let pci ← getConstInfo proj
      IO.println s!"    field {f} : {← Meta.ppExpr pci.type}"
