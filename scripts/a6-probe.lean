/-
a6-probe.lean — the debug companion to `a6-query.lean` (r0044, agent6).
`scripts/a6-env-scan.sh <out> scripts/a6-probe.lean` runs this instead of the
main query. It holds whatever question is currently open; each answer it
produced is recorded in the round's report rather than kept here.

Open question: does a `simp only [L]` that fires leave `L` in the proof term?
`Flat.pset_fcOfSet` (FlatPowerdomain.lean:846) is proved by
`simp only [mem_pset, fcOfSet]`, and `mem_pset` is `Iff.rfl`-proved, so it is
not a `rfl` theorem in `Meta.isRflTheorem`'s sense (that predicate tests `Eq`
only, SimpTheorems.lean:194). If `mem_pset` is absent from the proof term
anyway, then a zero reference count is NOT evidence that a tag never fired, and
the SIMP column of the main query has to be read with that caveat.
-/

open Lean Meta Elab Command

run_cmd Command.liftTermElabM do
  let env ← getEnv
  for n in [`ScottDomains.Flat.pset_fcOfSet, `ScottDomains.Flat.pset_fcBotPair,
            `ScottDomains.ClosureProperties.Powerdomain.pN_greatest] do
    match env.find? n with
    | none => IO.println s!"MISSING\t{n}"
    | some ci =>
      match ci.value? (allowOpaque := true) with
      | none => IO.println s!"NOVALUE\t{n}"
      | some v =>
        let used := v.getUsedConstants
        IO.println s!"USES\t{n}\t{used.size} constants"
        for c in used do
          if (`ScottDomains).isPrefixOf c then IO.println s!"  {n}\t{c}"
