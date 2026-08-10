/- a1-r52-sorry-cone.lean — body for `scripts/a6-env-scan.sh`: print every package
constant that depends on `sorryAx`, directly or transitively.

`a6-query.lean`'s `SORRYUSER` record is a *direct* test — it reports a constant
whose own type or value names `sorryAx`. Round r0052 needs the transitive cone
instead, because the property to check is "no pre-existing theorem's axiom
footprint changed": a consumer that got rewired to apply a sorried root would
name the root, not `sorryAx`, and the direct test would miss it.

The closure runs over package constants only. Mathlib is elaborated before the
package and cannot name a package constant, so nothing outside `ScottDomains` can
enter the cone. Iterating to a fixpoint costs one pass per level of the cone.

Output:
    SORRYCONE <name>       one line per constant depending on sorryAx
    SORRYCONECOUNT <n>
-/

open Lean Meta Elab Command

namespace A1R52

def isPkgModule (m : Name) : Bool :=
  m == `ScottDomains || (`ScottDomains).isPrefixOf m

/-- Every constant name occurring in `ci`'s type or value. -/
def usedBy (ci : ConstantInfo) : Array Name :=
  let fromType := ci.type.getUsedConstants
  match ci.value? (allowOpaque := true) with
  | some v => fromType ++ v.getUsedConstants
  | none   => fromType

run_cmd do
  let env ← getEnv
  -- The package's own constants, paired with the names each one mentions.
  let mut rows : Array (Name × Array Name) := #[]
  for (n, ci) in env.constants.toList do
    let some m := env.getModuleFor? n | continue
    unless isPkgModule m do continue
    rows := rows.push (n, usedBy ci)
  let mut cone : Std.HashSet Name := ({} : Std.HashSet Name).insert ``sorryAx
  let mut changed := true
  while changed do
    changed := false
    for (n, us) in rows do
      if cone.contains n then continue
      if us.any cone.contains then
        cone := cone.insert n
        changed := true
  let names := (cone.toList.filter (· != ``sorryAx)).toArray.qsort (·.lt ·)
  for n in names do
    IO.println s!"SORRYCONE\t{n}"
  IO.println s!"SORRYCONECOUNT\t{names.size}"

end A1R52
