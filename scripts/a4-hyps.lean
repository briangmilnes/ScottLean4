/-
a4-hyps.lean — r0044 Class 2 instrument, part B: the *semantic* half of the
vacuity sweep.

`#lint only unusedArguments` (part A, run by `scripts/a4-lint.sh`) reports a
hypothesis that occurs in neither the statement nor the proof term.  It therefore
misses the `EffectivePresentation` mechanism entirely, where the hypothesis *is*
used and the defect is that every object of the ambient context satisfies it.
This file asks the two questions `unusedArguments` cannot.

**Q1 — EMPTY-HYPOTHESIS.**  For every `theorem` in agent4's area and every `Prop`
binder `h : P` of it, is `P` provable outright in the context of the binders that
precede it?  The test runs Lean's `trivial` tactic (which tries `rfl`,
`assumption`, `trivial`, `And.intro`, `decide`) on a fresh metavariable of type
`P` in that context.  If it closes, `h` carries no information and the theorem is
unconditional in `h` — the vacuity shape, and a *sound* verdict: the tactic
produced a proof term.  A failure is not a verdict of non-triviality, only of
non-triviality-by-`trivial`, so the instrument under-reports and never
over-reports.  That asymmetry is the one the plan asks for: a false positive here
would impugn an `S+P` row.

**Q2 — CLASS CENSUS.**  Free inhabitability is a property of a *class*, not of
each theorem that quantifies over it, so the expensive question ("is an instance
derivable for every object of the ambient context?") is asked once per class.
This prints the multiset of classes appearing in instance-implicit position, so
the census can be decided class-by-class by `scripts/a4-freeclass.lean`.

A third figure, NOT-IN-CONCLUSION, was measured and is **not** reported as a
defect signal: a `Prop` hypothesis is absent from the conclusion in the normal
case, by proof irrelevance, so the count (230 of 427 theorems) is noise.  It is
retained only for instance binders, where absence from the whole type is at least
suggestive.

Run with `scripts/a4-run-hyps.sh`.  Cost: one `trivial` invocation per `Prop`
binder; ~1.4e3 binders over the area's 427 theorems.
-/
open Lean Meta Elab Command Term Tactic

namespace A4

/-- The modules of agent4's r0044 area, as module names. -/
def areaModules : Array Name := #[
  `ScottDomains.Flat, `ScottDomains.FlatOmega, `ScottDomains.FlatPowerdomain,
  `ScottDomains.FlatSection6,
  `ScottDomains.Powerdomain.BoundedComplete, `ScottDomains.Powerdomain.Hoare,
  `ScottDomains.Powerdomain.Plotkin, `ScottDomains.Powerdomain.Smyth,
  `ScottDomains.Powerdomain.Universal,
  `ScottDomains.PowerdomainCompacts, `ScottDomains.PowerdomainMap,
  `ScottDomains.PowerdomainMapRep, `ScottDomains.ContinuousAlgebra,
  `ScottDomains.ClosureProperties.Powerdomain, `ScottDomains.Audit.Powerdomains,
  `ScottDomains.Powerset ]

/-- Declarations of the environment that live in one of `areaModules`. -/
def areaDecls : CoreM (Array (Name × Name)) := do
  let env ← getEnv
  let mut out := #[]
  for (n, _) in env.constants.map₁.toList do
    if n.isInternalDetail then continue
    match env.const2ModIdx[n]? with
    | none => pure ()
    | some idx =>
      let m := env.header.moduleNames[idx.toNat]!
      if areaModules.contains m then out := out.push (m, n)
  return out.qsort (fun a b => a.1.toString ++ "::" ++ a.2.toString
                             < b.1.toString ++ "::" ++ b.2.toString)

/-- Head constant of an expression, if any. -/
def headConst (e : Expr) : Option Name := e.getAppFn.constName?

/-- Can `goal` be synthesized as a typeclass instance in the current local
context?  Used to test an instance binder for *redundancy*: if the class is
derivable from the binders that precede it, the binder adds nothing, and this is
a decisive verdict — unlike `unusedArguments`, it fires even when the binder is
consumed by the proof term, because a synthesized instance can replace it. -/
def synthesizable (goal : Expr) : MetaM Bool := do
  try
    match ← trySynthInstance goal with
    | .some _ => return true
    | _ => return false
  catch _ => return false

/-- Can `goal` be closed by `trivial` in the current local context? -/
def closableByTrivial (goal : Expr) : TermElabM Bool :=
  withoutErrToSorry do
    try
      let mv ← mkFreshExprMVar goal
      let rest ← Tactic.run mv.mvarId! (evalTactic (← `(tactic| trivial)))
      return rest.isEmpty && !(← instantiateMVars mv).hasSorry
    catch _ => return false

/-- For one declaration: the `Prop` binders closable by `trivial`, and the classes
it quantifies over.

The `i`-th binder is tested in the local context of binders `0 … i-1` **only**.
Testing it in the full telescope is the mistake that makes this instrument
useless: `trivial` ends in `assumption`, and the binder is itself an assumption
there, so every hypothesis "closes" (measured: 267 of 427 theorems, i.e. noise). -/
def analyze (nm : Name) : TermElabM (Array String × Array Name) := do
  let info ← getConstInfo nm
  let arity ← forallTelescopeReducing info.type fun args _ => pure args.size
  let classes ← forallTelescopeReducing info.type fun args _ => do
    let mut cs := #[]
    for a in args do
      let ld ← a.fvarId!.getDecl
      if ld.binderInfo == .instImplicit then
        if let some c := headConst ld.type then cs := cs.push c
    return cs
  -- Instance binders that occur nowhere else in the *type*: deleting one leaves
  -- a well-formed statement, so the hypothesis survives deletion if and only if
  -- some proof exists without it.  This is the candidate set for the
  -- used-but-unnecessary class that `unusedArguments` cannot see (agent1's
  -- `Kleene.sSup_recoverAt` is the exemplar: consumed by the proof, removable by
  -- a different one).  Membership here is necessary, not sufficient — each
  -- candidate still has to be reproved to be decided.
  let deletable ← forallTelescopeReducing info.type fun args concl => do
    let mut used := (collectFVars {} concl).fvarSet
    for a in args do
      let ld ← a.fvarId!.getDecl
      for f in (collectFVars {} ld.type).fvarSet do used := used.insert f
    let mut ds := #[]
    for a in args do
      let ld ← a.fvarId!.getDecl
      if ld.binderInfo == .instImplicit && !used.contains a.fvarId! then
        ds := ds.push s!"    DELETABLE-FROM-STATEMENT [inst] : {← ppExpr ld.type}"
    return ds
  -- Control for `#lint`'s blind spot: Batteries' `unusedArguments` exempts any
  -- binder whose user name begins with `_`, so a dead hypothesis named `_d` is
  -- reported clean.  Counting them here says how much of the area that
  -- exemption can hide.
  let underscored ← forallTelescopeReducing info.type fun args _ => do
    let mut k := 0
    for a in args do
      let ld ← a.fvarId!.getDecl
      if ld.userName.toString.startsWith "_" && !ld.userName.isInternalDetail then
        k := k + 1
    return k
  if underscored > 0 then
    logInfo s!"  UNDERSCORED-BINDERS {underscored} in {nm}"
  let mut msgs := deletable
  for i in [:arity] do
    let m ← forallBoundedTelescope info.type (some i) fun _ body => do
      match ← whnf body with
      | .forallE bn dom _ bi =>
        if bi == .instImplicit then
          if ← synthesizable dom then
            return some s!"    REDUNDANT-INSTANCE {bn} : {← ppExpr dom}"
          return none
        if ← Meta.isProp dom then
          if ← closableByTrivial dom then
            return some s!"    EMPTY-HYPOTHESIS {bn} : {← ppExpr dom}"
        return none
      | _ => return none
    if let some s := m then msgs := msgs.push s
  return (msgs, classes)

end A4

open A4 in
run_cmd do
  let decls ← liftCoreM areaDecls
  let mut census : Std.HashMap Name Nat := {}
  let mut hits := 0
  let mut total := 0
  let mut lines : Array String := #[]
  for (m, n) in decls do
    let some info := (← getEnv).find? n | continue
    unless info matches .thmInfo _ do continue
    total := total + 1
    let (triv, classes) ← liftTermElabM (analyze n)
    for c in classes do census := census.insert c ((census.getD c 0) + 1)
    if triv.size > 0 then
      hits := hits + 1
      lines := lines.push s!"  {m} :: {n}"
      lines := lines ++ triv
  logInfo s!"=== A4 hypothesis findings: {hits} of {total} theorems in the area ==="
  for l in lines do logInfo l
  let cen := census.toList.toArray.qsort (fun a b => a.2 > b.2)
  logInfo "=== A4 CLASS CENSUS (uses in the area / registered instances package-wide) ==="
  -- A class with *no* instance is unfalsifiable: every theorem quantified over it
  -- is unexercised, and an error in the class or in what consumes it would go
  -- undetected. `Atomless.lean:653` states the convention; this measures it.
  for (c, k) in cen do
    let insts ← liftCoreM (do
      let env ← getEnv
      let all := (Lean.Meta.instanceExtension.getState env).instanceNames
      let mut n := 0
      for (nm, _) in all.toList do
        if let some ci := env.find? nm then
          if (← Lean.Meta.MetaM.run' (Lean.Meta.forallTelescopeReducing ci.type
                fun _ b => pure (b.getAppFn.constName? == some c))) then n := n + 1
      pure n)
    logInfo s!"  uses {k}\tinstances {insts}\t{c}"
