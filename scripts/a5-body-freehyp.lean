/-!
Instrument 4 of the r0044 Class-2 vacuity sweep: the **free-hypothesis** detector.

This is the mechanism the r0044 plan names, and it is *not* what
`unusedArguments` catches. In `Effective.nonempty_effectivePresentation` the
hypothesis is used in the proof — it is simply free: `Classical.dec` fills
`EffectivePresentation`'s decidability fields, so every domain has one and any
theorem taking it as a hypothesis says no more than its hypothesis-free form.

Generalized: theorem `T` has an explicit binder `h : P`, and the package contains
a declaration `D` taking **no explicit arguments** whose conclusion unifies with
`P` — with every remaining metavariable either determined by that unification or
discharged by `synthInstance` **in `T`'s own local context**. Then `h` costs
nothing: `D` supplies it wherever `T` applies, and `T` is strictly weaker than
its hypothesis-free form.

Both halves matter. A head-constant match alone is far too loose — a first cut
scored 644 hits because `ScottDomains.Flat.instDomain` "provides" `Domain α` by
head symbol while proving it only at `Flat α`. Requiring `isDefEq` against the
actual binder type, in `T`'s context, with `T`'s own instances available for
synthesis, is what makes the test decisive rather than suggestive.

`Nonempty (P …)` is followed through to `P`, since a `Nonempty` provider is what
free inhabitation of a *structure* hypothesis looks like.

Two populations are reported separately, because they mean different things.

* **PROP** — explicit binders that are `Prop`s. A free one is a genuine vacuity
  candidate: the theorem is strictly weaker than its hypothesis-free form.
* **DATA** — explicit binders that are `Type`s. These are almost always ordinary
  universal quantifiers (`∀ f : ScottHom D D, …`) and inhabitability says nothing
  against them; `idHom` inhabits `ScottHom D D` without making one statement
  about all Scott-continuous maps vacuous. They are reported only because the
  `EffectivePresentation` case *is* of this shape — a `Type`-valued structure
  whose inhabitation is supposed to be a claim — so the population has to be
  looked at rather than filtered away. Every DATA row needs the question asked by
  hand: is inhabiting this structure supposed to cost something?

Lean's own auto-generated declarations (`.injEq`, `.sizeOf_spec`, equation
lemmas) are skipped: they are not statements anyone wrote.
-/

open Lean Elab Command Meta

private def a5InPkg (env : Environment) (n : Name) : Bool :=
  match env.const2ModIdx[n]? with
  | some i => (`ScottDomains).isPrefixOf env.header.moduleNames[i]!
  | none   => false

/-- Head constant of an expression, seeing through `Nonempty`. -/
private def a5Head (e : Expr) : Option Name :=
  match e.getAppFn with
  | .const n _ =>
      if n == ``Nonempty then (e.getAppArgs[0]!).getAppFn.constName? else some n
  | _ => none

/-- Can `provider` be applied, in the current local context, to produce something
defeq to `goal`? Instance-implicit holes are discharged with `synthInstance`;
every other hole must be determined by the unification itself. -/
private def a5Provides (provider : Name) (goal : Expr) : MetaM Bool := do
  try
    withNewMCtxDepth do
      let ci ← getConstInfo provider
      let lvls ← ci.levelParams.mapM fun _ => mkFreshLevelMVar
      let ty := ci.type.instantiateLevelParams ci.levelParams lvls
      -- Non-reducing on purpose. `forallMetaTelescopeReducing` unfolds a
      -- `Prop`-valued `def` in the conclusion into further binders, so a
      -- provider of `FixedPointOfCompactDeflationIsCompact α` presents its
      -- *unfolded* body and never matches a binder written at the folded name.
      let (mvars, bis, concl) ← forallMetaTelescope ty
      let concl := if concl.isAppOf ``Nonempty then concl.getAppArgs[0]! else concl
      let goal := if goal.isAppOf ``Nonempty then goal.getAppArgs[0]! else goal
      unless ← isDefEq concl goal do return false
      for (m, bi) in mvars.zip bis do
        if ← m.mvarId!.isAssigned then continue
        unless bi == .instImplicit do return false
        let mty ← instantiateMVars (← m.mvarId!.getType)
        if mty.hasExprMVar then return false
        match ← trySynthInstance mty with
        | .some val => unless ← isDefEq m val do return false
        | _ => return false
      return true
  catch _ => return false

run_cmd liftTermElabM do
  let env ← getEnv
  let mut pkgDecls : Array Name := #[]
  for (n, _) in env.constants.map₁.toList do
    if a5InPkg env n && !n.isInternal then
      pkgDecls := pkgDecls.push n
  pkgDecls := pkgDecls.qsort (fun a b => a.toString < b.toString)

  -- Candidate providers, bucketed by the head constant of their conclusion. No
  -- filter on the binders here: `a5Provides` is the gate, and it is the right
  -- one. An earlier version required zero explicit binders and so **missed the
  -- known case** — `Effective.nonempty_effectivePresentation` takes `α` as an
  -- explicit argument, and rejecting it made the instrument silent on
  -- `EffectivePresentation`, the very structure the plan cites. Unification
  -- assigns a type argument from the goal and leaves a *proof* argument
  -- unassigned, so `a5Provides` accepts the first and rejects the second
  -- without any binder-counting heuristic.
  let mut providers : Std.HashMap Name (Array Name) := {}
  for n in pkgDecls do
    if ← Batteries.Tactic.Lint.isAutoDecl n then continue
    let ci ← getConstInfo n
    let concl ← forallTelescope ci.type fun _ body => pure body
    if let some h := a5Head concl then
      if a5InPkg env h then
        providers := providers.insert h ((providers.getD h #[]).push n)

  IO.println s!"-- package declarations: {pkgDecls.size}"
  IO.println s!"-- constants with a candidate hypothesis-free provider: {providers.size}"
  IO.println "-- HIT <theorem> (<binder> : <head>) <= <provider that discharges it>"

  let mut nThm := 0
  let mut nBinder := 0
  let mut nProp := 0
  let mut nData := 0
  let mut dataRows : Array String := #[]
  for n in pkgDecls do
    let ci ← getConstInfo n
    unless ci matches .thmInfo _ do continue
    if ← Batteries.Tactic.Lint.isAutoDecl n then continue
    nThm := nThm + 1
    let (rows, k) ← forallTelescopeReducing ci.type fun args _ => do
      let mut rows : Array (Bool × Name × Name × Name) := #[]
      let mut k := 0
      for a in args do
        let ld ← a.fvarId!.getDecl
        unless ld.binderInfo == .default do continue
        let isP ← isProp ld.type
        unless isP || (← isType ld.type) do continue
        let some h := a5Head ld.type | continue
        let cands := providers.getD h #[]
        if cands.isEmpty then continue
        k := k + 1
        for p in cands do
          if p == n then continue
          if ← a5Provides p ld.type then
            rows := rows.push (isP, ld.userName, h, p)
            break
      pure (rows, k)
    nBinder := nBinder + k
    for (isP, bn, h, p) in rows do
      if isP then
        nProp := nProp + 1
        IO.println s!"PROP {n}  ({bn} : {h})  <=  {p}"
      else
        nData := nData + 1
        dataRows := dataRows.push s!"DATA {n}  ({bn} : {h})  <=  {p}"
  IO.println s!"\n-- DATA rows (Type-valued binders; usually ordinary quantifiers)"
  for r in dataRows do IO.println r
  IO.println s!"\n-- theorems scanned (auto-generated excluded): {nThm}"
  IO.println s!"-- explicit binders with a candidate provider: {nBinder}"
  IO.println s!"-- free PROP hypotheses: {nProp}"
  IO.println s!"-- free DATA binders:    {nData}"
