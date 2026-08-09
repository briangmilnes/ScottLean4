/-!
r0044 / agent3 — Class 2 (vacuity) instrument, body.

This file is the *body* of the instrument; `scripts/a3-gen.sh` prepends the
`import` block (one line per module of the package, generated from the file
tree) and writes `scripts/a3-vacuity.lean`.  The split exists because a Lean
`import` block must be literal — the package root `ScottDomains.lean` imports
only Mathlib, so `import ScottDomains` loads none of our 1773 theorems, which is
why `#lint … in ScottDomains` reported "0 declarations".

# WHAT THIS INSTRUMENT DOES NOT MEASURE — read first

There are two distinct defects, and sections 1–3 below find only the first:

1. **hypothesis unused by the proof term.**  The proof as written never touches
   the binder.  Decidable by inspecting the term; sections 1 and 2 decide it.
2. **hypothesis used but unnecessary.**  The proof as written consumes the
   binder, yet a *different* proof of the same statement does not need it.  No
   inspection of the existing term can see this — only reproving can.

agent1's r0044 stream produced the standing counterexample: `Kleene.sSup_recoverAt`
consumed `[BoundedComplete β]`, so `unusedArguments` and section 1 both report it
clean, and agent1 nevertheless deleted the binder and reproved the statement from
`IsAlgebraic β`'s `directedOn_compactsBelow`, kernel-accepted at footprint
`[propext, Quot.sound]`.  That hypothesis was unnecessary and no term inspection
would ever have said so.

**Do not read a count from sections 1–3 as a count of unnecessary hypotheses.**
It is a count of unused ones — a strict subset.  Section 4 is a sound but
*partial* attack on the second defect: it flags an instance binder that the
remaining binders already synthesize, which is unnecessary regardless of what the
proof does with it.  Everything outside section 4's reach — a hypothesis
removable only by finding a new argument — remains unmeasured by this instrument
and by any instrument in this round.

# What it measures

For every non-auto declaration whose defining module passes the filter, it takes
the type's `forallTelescope` and computes, per binder, two independent bits:

* **in the statement** — the binder's free variable occurs in the conclusion or
  in the type (or let-value) of another binder.  Note that a `Prop` binder can
  essentially never satisfy this, since proof terms do not appear in statements;
  that is why the two report sections below are split by `Prop` vs data.
* **in the proof** — the binder's free variable occurs in `(val args).headBeta`,
  the proof/definition term applied to the telescope.  This is the same
  computation Batteries' `unusedArguments` linter performs.

Two report sections follow:

1. **DEAD** — binder in neither.  The declaration elaborates verbatim with the
   binder deleted, so it is strictly weaker than the same statement without it.
   Reported for `Prop` and data binders alike.
2. **INVISIBLE DATA** — the declaration is a *theorem*, and the binder is data
   (its type is not a `Prop`), occurs in the proof, but occurs nowhere in the
   statement.  Such a theorem has the form
   `∀ (h : T), Q` with `h ∉ Q`, so it is exactly as strong as `Q` whenever `T`
   is inhabited for every instantiation of the ambient binders.  This is the
   `EffectivePresentation` shape.  The restriction to theorems is not a
   convenience: for a `def`, the "conclusion" is the result type, and an
   argument that does not occur in the result type is the ordinary case
   (`def f (n : ℕ) : Set ℕ`), so including `def`s makes the section 90 rows of
   noise in this area alone.  Inhabitedness is *not* decided here — the
   section is a candidate list, and the histogram of binder-type head constants
   printed with it is the short list a human must settle one entry at a time.
3. **DATA STRUCTURE CENSUS** — every `structure`/`inductive`/`class` declared in
   a selected module whose sort is not `Prop`, with the number of theorem
   binders anywhere in the selected modules whose type has that head constant.
   This is the plan's method 3: a structure that is inhabited for *every*
   instantiation makes any theorem quantifying over it suspect, so this section
   is the enumeration one has to settle.  A `Prop`-valued class (`Domain`,
   `BoundedComplete`) is excluded, since it is an ordinary hypothesis and its
   inhabitedness is the mathematics, not an encoding artifact.
4. **REDUNDANT INSTANCE BINDERS** — an instance-implicit binder `[C x]` such that
   `synthInstance` produces a term of `C x` from the *other* binders alone, with
   `[C x]` erased from both the local context and the local instance set.  Such a
   binder is unnecessary whatever the proof does with it, so this section reaches
   defect 2 above, soundly but only where the missing argument is instance
   resolution rather than mathematics.  A hit here is a real redundancy; a miss
   is not evidence of anything.

# Why not Batteries' `unusedArguments`

`unusedArguments` exempts any binder whose user name begins with `_`.  Both
known instances in this package (`Effective.theorem7_strict`,
`Effective.operator_preserves_effectivePresentation`) name their dead hypotheses
`_d` and `_e`, so that linter reports them as clean.  Section 1 here applies no
such exemption; the `_`-prefixed binders are flagged with an `(underscored)`
marker instead, since the author's intent is evidence about the finding, not a
reason to suppress it.

# Filter

`A3_ARGS` holds a comma-separated list of module-name prefixes, e.g.
`ScottDomains.Effective,ScottDomains.Kleene`.  Empty means every module of the
package.  Prefixes are matched with `Name.isPrefixOf`, so
`ScottDomains.Effective` selects `ScottDomains.Effective.Powerset` and
`ScottDomains.Effective.FunctionSpace`.  A bare module name selects exactly that
module.
-/

open Lean Meta Elab Command

namespace A3Vacuity

/-- Parse `A3_ARGS` into a list of module-name prefixes. -/
def filters : IO (Array Name) := do
  let s := (← IO.getEnv "A3_ARGS").getD ""
  let parts := s.splitOn "," |>.map (·.trimAscii.toString) |>.filter (· ≠ "")
  return (parts.map (·.toName)).toArray

/-- The module a constant was declared in. -/
def moduleOf (env : Environment) (n : Name) : Name :=
  match env.const2ModIdx[n]? with
  | some idx => env.header.moduleNames[idx.toNat]!
  | none => .anonymous

/-- Does this module pass the filter? -/
def selected (fs : Array Name) (m : Name) : Bool :=
  if fs.isEmpty then (`ScottDomains).isPrefixOf m else fs.any (·.isPrefixOf m)

/-- Bracket a binder the way it is written in source. -/
def brackets : BinderInfo → String × String
  | .implicit => ("{", "}")
  | .strictImplicit => ("⦃", "⦄")
  | .instImplicit => ("[", "]")
  | .default => ("(", ")")

/-- One flagged binder. -/
structure Hit where
  decl : Name
  mod : Name
  line : Nat
  idx : Nat
  binder : MessageData
  headConst : Name
  underscored : Bool
  isThm : Bool

/-- The head constant of a binder type, used to build the histogram. -/
def headConstOf (e : Expr) : Name :=
  match e.getAppFn with
  | .const c _ => c
  | .sort _ => `Sort
  | _ => .anonymous

/-- The four per-declaration outputs: dead binders (§1), statement-invisible data
binders of theorems (§2), the head constants of every data binder of a theorem
(raw material for the §3 census), and instance binders the remaining context
already synthesizes (§4). -/
structure Out where
  dead : Array Hit := #[]
  invis : Array Hit := #[]
  heads : Array Name := #[]
  redundant : Array Hit := #[]
  /-- §4 control counters: instance binders examined, and of those, how many
  `synthInstance` recovers with the binder still in context.  The second is the
  positive control — if it were also 0 the §4 result would be a broken check
  rather than a measurement. -/
  instExamined : Nat := 0
  instControlOk : Nat := 0
  /-- §4 second control: with binder `i` erased, `synthInstance` is asked for the
  type of a *different* instance binder `j ≠ i` that is still in context.  That
  must succeed.  If it did not, the zero in §4 would be an artifact of the
  erased-context machinery rather than a property of the package. -/
  crossTried : Nat := 0
  crossOk : Nat := 0

/-- Analyse one declaration. -/
def analyze (declName : Name) : MetaM Out := do
  let env ← getEnv
  if env.isAutoDecl declName then return {}
  if ← isProjectionFn declName then return {}
  let info ← getConstInfo declName
  let ty := info.type
  let val? : Option Expr := match info with
    | .defnInfo v => some v.value
    | .thmInfo v => some v.value
    | _ => none
  let isThm := match info with | .thmInfo _ => true | _ => false
  let some val := val? | return {}
  if val.hasSorry || ty.hasSorry then return {}
  let line := (← findDeclarationRanges? declName).map (·.range.pos.line) |>.getD 0
  let mod := moduleOf env declName
  forallTelescope ty fun args concl => do
    let ldecls ← args.mapM fun a => a.fvarId!.getDecl
    -- occurrences in the proof term
    let usedVal := (collectFVars {} (mkAppN val args).headBeta).fvarSet
    -- occurrences anywhere in the statement: the conclusion and every binder type
    let mut stmt := concl
    for ldecl in ldecls do
      stmt := mkApp stmt ldecl.type
      if let some v := ldecl.value? then stmt := mkApp stmt v
    let usedStmt := (collectFVars {} stmt).fvarSet
    let lctx ← getLCtx
    let insts ← getLocalInstances
    let mut out : Out := {}
    for (ldecl, i) in ldecls.zipIdx do
      let (l, r) := brackets ldecl.binderInfo
      let name := ldecl.userName
      let msg ← addMessageContextFull m!"{l}{name} : {ldecl.type}{r}"
      let hit : Hit :=
        { decl := declName, mod := mod, line := line, idx := i + 1, binder := msg,
          headConst := headConstOf ldecl.type,
          underscored := name.toString.startsWith "_", isThm := isThm }
      let isPropBinder ← Meta.isProp ldecl.type
      if isThm && !isPropBinder then
        out := { out with heads := out.heads.push hit.headConst }
      -- §1 / §2: occurrence analysis
      if !usedStmt.contains ldecl.fvarId then
        if usedVal.contains ldecl.fvarId then
          if isThm && !isPropBinder then out := { out with invis := out.invis.push hit }
        else
          out := { out with dead := out.dead.push hit }
      -- §4: is this instance binder synthesizable from the rest of the context?
      if ldecl.binderInfo == .instImplicit && usedVal.contains ldecl.fvarId then
        out := { out with instExamined := out.instExamined + 1 }
        let control ← try (do let _ ← synthInstance ldecl.type; pure true) catch _ => pure false
        if control then out := { out with instControlOk := out.instControlOk + 1 }
        let lctx' := lctx.erase ldecl.fvarId
        let insts' := insts.filter fun li => li.fvar.fvarId! != ldecl.fvarId
        let ok ← withLCtx lctx' insts' do
          try
            let _ ← synthInstance ldecl.type
            pure true
          catch _ => pure false
        if ok then out := { out with redundant := out.redundant.push hit }
        -- second control: a still-present instance binder must remain synthesizable
        let other? := ldecls.find? fun d =>
          d.binderInfo == .instImplicit && d.fvarId != ldecl.fvarId
        if let some other := other? then
          out := { out with crossTried := out.crossTried + 1 }
          let okCross ← withLCtx lctx' insts' do
            try
              let _ ← synthInstance other.type
              pure true
            catch _ => pure false
          if okCross then out := { out with crossOk := out.crossOk + 1 }
    return out

def render (h : Hit) : MessageData :=
  m!"{h.mod}:{h.line}  {if h.isThm then "theorem" else "def"} {h.decl}  argument {h.idx}: {h.binder}" ++
    (if h.underscored then m!"  (underscored)" else m!"")

end A3Vacuity

open A3Vacuity in
run_cmd Command.liftTermElabM do
  let env ← getEnv
  let fs ← filters
  let mut names : Array Name := #[]
  for (n, _) in env.constants.map₁.toList do
    if selected fs (moduleOf env n) then names := names.push n
  names := names.qsort (·.toString < ·.toString)
  let mut dead : Array Hit := #[]
  let mut invis : Array Hit := #[]
  let mut redundant : Array Hit := #[]
  let mut heads : Std.HashMap Name Nat := {}
  let mut scanned : Nat := 0
  let mut examined : Nat := 0
  let mut controlOk : Nat := 0
  let mut crossTried : Nat := 0
  let mut crossOk : Nat := 0
  for n in names do
    if (← getEnv).isAutoDecl n then continue
    let o ← analyze n
    scanned := scanned + 1
    dead := dead ++ o.dead
    invis := invis ++ o.invis
    redundant := redundant ++ o.redundant
    examined := examined + o.instExamined
    controlOk := controlOk + o.instControlOk
    crossTried := crossTried + o.crossTried
    crossOk := crossOk + o.crossOk
    for c in o.heads do heads := heads.insert c ((heads.getD c 0) + 1)
  logInfo m!"### a3-vacuity"
  logInfo m!"filter: {if fs.isEmpty then #[`ScottDomains] else fs}"
  logInfo m!"constants in filtered modules: {names.size}"
  logInfo m!"declarations analysed (auto-generated excluded): {scanned}"
  logInfo m!"NOTE: sections 1-3 measure hypotheses UNUSED by the proof term."
  logInfo m!"      A hypothesis that is used but unnecessary is invisible to them;"
  logInfo m!"      section 4 reaches that class only where instance resolution closes the gap."
  logInfo m!"--- SECTION 1: DEAD binders (in neither statement nor proof): {dead.size}"
  for h in dead do logInfo (render h)
  logInfo m!"--- SECTION 2: statement-invisible DATA binders of theorems (used in proof only): {invis.size}"
  let mut hist : Std.HashMap Name Nat := {}
  for h in invis do hist := hist.insert h.headConst ((hist.getD h.headConst 0) + 1)
  let rows := hist.toList.toArray.qsort (fun a b => a.2 > b.2)
  logInfo m!"histogram of binder-type head constants ({rows.size} distinct):"
  for (c, k) in rows do logInfo m!"  {k}\t{c}"
  logInfo m!"per-declaration:"
  for h in invis do logInfo (render h)
  -- §3: data structures declared in the selected modules
  let mut census : Array (Name × Nat) := #[]
  for n in names do
    match (← getEnv).find? n with
    | some (.inductInfo _) =>
      if (← getEnv).isAutoDecl n then pure () else
      let isPropSort ← forallTelescope ((← getConstInfo n).type) fun _ s => do
        match ← whnf s with
        | .sort l => pure (l == Level.zero)
        | _ => pure false
      if !isPropSort then census := census.push (n, heads.getD n 0)
    | _ => pure ()
  logInfo m!"--- SECTION 3: data structures/inductives declared here ({census.size}), \
    with the number of theorem data-binders of that type:"
  for (c, k) in census.qsort (fun a b => a.2 > b.2) do logInfo m!"  {k}\t{c}"
  logInfo m!"--- SECTION 4: instance binders synthesizable from the remaining context: {redundant.size}"
  logInfo m!"control: {examined} instance binders examined; \
    {controlOk} recovered by synthInstance WITH the binder in context \
    (this is the positive control — a low number here means the check is broken, \
    not that the package is clean)"
  logInfo m!"control 2 (erased context still resolves): {crossOk} of {crossTried} \
    other instance binders still synthesizable after the erasure"
  for h in redundant do logInfo (render h)
