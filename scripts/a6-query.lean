/-
a6-query.lean — the body of round r0044's Class-3 instrument (agent6).

This file is NOT a package module: it lives in `scripts/`, outside
`ScottDomains/ScottDomains/`, so it is invisible to `lake build`, to
`scripts/counts.sh` and to the 100-module / 37300-line / 1773-theorem metrics.
`scripts/a6-env-scan.sh` prepends one `import` line per package module and runs
the result under `lake env lean`.

Why the Lean environment and not grep. The question "is this `def` a stated
claim?" is the question "does its type, after stripping binders, end in `Prop`?",
and that is a property of the *elaborated* type: `def StepFunctionsDecidable … :
Prop := IsRecursive (scottHom d e)` is visible to a regex only because the token
`Prop` happens to be written, and `def Flat.le … := …` with an inferred
Prop-valued result is not visible at all. The follow-on question — "did anybody
discharge it?" — is not lexical under any reading: it asks whether some theorem
in the package has this definition as its conclusion. r0044's evidence rule
(check the built `.olean`, not a source line) is exactly this.

The decisive test for an undischarged claim:

    D is discharged  ⟺  some package theorem's type, after stripping every
                        leading binder, is headed by the constant D.

`sorry` cannot see the failure of that test, because a `def` carries no proof
obligation at all — a definition always elaborates.

Auto-generated declarations (`.mk`, `.rec`, `.injEq`, `.eq_def`, equation
lemmas, …) are excluded from every reference count. Counting them made every
structure look instantiated and every definition look consumed.

Output is one tab-separated record per line, tagged so the shell can split the
streams:

  PROPDEF <module> <line> <name> <binders> <refs> <proofs> <uncond> <hyps> <refuted>
      a `def`/`abbrev` whose type ends in `Prop`. `refs` counts source-level
      package constants whose type or value mentions it; `proofs` counts package
      theorems whose conclusion is headed by it, `uncond` the subset of those
      carrying no proof hypothesis — `uncond 0` is undischarged; `hyps` counts
      package constants taking something headed by it as a hypothesis; `refuted`
      counts closed refutations (see REFUTEDBY).
  PROVEDBY <propdef> <theorem> <propHypotheses> <generic>
      one line per theorem concluding a Prop-valued package definition, so every
      discharge claim in the report can be checked by name. `generic` is true
      when the conclusion applies the definition to pairwise-distinct binders of
      the theorem itself — the universal closure — and false when some argument
      is a particular value or repeats another. Added in r0046 (agent1): the
      `uncond` test above scores `preservesRecursivePresentation_id :
      PreservesRecursivePresentation α d e` as an unconditional discharge, and it
      is the schema at `γ := α`, which is r0044's dominant defect mode. This
      field measures that rather than leaving it to a reader.
  REFUTEDBY <propdef> <theorem>
      one line per *closed refutation* of a Prop-valued package definition: a
      theorem with no binders at all whose type is `¬ e`, where `e` after
      stripping binders is headed by that definition. Added in r0046 (agent1)
      because the `uncond 0` test above scores a refuted claim as undischarged: a
      refutation produces `¬ D`, whose conclusion is headed by `Not`, so it never
      increments `proofs`. Three of the ten claims r0045 left on the list —
      `Colimit.Thm29Second`, `PRep.Lemma28`, `LemThirty.Lemma30` — are refuted,
      not open, and without this record they inflate the count forever.

      Why the criterion is exactly "no binders, conclusion `¬ e`". Soundness:
      if `¬ e` holds and `e` is `∀ xs, hyps → D args`, then the universal closure
      of `D` fails, because that closure would give `D args` for every `args` and
      hence `e`. Both a refutation of an *instance* (`¬ D c`) and a refutation of
      a *weakened* form (`¬ ∀ U, Domain U → D U`) are therefore sound witnesses,
      and both occur in this package. Requiring zero binders is what rules out
      the unsound reading: `[Subsingleton U] → ¬ D U` refutes nothing about `D`
      until some `U` is exhibited, and `ScottDomains.R45.Agent2` contains exactly
      that theorem alongside the closed one.
  AXIOM <module> <line> <name>
      an `axiom` declaration in a package module.
  STRUCT <module> <line> <name> <ctorRefs> <fields> <propFields>
      a structure or class. `ctorRefs` counts source-level package constants
      mentioning its constructor, so `ctorRefs 0` means nothing in the package
      ever instantiates it and every obligation in its `propFields` fields stays
      undischarged.
  SORRYUSER <name>
      a package constant mentioning `sorryAx` directly, cross-checking
      `counts.sh`'s lexical `sorry` count.

  A theorem whose axiom footprint contains `sorryAx` is EXCLUDED from `proofs`,
  `uncond`, `PROVEDBY`, `refuted` and `REFUTEDBY` (r0052, agent1). It proves
  nothing, so counting it as a discharge is the same defect class the `uncond`
  and `REFUTEDBY` notes above describe. Before r0052 the package held no `sorry`
  and the case never arose; r0052 states each unproved result as a `theorem …
  := sorry`, and without this exclusion each such theorem removes its own claim
  from the undischarged list. The test is the TRANSITIVE footprint, not
  `SORRYUSER`'s direct one: a theorem applying a sorried root names the root and
  not `sorryAx`.
  SIMP <module> <line> <name> <valueRefs> <isRflTheorem>
      a package declaration carrying the `simp` attribute, with the number of
      OTHER package constants whose *proof term* mentions it. A `simp` call that
      rewrites with `L` puts `L` into the proof term it builds, so `valueRefs 0`
      means no proof in the package was built using `L` by any route — `simp`,
      `rw` or `exact`. That is a sound witness that the tag never fired, EXCEPT
      when `isRflTheorem` is true: a `rfl`-theorem may be applied on `simp`'s
      definitional (`dsimp`) path, which rewrites without building a proof term
      and so leaves no reference behind. The converse never holds: a nonzero
      count says the lemma was used, not that `simp` used it.
  TOTALS <constants> <sourceConstants> <defs> <theorems> <propDefs> <simpTagged>
-/

open Lean Meta Elab Command

namespace A6

/-- The package's own modules: `ScottDomains` and everything under it. -/
def isPkgModule (m : Name) : Bool :=
  m == `ScottDomains || (`ScottDomains).isPrefixOf m

/-- Suffixes Lean generates automatically for a declaration the user wrote. A
reference from one of these is not a use by the development. -/
def genSuffix : Array String :=
  #["mk", "rec", "recOn", "casesOn", "below", "brecOn", "binductionOn", "ndrec",
    "noConfusion", "noConfusionType", "injEq", "inj", "sizeOf_spec", "toCtorIdx",
    "eq_def", "ofNat", "ext", "ext_iff", "sizeOf_inst"]

/-- `eq_1`, `eq_2`, … — equation lemmas. Not `eq_of_le`, which a human wrote. -/
def isEqLemma (s : String) : Bool :=
  s.startsWith "eq_" && (s.drop 3).length > 0 && (s.drop 3).all Char.isDigit

partial def hasUnderscoreComponent : Name → Bool
  | .str p s => s.startsWith "_" || hasUnderscoreComponent p
  | .num p _ => hasUnderscoreComponent p
  | .anonymous => false

/-- Map an auxiliary declaration back to the declaration it was generated for:
`L._simp_1`, `L._simp_1_2`, `f._proof_1`, `f._eq_1` all become `L` / `f`.

This is load-bearing for every reference count. `simp` does not put the simp
lemma `L` into the proof term it builds; it puts `L._simp_1`, the `Eq`-form
auxiliary Lean derives from `L` when the tag is registered. Measured on
`Flat.pset_fcOfSet`, whose script is `simp only [mem_pset, fcOfSet]`: the term
names `Flat.mem_pset._simp_1` and `Flat.fcOfSet._proof_1`, and neither
`mem_pset` nor `fcOfSet`. Without this normalization the scan reported 92 of 194
`@[simp]` lemmas as never referenced, and `mem_pset` — which demonstrably fires
two lines below its own declaration — was one of them. -/
partial def normalizeRef : Name → Name
  | .str p s => if s.startsWith "_" then normalizeRef p else .str p s
  | n => n

def isGenerated (n : Name) : Bool :=
  if n.isInternal || hasUnderscoreComponent n then true
  else match n with
  | .str _ s => genSuffix.contains s || isEqLemma s
  | _ => false

/-- Does this type, after stripping every leading binder, end in `Prop`? -/
def resultIsProp (t : Expr) : MetaM Bool :=
  forallTelescope t fun _ body => do
    match body with
    | .sort .zero => return true
    | _           => return false

/-- The head constant of a type's conclusion, after stripping binders. -/
def conclHead (t : Expr) : MetaM (Option Name) :=
  forallTelescope t fun _ body => do
    match body.getAppFn with
    | .const n _ => return some n
    | _          => return none

/-- The head constants of every binder type of `t`. -/
def hypHeads (t : Expr) : MetaM (Array Name) :=
  forallTelescope t fun xs _ => do
    let mut acc : Array Name := #[]
    for x in xs do
      let ty ← inferType x
      if let some h ← conclHead ty then acc := acc.push h
    return acc

/-- Does this theorem conclude its claim at the *generic* instance — the claim
applied to pairwise-distinct binders of the theorem — rather than at particular
values? A theorem `D α d e` where the `γ` slot is filled by `α`, or by a closed
term such as `Flat ℕ`, proves an instance of the claim and not the claim; the
`uncond` test cannot see the difference because both conclusions are headed by
`D`. A definition with no arguments is generic vacuously, which is correct: a
closed `Prop` has only one instance. -/
def conclIsGeneric (t : Expr) : MetaM Bool :=
  forallTelescope t fun xs body => do
    let mut seen : Array FVarId := #[]
    for a in body.getAppArgs do
      let .fvar id := a | return false
      if seen.contains id then return false
      unless xs.any (fun x => x.fvarId! == id) do return false
      seen := seen.push id
    return true

/-- The claim a *closed refutation* refutes, if this type is one. `t` must be
literally `¬ e` with no leading binder; the answer is the head constant of `e`'s
conclusion. `forallTelescope` does not unfold `Not`, so a theorem of type `¬ D`
contributes `Not` — not `D` — to `conclHead` and therefore to `proofs`; that is
why a refuted claim reads as undischarged and why this record exists. -/
def refutedClaim (t : Expr) : MetaM (Option Name) := do
  match t.getAppFn, t.getAppArgs with
  | .const ``Not _, #[arg] => conclHead arg
  | _, _ => return none

/-- How many of `t`'s binders are proof hypotheses — binders whose own type is a
proposition, excluding instance-implicit binders, which carry structure rather
than an assumption. A theorem concluding `D` with a proof hypothesis has not
discharged `D`; it has reduced `D` to something else. `StepFunctionsDecidable`'s
`exists_isRecursive_of_stepFunctionsDecidable` is exactly that shape, and
counting it as a discharge would hide the gap this sweep exists to find. -/
def propHypCount (t : Expr) : MetaM Nat :=
  forallTelescope t fun xs _ => do
    let mut k := 0
    for x in xs do
      let d ← x.fvarId!.getDecl
      unless d.binderInfo == .instImplicit do
        if ← Meta.isProp d.type then k := k + 1
    return k

/-- The line the declaration's *name* sits on. `range.pos` would give the start
of its docstring instead — `StepFunctionsDecidable` reports 366 that way and 374
this way, and 374 is the `def`. -/
def lineOf (n : Name) : CoreM Nat := do
  match ← findDeclarationRanges? n with
  | some r => return r.selectionRange.pos.line
  | none   => return 0

/-- Every constant name occurring in `ci`'s type or value, unnormalized —
auxiliaries stay distinct, which is what the `sorryAx` closure below needs: a
parent references its own auxiliary, so the closure reaches it either way. -/
def usedNames (ci : ConstantInfo) : Array Name :=
  match ci.value? (allowOpaque := true) with
  | some v => ci.type.getUsedConstants ++ v.getUsedConstants
  | none   => ci.type.getUsedConstants

end A6

open A6 in
run_cmd Command.liftTermElabM do
  let env ← getEnv
  let mods := env.header.moduleNames
  -- Every package constant, and the subset a human actually wrote.
  let mut nPkg := 0
  let mut src : Array (Name × Name × ConstantInfo) := #[]
  let mut pkgUses : Array (Name × Array Name) := #[]
  for (n, ci) in env.constants.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let m := mods[idx]!
    unless isPkgModule m do continue
    nPkg := nPkg + 1
    pkgUses := pkgUses.push (n, usedNames ci)
    unless isGenerated n do src := src.push (n, m, ci)
  -- The transitive `sorryAx` cone (r0052, agent1). A theorem ending in `sorry`
  -- does not discharge a claim, and until r0052 nothing in this scan said so —
  -- there were no `sorry`s to catch. `theorem29Normal_unproven : Theorem29Normal
  -- := sorry` is an unconditional theorem concluding a claim, so it incremented
  -- `uncond` and the claim left the undischarged list. The test has to be the
  -- transitive footprint and not `used.contains sorryAx`: a theorem applying a
  -- sorried root names the root, not `sorryAx`.
  --
  -- Reverse reachability to a fixpoint, over package constants only. Mathlib is
  -- elaborated before the package and cannot name a package constant, so nothing
  -- outside `ScottDomains` can enter the cone; one pass per level of the cone.
  let mut sorryCone : Std.HashSet Name := ({} : Std.HashSet Name).insert ``sorryAx
  let mut growing := true
  while growing do
    growing := false
    for (n, us) in pkgUses do
      unless sorryCone.contains n do
        if us.any sorryCone.contains then
          sorryCone := sorryCone.insert n
          growing := true
  -- One pass over source constants: references, conclusions, hypotheses.
  let mut refs   : Std.HashMap Name Nat := {}
  -- References from proof/definition BODIES only. A `simp` lemma that fires is
  -- named in the term `simp` builds, so this is the map that answers "did this
  -- tag ever do any work?"; `refs` also counts mentions in a statement, which is
  -- not use.
  let mut valRefs : Std.HashMap Name Nat := {}
  let mut proofs : Std.HashMap Name Nat := {}
  let mut uncond : Std.HashMap Name Nat := {}
  let mut hyps   : Std.HashMap Name Nat := {}
  let mut refuted : Std.HashMap Name Nat := {}
  let mut conclusions : Array (Name × Name × Nat × Bool) := #[]
  let mut refutations : Array (Name × Name) := #[]
  let mut nDefs := 0
  let mut nThms := 0
  let mut propDefs : Array (Name × Name × ConstantInfo) := #[]
  for (n, m, ci) in src do
    let mut used : Std.HashSet Name := {}
    for c in ci.type.getUsedConstants do used := used.insert (normalizeRef c)
    -- `allowOpaque := true` is load-bearing: `ConstantInfo.value?` returns `none`
    -- for a theorem unless it is passed (Lean/Declaration.lean:485). Without it
    -- every reference occurring inside a *proof* is invisible, and since a
    -- Prop-valued class instance is a theorem, every such class then looks as if
    -- nothing ever instantiated it. The first run of this scan reported
    -- `ScottDomains.Domain` with 0 constructor references while the sources
    -- declare nine `instance … : Domain …`; that is what the flag fixes.
    if let some v := ci.value? (allowOpaque := true) then
      let mut inVal : Std.HashSet Name := {}
      for c0 in v.getUsedConstants do
        let c := normalizeRef c0
        used := used.insert c
        inVal := inVal.insert c
      for c in inVal do
        if c != n then valRefs := valRefs.insert c ((valRefs.getD c 0) + 1)
    if used.contains ``sorryAx then IO.println s!"SORRYUSER\t{n}"
    for c in used do
      if c != n then refs := refs.insert c ((refs.getD c 0) + 1)
    for h in ← hypHeads ci.type do
      if h != n then hyps := hyps.insert h ((hyps.getD h 0) + 1)
    match ci with
    | .axiomInfo _ => IO.println s!"AXIOM\t{m}\t{← lineOf n}\t{n}"
    | .thmInfo _   =>
        nThms := nThms + 1
        -- A theorem in the `sorryAx` cone proves nothing; it neither discharges a
        -- claim nor refutes one. Skipping it here keeps `proofs`, `uncond`,
        -- `PROVEDBY`, `refuted` and `REFUTEDBY` all measuring kernel-checked work.
        unless sorryCone.contains n do
          if let some c ← conclHead ci.type then
            if c != n then
              proofs := proofs.insert c ((proofs.getD c 0) + 1)
              let k ← propHypCount ci.type
              let g ← conclIsGeneric ci.type
              if k == 0 then uncond := uncond.insert c ((uncond.getD c 0) + 1)
              conclusions := conclusions.push (c, n, k, g)
          if let some c ← refutedClaim ci.type then
            if c != n then
              refuted := refuted.insert c ((refuted.getD c 0) + 1)
              refutations := refutations.push (c, n)
    | .defnInfo di =>
        nDefs := nDefs + 1
        if ← resultIsProp di.type then propDefs := propDefs.push (n, m, ci)
    | _ => pure ()
  let mut propNames : Std.HashSet Name := {}
  for (n, _, _) in propDefs do propNames := propNames.insert n
  for (n, m, ci) in propDefs do
    let nb ← forallTelescope ci.type fun xs _ => pure xs.size
    IO.println s!"PROPDEF\t{m}\t{← lineOf n}\t{n}\t{nb}\t{refs.getD n 0}\t{proofs.getD n 0}\t{uncond.getD n 0}\t{hyps.getD n 0}\t{refuted.getD n 0}"
  for (c, t, k, g) in conclusions do
    if propNames.contains c then IO.println s!"PROVEDBY\t{c}\t{t}\t{k}\t{g}"
  for (c, t) in refutations do
    if propNames.contains c then IO.println s!"REFUTEDBY\t{c}\t{t}"
  for (n, m, _) in src do
    if isStructure env n then
      let ctor := (getStructureCtor env n).name
      -- Lean 4.32 elaborates structure-instance notation through a "flat
      -- constructor" `S.mk._flat_ctor`, so a term built with `where`/`⟨…⟩` may
      -- mention that name and never `S.mk`. Both count as instantiation.
      let flat := ctor ++ `_flat_ctor
      let ctorRefs := refs.getD ctor 0 + refs.getD flat 0
      let fields := getStructureFields env n
      let mut propFields := 0
      for f in fields do
        if let some proj := getProjFnForField? env n f then
          if let some pci := env.find? proj then
            let isP ← forallTelescope pci.type fun _ b => Meta.isProp b
            if isP then propFields := propFields + 1
      IO.println s!"STRUCT\t{m}\t{← lineOf n}\t{n}\t{ctorRefs}\t{fields.size}\t{propFields}"
  -- `@[simp]`-tagged package declarations, and whether any proof term names them.
  let simpThms ← Meta.getSimpTheorems
  let mut nSimp := 0
  for (n, m, _) in src do
    if simpThms.isLemma (.decl n) then
      nSimp := nSimp + 1
      -- A `rfl`-theorem can be applied by the `dsimp` path, which rewrites
      -- definitionally and emits NO proof term. For those, a zero reference
      -- count is not evidence that the tag never fired; for every other simp
      -- lemma it is.
      let rfl ← Meta.isRflTheorem n
      IO.println s!"SIMP\t{m}\t{← lineOf n}\t{n}\t{valRefs.getD n 0}\t{rfl}"
  IO.println s!"TOTALS\t{nPkg}\t{src.size}\t{nDefs}\t{nThms}\t{propDefs.size}\t{nSimp}"
