/-
a4-decl-query.lean — r0046 Goal B (agent4): the declaration index the prose sweep
checks its claims against.

Run it with the EXISTING driver, which already solves the import problem four
agents have hit:

    scripts/a6-env-scan.sh <out> scripts/a4-decl-query.lean

`import ScottDomains` alone yields a Mathlib-only environment, because the
package root imports none of the submodules; `a6-env-scan.sh` writes one `import`
line per module found under `ScottDomains/ScottDomains/` and so elaborates all
100. This file is not a package module — it lives in `scripts/`, invisible to
`lake build` and to `counts.sh`.

Why the environment and not a source lexer. Every sentence this round is
auditing is of the form "X is proved" / "X is open" / "X does not exist", and
each of those is a question about the ELABORATED environment:

  * "X is proved"      ⟺  some package theorem's type, after stripping binders,
                          is headed by the constant X.
  * "X is refuted"     ⟺  some package theorem's conclusion is `Not X`.
  * "an instance of C
     at T does not exist" ⟺ no package declaration's conclusion is headed by C.
  * "only N of the M
     schemes are proved" ⟺ the family's cardinality in the environment is N.

A grep cannot answer any of them: `theorem foo : Bar := …` written with an
abbreviation, a `variable`-bound instance binder, or a conclusion reached through
a definitional unfolding are all invisible to a lexer and all visible here.

Output, one tab-separated record per line:

  DECL <module> <line> <kind> <name> <conclHead> <negHead> <propHyps> <isInst>
      kind is thm | propdef | def | axiom | struct | other.
      conclHead  head constant of the type's conclusion after stripping every
                 leading binder ("-" when the conclusion is not an application
                 of a constant, e.g. a Prop-valued `def` whose body is a sort).
      negHead    when conclHead is `Not`, the head of the negated proposition,
                 so a refutation is indexed by WHAT it refutes.
      propHyps   count of non-instance proof hypotheses. A theorem concluding D
                 with a proof hypothesis has reduced D, not discharged it —
                 r0044's dominant defect mode, so it is carried through.
      isInst     true when the declaration carries the `instance` attribute.
  TOTALS <pkgConstants> <sourceConstants>

Generated declarations (`.mk`, `.rec`, `.injEq`, equation lemmas, internals) are
dropped, exactly as in `a6-query.lean`, whose predicates this file reuses.
-/

open Lean Meta Elab Command

namespace A4

def isPkgModule (m : Name) : Bool :=
  m == `ScottDomains || (`ScottDomains).isPrefixOf m

def genSuffix : Array String :=
  #["mk", "rec", "recOn", "casesOn", "below", "brecOn", "binductionOn", "ndrec",
    "noConfusion", "noConfusionType", "injEq", "inj", "sizeOf_spec", "toCtorIdx",
    "eq_def", "ofNat", "ext", "ext_iff", "sizeOf_inst"]

def isEqLemma (s : String) : Bool :=
  s.startsWith "eq_" && (s.drop 3).length > 0 && (s.drop 3).all Char.isDigit

partial def hasUnderscoreComponent : Name → Bool
  | .str p s => s.startsWith "_" || hasUnderscoreComponent p
  | .num p _ => hasUnderscoreComponent p
  | .anonymous => false

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

/-- The head constant of a type's conclusion, and — when that head is `Not` —
the head of the proposition being negated. -/
def heads (t : Expr) : MetaM (Option Name × Option Name) :=
  forallTelescope t fun _ body => do
    match body.getAppFn with
    | .const n _ =>
        if n == ``Not then
          let args := body.getAppArgs
          if h : 0 < args.size then
            match args[0]!.getAppFn with
            | .const m _ => return (some n, some m)
            | _          => return (some n, none)
          else return (some n, none)
        else return (some n, none)
    | _ => return (none, none)

/-- Non-instance proof hypotheses. Instance-implicit binders carry structure,
not an assumption, so they are excluded — but see the report: an ADDED instance
binder is itself a weakening, and the sweep reports it separately. -/
def propHypCount (t : Expr) : MetaM Nat :=
  forallTelescope t fun xs _ => do
    let mut k := 0
    for x in xs do
      let d ← x.fvarId!.getDecl
      unless d.binderInfo == .instImplicit do
        if ← Meta.isProp d.type then k := k + 1
    return k

def lineOf (n : Name) : CoreM Nat := do
  match ← findDeclarationRanges? n with
  | some r => return r.selectionRange.pos.line
  | none   => return 0

end A4

open A4 in
run_cmd Command.liftTermElabM do
  let env ← getEnv
  let mods := env.header.moduleNames
  let mut nPkg := 0
  let mut nSrc := 0
  for (n, ci) in env.constants.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let m := mods[idx]!
    unless isPkgModule m do continue
    nPkg := nPkg + 1
    if isGenerated n then continue
    nSrc := nSrc + 1
    let (ch, nh) ← heads ci.type
    let k ← propHypCount ci.type
    let isInst := Lean.Meta.isInstanceCore env n
    let kind :=
      match ci with
      | .axiomInfo _ => "axiom"
      | .thmInfo _   => "thm"
      | .defnInfo _  => "def"
      | .inductInfo _ => "struct"
      | _            => "other"
    let kind ←
      if kind == "def" then
        if ← resultIsProp ci.type then pure "propdef" else pure "def"
      else pure kind
    let chs := match ch with | some c => toString c | none => "-"
    let nhs := match nh with | some c => toString c | none => "-"
    IO.println s!"DECL\t{m}\t{← lineOf n}\t{kind}\t{n}\t{chs}\t{nhs}\t{k}\t{isInst}"
  IO.println s!"TOTALS\t{nPkg}\t{nSrc}"
