/-!
r0046 / agent5, Goal B — **the dependency probe** (body; the 105-module import
block is prepended by `scripts/a5-r46-gen.sh`, which is why this file alone does
not elaborate).

NOT part of the package: generated into `scripts/`, outside
`ScottDomains/ScottDomains/`, so `lake build` never sees it and the job count
stays at 1344.

## What it decides

The sweep `scripts/a5-r46-sweep.sh` found 230 candidate sentences in three
decidable shapes. Two of them are questions about the *proof terms* in the
`.olean`, so they need no re-proving:

**Shape 1 — "the argument has to go through `L`" / "`L` is indispensable".**
Let `T` be the theorem concluding the result and `L` the constant asserted
unavoidable. If `L ∉ deps(T)` the kernel has already accepted a proof that does
not go through `L`, and the sentence is **refuted**. `depsOn` decides this.

The converse is *not* decided here: `L ∈ deps(T)` shows this proof uses `L`, not
that every proof must. Confirming a necessity claim needs the deletion probe
(`scripts/a5-r46-delete.lean`), a different experiment. The report keeps
"refuted" and "consistent with the claim" apart for exactly this reason.

**Shape 2 — "this is the only place `L` is used/spent".** This is reverse
reachability: enumerate every package declaration whose body or type mentions
`L`. If the count is not 1, or the one hit is not the declaration the sentence
points at, the sentence is **false**. `directUsers` decides this. Note that 103
of the sweep's 230 candidates are of this shape, so it is the largest class.

## Cost

`depsOn` is O(|deps|) memoized environment lookups per query. `directUsers` is
one O(|package declarations| x |direct constants|) pass over the environment,
which is why it is computed once per query rather than materializing the whole
reverse graph.
-/

open Lean

namespace A5R46Deps

/-- The declaration's proof/definition body, if it has one.

**Do not replace this with `ConstantInfo.value?`.** Measured in this Lean
toolchain (`scripts/a5-r46-diag.lean`): for `ScottDomains.R45.Agent4.smythImageIso`,
`ci` is `thmInfo`, `ci.value?.isSome` is **`false`**, and yet
`v.value.getUsedConstants.size` is **56**. `value?` does not surface theorem
bodies here, so a probe built on it reports every theorem as depending on
nothing and refutes every necessity claim put to it. That defect was caught by
the `USES` control below, which is why the control is not optional. -/
def bodyOf : ConstantInfo → Option Expr
  | .thmInfo v    => some v.value
  | .defnInfo v   => some v.value
  | .opaqueInfo v => some v.value
  | _             => none

/-- The constants occurring directly in a declaration's type and body. -/
def directConsts (ci : ConstantInfo) : Array Name :=
  match bodyOf ci with
  | some v => ci.type.getUsedConstants ++ v.getUsedConstants
  | none   => ci.type.getUsedConstants

/-- Transitive constants of a declaration, memoized: the fixpoint of
`directConsts`. -/
partial def transDeps (env : Environment) (n : Name) : StateM NameSet Unit := do
  if (← get).contains n then return
  modify (·.insert n)
  match env.find? n with
  | none => return
  | some ci => for c in directConsts ci do transDeps env c

/-- Shape 1. `NOT-USED` **refutes** a "`T` has to go through `L`" claim. -/
def depsOn (thm target : Name) : CoreM Unit := do
  let env ← getEnv
  if (env.find? thm).isNone then IO.println s!"MISSING THEOREM  {thm}"; return
  if (env.find? target).isNone then IO.println s!"MISSING TARGET   {target}"; return
  let (_, s) := (transDeps env thm).run {}
  let tag := if s.contains target then "USES    " else "NOT-USED"
  IO.println s!"{tag}  {thm}  ->  {target}   (|deps| = {s.size})"

/-- Shape 2. Every package declaration mentioning `target` directly.
"This is the only place `target` is spent" is true exactly when this list has
one entry and it is the declaration the sentence points at. Auto-generated
equation lemmas and `match` arms are dropped: they are artifacts of the
elaborator, not places a human spent a hypothesis. -/
def directUsers (target : Name) : CoreM Unit := do
  let env ← getEnv
  if (env.find? target).isNone then IO.println s!"MISSING TARGET   {target}"; return
  let mut hits : Array Name := #[]
  for (n, ci) in env.constants.toList do
    if n == target then continue
    if !(`ScottDomains).isPrefixOf n then continue
    if n.isInternal then continue
    if (directConsts ci).contains target then hits := hits.push n
  IO.println s!"USERS of {target}: {hits.size}"
  for h in hits.qsort (·.toString < ·.toString) do IO.println s!"    {h}"

end A5R46Deps

open A5R46Deps

/-! # Shape 1 queries -/

/-! ## N1 — `PowerdomainMapRep.lean:46-48`

> "the identification of the two sides cannot be made by transporting a basis; it
> has to go through `IsProjection.isCompactElement_iff` (Lemma 5), which
> characterises `K(im p)` intrinsically."

`SmythImageIso` and `HoareImageIso` are discharged in `A4PowerdomainRep.lean`
(r0045, agent4). If those proofs do not depend on the named lemma, the sentence
is refuted by the kernel. -/

#eval depsOn `ScottDomains.R45.Agent4.smythImageIso
  `ScottDomains.ScottHom.IsProjection.isCompactElement_iff
#eval depsOn `ScottDomains.R45.Agent4.hoareImageIso
  `ScottDomains.ScottHom.IsProjection.isCompactElement_iff

/-! ### Control — the instrument must be able to answer `USES`.

A dependency probe that answered `NOT-USED` for everything would be worthless,
and the first version of this file did exactly that (see `bodyOf`).
`A4PowerdomainRep.lean:40-41` names `nonempty_orderIso_range_of_section` as what
`smythImageIso` reduces to, so it must show `USES`. -/

#eval depsOn `ScottDomains.R45.Agent4.smythImageIso
  `ScottDomains.R45.Agent4.nonempty_orderIso_range_of_section

/-! # Shape 2 queries — "the only place X is used/spent" -/

/-! ## U1 — `JungBicomplete.lean:506`: `JungNets.HasChainInfima`,
"which `Thm18` is now known to be the only consumer of". -/

#eval directUsers `ScottDomains.JungNets.HasChainInfima

/-! ## U2 — `FinitaryProjectionPoset.lean:461`: "This is the only place
bifiniteness is spent, and it is spent through …". -/

#eval directUsers `ScottDomains.IsBifinite

/-! ## U3 — `LemThirty.lean:147,662`: `countable_compacts_of_reflects`
"shows the word is load-bearing" / "shows it is not optional". The claim is that
this lemma is what makes the countability hypothesis necessary, so it must have
consumers. -/

#eval directUsers `ScottDomains.LemThirty.countable_compacts_of_reflects

/-! ## U4 — `Universality.lean:88`: `orderIsoProdCongr` was built because Mathlib
has none. `SeparatedSum.lean:173` builds a second copy and says "without it
`e₁.prodCongr e₂` silently resolves through the coercion". Two copies of one
missing Mathlib lemma is itself worth measuring. -/

#eval directUsers `ScottDomains.ClosureProperties.orderIsoProdCongr

/-! ## U5 — `Dyadic.lean:454`: §7.3's proof paragraph "is the only part of
Theorem 27 not proved in this development"; and `Dyadic.lean:552`: "**This is
the only place normality of `N` is used**". -/

#eval directUsers `ScottDomains.NormalSubposet
