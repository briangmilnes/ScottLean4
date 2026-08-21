#!/bin/zsh
# sorry-axioms.sh — which package constants depend on `sorryAx`, exhaustively.
#
# `scripts/counts.sh` counts `sorry` tokens lexically (`^\s*sorry\s*$`) and
# `scripts/axioms.sh` runs `#print axioms` over declarations you name. Neither
# answers the question the development's design actually rests on: *no proved
# declaration applies an unproved one*, i.e. exactly the stub theorems depend on
# `sorryAx` and nothing else does. A lexical count cannot see that, and naming
# declarations by hand cannot certify it.
#
# This generates a Lean file importing every module in the package, then walks
# every constant those modules declare and calls `Lean.collectAxioms` — the same
# machinery `#print axioms` uses — reporting each constant whose axiom set
# contains `sorryAx`. Measured 2026-08-21: 4,910 constants scanned in 6.0 s.
#
# Usage: scripts/sorry-axioms.sh
set -e
cd "${0:A:h}/.."
pkg="$HOME/projects/ScottProjects/ScottDomains"
out="${TMPDIR:-/tmp}/sorry-axioms-scan.lean"

python3 - "$pkg" "$out" <<'PY'
import os, sys
pkg, out = sys.argv[1], sys.argv[2]
mods = []
for root, _, files in os.walk(os.path.join(pkg, 'ScottDomains')):
    for f in sorted(files):
        if f.endswith('.lean'):
            rel = os.path.relpath(os.path.join(root, f), pkg)[:-5]
            mods.append(rel.replace(os.sep, '.'))
mods.sort()
# Theorem bodies of imported modules are not available through
# `ConstantInfo.value?` (Lean stores them out of line), so the scan must go
# through `collectAxioms` rather than walking the proof terms directly.
body = '''
open Lean

run_cmd Elab.Command.liftCoreM do
  let env ← getEnv
  let isOurs (n : Name) : Bool :=
    match env.getModuleIdxFor? n with
    | some i => (`ScottDomains).isPrefixOf (env.header.moduleNames[i.toNat]!)
    | none   => false
  let mut scanned : Nat := 0
  let mut hits : Array Name := #[]
  for (n, _) in env.constants.toList do
    if !isOurs n then continue
    scanned := scanned + 1
    let ax ← collectAxioms n
    if ax.contains ``sorryAx then hits := hits.push n
  logInfo m!"package constants scanned: {scanned}"
  logInfo m!"depend on sorryAx: {hits.size} {hits}"
'''
open(out, 'w').write('\n'.join('import ' + m for m in mods) + '\n' + body)
print(f'{len(mods)} modules imported by {out}')
PY

cd "$pkg"
lake env lean "$out"
