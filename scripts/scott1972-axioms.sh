#!/usr/bin/env bash
# scott1972-axioms.sh — independent axiom audit of Ericson's scott1972 artifact.
#
#   scripts/scott1972-axioms.sh [decl …]      (default: Theorem 4.4's two halves)
#
# The paper (arXiv 2606.30782) claims every result checks on the standard
# footprint `[propext, Classical.choice, Quot.sound]`. This project's own rule is
# that a claim about an artifact is checked, not read — so this runs
# `#print axioms` against the artifact's own toolchain rather than believing the
# abstract.
#
# Same `cd` reason as scripts/scott1972-verify.sh: the artifact pins
# leanprover/lean4:v4.30.0 and elan selects the toolchain from the working
# directory, so `lake env --dir=…` would run the wrong Lean. Run
# scott1972-verify.sh first — this needs the oleans.
set -u

root=/home/milnes/projects/ScottLean4
art="$root/scott1972"
[ -d "$art" ] || { echo "scott1972-axioms: no artifact at $art" >&2; exit 1; }

if [ "$#" -gt 0 ]; then
  decls=("$@")
else
  decls=(
    Scott1972.ContinuousLattice.projInfInf_embInfInf
    Scott1972.ContinuousLattice.embInfInf_projInfInf
  )
fi

src=$(mktemp /tmp/scott1972-ax-XXXXXX.lean)
{
  echo "import Scott1972"
  for d in "${decls[@]}"; do echo "#print axioms $d"; done
} > "$src"

cd "$art" || exit 1
lake env lean "$src"
rc=$?
rm -f "$src"
exit "$rc"
