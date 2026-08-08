#!/bin/zsh
# a1-check-thm18-after-cor136.sh — how many open propositions does Theorem 18
# still rest on, now that r0042 stream 1 has proved Jung's Corollary 1.36?
#
# `scripts/check-thm18-composition.sh` elaborates Theorem 18 against BOTH open
# propositions, Jung's Theorem 1.37 and his Corollary 1.36. This script drops the
# second hypothesis and supplies
#   ScottDomains.JungCor136.fixedPointOfCompactDeflationIsCompact
# in its place. Exit 0 means Theorem 18 now rests on Theorem 1.37 alone.
#
# `lake build` cannot answer this: it never imports JungCor136 and JungNets into
# one environment. Same blind spot the r0028 duplicate-declaration incident
# exposed, so the check is elaborated directly, in one allowlisted command.
set -e
cd "${0:A:h}/.."
pkg="$PWD/ScottDomains"

src=$(mktemp /tmp/thm18-after-cor136-XXXXXX.lean)
cat > "$src" <<'LEAN'
import ScottDomains.JungCor136
import ScottDomains.JungNets

open ScottDomains

/-- Theorem 18 from Jung's Theorem 1.37 alone. Corollary 1.36 is no longer a
hypothesis: `JungCor136.fixedPointOfCompactDeflationIsCompact` proves it from
`IsAlgebraic (ScottHom α α)`, which `Domain (ScottHom α α)` already supplies. -/
theorem thm18_of_jung_1_37
    {α : Type} [CompletePartialOrder α] [Domain α] [Domain (ScottHom α α)]
    (h137 : JungNets.Thm137 α) :
    IsBifinite α :=
  JungFinite.thm18_of_propertyM JungCor136.fixedPointOfCompactDeflationIsCompact
    (fun v hvc hvfin =>
      JungNets.forall_hasCompleteMub_of_thm137 h137 inferInstance v hvfin hvc)

#print axioms thm18_of_jung_1_37
LEAN

cd "$pkg"
lake env lean "$src"
echo "composition typechecks: thm18 now rests on Thm137 alone"
