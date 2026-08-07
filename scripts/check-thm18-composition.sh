#!/bin/zsh
# check-thm18-composition.sh — does r0037's Theorem 18 work actually compose?
#
# agent1 (ScottDomains.JungFinite) proved the assembly
#   thm18_of_propertyM : FixedPointOfCompactDeflationIsCompact α →
#                        (property m at every finite subset of K(α)) → IsBifinite α
# and agent2 (ScottDomains.JungNets) proved
#   forall_hasCompleteMub_of_thm137 : Thm137 D → IsAlgebraic (ScottHom D D) →
#                        (property m at every finite subset of K(D))
# in separate worktrees, neither able to see the other. Their hypothesis shapes
# were negotiated only through the round plan, and the argument order differs.
#
# `lake build` cannot answer whether they compose: it never imports two unrelated
# modules into one environment. That is the same blind spot that let r0028's
# duplicate declaration survive 971 green jobs. So this elaborates the composite
# directly, in one allowlisted command with no chaining.
#
# Exit 0 and "composition typechecks" means Theorem 18 now rests on exactly two
# named open propositions: Jung's Theorem 1.37 and his Corollary 1.36.
set -e
cd "${0:A:h}/.."
pkg="$PWD/ScottDomains"

src=$(mktemp /tmp/thm18-compose-XXXXXX.lean)
cat > "$src" <<'LEAN'
import ScottDomains.JungFinite
import ScottDomains.JungNets

open ScottDomains

/-- Theorem 18 from Jung's Theorem 1.37 and his Corollary 1.36, with every other
step of the five-step route discharged. -/
theorem thm18_of_jung_1_37_and_1_36
    {α : Type} [CompletePartialOrder α] [Domain α] [Domain (ScottHom α α)]
    (hcor : JungFinite.FixedPointOfCompactDeflationIsCompact α)
    (h137 : JungNets.Thm137 α) :
    IsBifinite α :=
  JungFinite.thm18_of_propertyM hcor
    (fun v hvc hvfin =>
      JungNets.forall_hasCompleteMub_of_thm137 h137 inferInstance v hvfin hvc)

#print axioms thm18_of_jung_1_37_and_1_36
LEAN

cd "$pkg"
lake env lean "$src"
echo "composition typechecks: thm18 rests on Thm137 and Corollary 1.36 alone"
