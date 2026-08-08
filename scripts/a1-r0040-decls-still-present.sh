#!/usr/bin/env bash
# a1-r0040-decls-still-present.sh — r0043, agent1.
#
# Read-only. Writes nothing. r0043's scope is the 24 rows r0040 labelled `N`;
# the other 177 rows are out of scope, but the plan asks that a *regression*
# be reported if one is noticed. This is the cheapest possible check for one:
# every declaration name r0040's §2/§3 property table cited as the evidence for
# an `S+P` or `S≠` row is grepped for its defining occurrence in the package.
# A name with 0 hits would be a declaration that has since been deleted or
# renamed, which would put its row back to `N`.
#
# Mathlib names (Function.Embedding.schroeder_bernstein, Set.instCompleteLattice,
# Set.sSup_eq_sUnion) are not in this package and are not listed.
#
# Usage: scripts/a1-r0040-decls-still-present.sh

set -u
PKG=/home/milnes/projects/ScottLean4-agent1/ScottDomains/ScottDomains

NAMES="
theorem1
map_kleeneFix
kleeneFix_le
theorem3
IsNormalIn.trans
IsNormalIn.mono_right
IsNormalIn.bot_mem
IsNormalIn.refl
isNormalIn_sUnion
isNormalIn_sUnion_of_mem
isNormalIn_sUnion_le
singleton_bot_isNormalIn_of_isNormalIn
isCompactElement_iff
isNormalIn_compacts
theorem6
isBoundedCompleteDomain_scottHom
strictHomDomain
lem10_strict
isCompactElement_iff_finite
scottContinuous_stepFun
isCompactElement_step
exists_finite_isLUB_of_isCompactElement
injective_embedding
surjective_projection
isFinitaryProjection_normalHom
strictHomCpo
isLUB_of_finite_directed
scottContinuous_of_monotone_of_finite
coe_eq_basisExtension_self
scottContinuous_strictFun
strictFun_bot
strictHom_val_of_isStrict
strictHom_val_le
apply_of_mem_range
scottContinuous_val
scottContinuous_corestrict
range_normalHom_inter_compacts
normalFun_range_inter_compacts
isFinitaryProjection_sSup
lemma213
strictHomIsAlgebraic
isCompactElement_val_of_isCompactElement
countable_compacts_scottHom
"

missing=0
for n in $NAMES; do
  # An attribute may precede the keyword on the same line (`@[simp] theorem f`),
  # so the pattern allows one bracketed attribute list before it.
  c=$(grep -rEc --include='*.lean' "^ *(@\[[^]]*\] *)?(protected )?(noncomputable )?(theorem|lemma|def|instance|abbrev|structure).*\b${n}\b" "$PKG" 2>/dev/null | grep -v ':0$' | wc -l)
  if [ "$c" -eq 0 ]; then
    printf 'MISSING  %s\n' "$n"
    missing=$((missing + 1))
  else
    printf 'present  %s  (%s file(s))\n' "$n" "$c"
  fi
done
printf '\n%s name(s) with no defining occurrence\n' "$missing"
