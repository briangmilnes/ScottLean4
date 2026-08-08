#!/usr/bin/env bash
# a1-absence-greps.sh — evidence for the `N` (not stated) rows of r0040's §2/§3
# property-coverage audit.
#
# Why this exists: r0040 requires that before a paper property is labelled `N`
# ("no Lean declaration says this, in any form"), the development is grepped for
# the concept under at least three names, and the three names are reported. Doing
# that by hand is ~60 separate `grep` calls, each one a permission prompt under
# the project's no-chaining rule; this script runs them all as one command and
# prints a hit count per name, so the report cites counts rather than asserting
# absence.
#
# Each row is <property> <pattern> <hits>, case-insensitive, over
# ScottDomains/ScottDomains/**.lean only (docstrings included — a docstring hit
# is what separates label `P` from label `N`).
#
# It reads only. It writes nothing. Usage: scripts/a1-absence-greps.sh
set -uo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
src="$root/ScottDomains/ScottDomains"

probe () {
  local label="$1" pat="$2" n
  n=$(grep -rEi --include='*.lean' -c -- "$pat" "$src" | awk -F: '{s+=$2} END {print s+0}')
  printf '%-40s %-52s %s\n' "$label" "$pat" "$n"
}

printf '%-40s %-52s %s\n' '--- property ---' '--- pattern ---' 'hits'

probe 'omega-cpo-1'          'omegaTop|omega_top|OmegaTop'
probe 'omega-cpo-2'          'Ordinal'
probe 'omega-cpo-3'          'not a cpo|fails to be a cpo'
probe 'rationals-cpo-1'      'sqrt|square root'
probe 'rationals-cpo-2'      'LinearOrderedField|Rat\.instCompletePartialOrder'
probe 'rationals-cpo-3'      'CompletePartialOrder .{0,3}(Rat|ℚ)'
probe 'unit-interval-1'      'unitInterval|Set\.Icc'
probe 'unit-interval-2'      'Real|ℝ'
probe 'unit-interval-3'      'unit interval'
probe 'no-inf-asc-chains-1'  'WellFoundedGT|IsWellFounded'
probe 'no-inf-asc-chains-2'  'ascendingChain|noInfiniteAscending|StrictMono.{0,20}bounded'
probe 'no-inf-asc-chains-3'  'ascending chain'
probe 'flat-naturals-1'      'WithBot (Nat|ℕ)|Option (Nat|ℕ)'
probe 'flat-naturals-2'      'flatDomain|FlatOrder|natBot|NatBot'
probe 'flat-naturals-3'      'discrete order|discreteOrder|flat cpo'
probe 'f-star-extension-1'   'monotone_image|scottContinuous_image|image_isLUB'
probe 'f-star-extension-2'   'image_sUnion|image_iUnion|image_union'
probe 'f-star-extension-3'   'extension of f|fStar|imageHom'
probe 'topological-cont-1'   'TopologicalSpace|nhds|Metric'
probe 'topological-cont-2'   'usual sense|topologically continuous'
probe 'topological-cont-3'   'ScottTopology|scottTopology'
probe 'factorial-1'          'factorial'
probe 'factorial-2'          'recursive equation|recursion equation'
probe 'factorial-3'          'Nat\.rec|fact\('
probe 'cfg-1'                'grammar|contextFree|CFG'
probe 'cfg-2'                'alphabet|language'
probe 'cfg-3'                'concatenation|Kleene star|List\.append'
probe 'fix-continuous-1'     'scottContinuous_kleeneFix|monotone_kleeneFix'
probe 'fix-continuous-2'     'fixHom|kleeneHom|fixOperatorHom'
probe 'fix-continuous-3'     'ScottContinuous \(kleeneFix|Monotone kleeneFix'
probe 'fix-is-uniform-1'     'kleeneOperator\.IsUniform|IsUniform kleeneOperator'
probe 'fix-is-uniform-2'     'isUniform_kleene|kleeneOperator_isUniform'
probe 'fix-is-uniform-3'     'fix is .{0,12}uniform|uniform fixed point operator'
probe 'graph-Gf-1'           'graphOf|IsGraph|approximable relation'
probe 'graph-Gf-2'           'recover.{0,20}value|value.{0,20}from .{0,4}G'
probe 'graph-Gf-3'           'Set \(.{1,12} .{0,3}× .{0,12}\).{0,20}continuous'
probe 'countable-graph-1'    'countable.{0,20}graph|graph.{0,20}countable'
probe 'countable-graph-2'    'uncountable'
probe 'countable-graph-3'    'Countable \(Set (Nat|ℕ)\)'
probe 'ep-pair-unique-1'     'uniquely determines|unique_projection|projection_unique'
probe 'ep-pair-unique-2'     'eq_of_isEmbeddingProjectionPair|embedding_eq|projection_eq'
probe 'ep-pair-unique-3'     'determines the other|determined by'
probe 'fnspace-not-domain-1' 'not a domain|fails to be a domain'
probe 'fnspace-not-domain-2' 'notDomain|not_domain|¬ *Domain'
probe 'fnspace-not-domain-3' '¬ *IsAlgebraic|not_isAlgebraic'
probe 'bc-iff-alg-lattice-1' 'WithTop|adjoinTop|addTop'
probe 'bc-iff-alg-lattice-2' 'algebraic lattice.{0,30}iff|iff.{0,30}algebraic lattice'
probe 'bc-iff-alg-lattice-3' 'boundedComplete_iff|BoundedComplete .{0,3}↔'
probe 'eff-pres-any-1'       'EffectivePresentation'
probe 'eff-pres-fnspace-2'   'EffectivePresentation \((ScottHom|StrictHom)'
probe 'eff-pres-decid-3'     'decidableNormal|decidableLE'
probe 'strict-step-fns-1'    'strictStep|stepStrict|strict step'
probe 'strict-step-fns-2'    'StrictHom.{0,20}step|step.{0,20}StrictHom'
probe 'strict-step-fns-3'    'basis .{0,20}strict|strict .{0,20}basis'
probe 'ops-preserve-eff-1'   'preserve.{0,20}presentation|presentation.{0,20}preserve'
probe 'ops-preserve-eff-2'   'effectively presented'
probe 'ops-preserve-eff-3'   'effective presentation'
