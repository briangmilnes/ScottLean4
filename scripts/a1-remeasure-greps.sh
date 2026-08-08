#!/usr/bin/env bash
# a1-remeasure-greps.sh — r0043, agent1.
#
# Read-only. Writes nothing. Re-runs the three-way absence probe of r0040
# (scripts/a1-absence-greps.sh) over the tree as it stands after r0041 and
# r0042 added 22 modules, for exactly those §2/§3 property rows that r0040
# labelled `N` and that the new-module survey did not obviously close.
#
# A row stays `N` only if all three of its greps return zero substantive hits.
# Every grep is `grep -rEni --include='*.lean'` over ScottDomains/ScottDomains/,
# docstrings included: a docstring hit is what would make a row `P` rather
# than `N`.
#
# Usage: scripts/a1-remeasure-greps.sh

set -u
PKG=/home/milnes/projects/ScottLean4-agent1/ScottDomains/ScottDomains

probe () {
  # $1 = row label, $2 = grep number, $3 = extended regex
  local n
  n=$(grep -rEni --include='*.lean' "$3" "$PKG" | wc -l)
  printf '=== %s  grep %s  /%s/  -> %s\n' "$1" "$2" "$3" "$n"
  if [ "$n" -gt 0 ] && [ "$n" -le 12 ]; then
    grep -rEni --include='*.lean' "$3" "$PKG"
  fi
}

echo "##### row 30 — Q (the rationals) is not a cpo"
probe row30 1 'sqrt|square root'
probe row30 2 'CompletePartialOrder .{0,4}(Rat|ℚ)|LinearOrderedField'
probe row30 3 'rationals.{0,40}(not|fail)|(not|fail).{0,40}(a cpo|cpo)'

echo "##### row 31 — the unit interval [0,1] is a cpo"
probe row31 1 'unitInterval|Set\.Icc'
probe row31 2 'ℝ|Real\.|Mathlib\.Data\.Real'
probe row31 3 'unit interval'

echo "##### row 33 — monotone implies continuous with no infinite ascending chains"
probe row33 1 'WellFoundedGT|IsWellFounded|WellFoundedLT'
probe row33 2 'ascendingChain|noInfiniteAscending|StrictMono.{0,24}bounded|ACC|ascending chain condition'
probe row33 3 'scottContinuous_of_monotone'

echo "##### row 38 — cpo-continuity vs topological continuity on [0,1]"
probe row38 1 'TopologicalSpace|nhds|Metric'
probe row38 2 'usual sense|topologically continuous|Continuous \('
probe row38 3 'ScottTopology|scottTopology|IsScott'

echo "##### rows 43 and 57 — all cpos so far are domains / all domains so far bounded complete"
probe row43 1 'mentioned so far|discussed so far|so far are'
probe row43 2 'every cpo (we|so far)|all of the cpo'
probe row43 3 'all of the domains|all the domains'

echo "##### row 44 — compacts of N-bot -> N-bot are the finite-domain functions"
probe row44 1 'finite domain of definition|finiteSupport|finite support|domain of definition'
probe row44 2 'ScottHom \(Flat|ScottHom NatBot|ScottHom \(NatBot'
probe row44 3 'compacts \(ScottHom|isCompactElement.{0,30}NatBot|NatBot.{0,30}isCompactElement'

echo "##### row 46 — a continuous f : P N -> P N is named by a countable G_f"
probe row46 1 'countable.{0,24}graph|graph.{0,24}countable|countable_graph'
probe row46 2 'graphPairs|G_f|graphOn'
probe row46 3 'Countable \(Set \(?(Nat|ℕ)|not_countable'

echo "##### row 47 — each of f and g uniquely determines the other in an e-p pair"
probe row47 1 'uniquely determines|unique_projection|projection_unique|unique_embedding'
probe row47 2 'eq_of_isEmbeddingProjectionPair|embedding_eq|projection_eq|determines_'
probe row47 3 'determines the other|determined by'

echo "##### row 54 — D bounded complete iff D-top is an algebraic lattice"
probe row54 1 'WithTop|adjoinTop|addTop|withTop'
probe row54 2 'algebraic lattice.{0,32}iff|iff.{0,32}algebraic lattice|AlgebraicLattice'
probe row54 3 'boundedComplete_iff|BoundedComplete .{0,4}↔|↔.{0,4}BoundedComplete'

echo "##### row 56 — N-bot -o N-bot lacks a top element, so is not an algebraic lattice"
probe row56 1 'lacks a top|no top element|OrderTop|IsTop|¬ *∃.{0,12}top'
probe row56 2 'StrictHom NatBot|StrictHom \(Flat|StrictHom \(NatBot'
probe row56 3 'fails to be an algebraic lattice|not an algebraic lattice'

echo "##### row 58 — step-function poset has decidable ordering and finite normal subposets"
probe row58 1 'StepFunctionsDecidable'
probe row58 2 'RecursiveNormal|RecursiveLE|IsRecursive'
probe row58 3 'tedious, but not difficult'
