#!/bin/zsh
# a5-simp-downstream.sh — r0038 agent5 audit: does a `@[simp]` tag fire in any
# module DOWNSTREAM of the one that declares it?
#
# Why this exists: `a5-simp-firing.sh` answers the question inside the declaring
# module only, by elaborating a copy with the attribute group deleted. That settles
# a leaf module and nothing else — a tag that does no work at home may still fire
# in an importer. This script closes that gap without editing any source file:
# Lean's `attribute [-simp] <name>` removes a lemma from the default simp set for
# the remainder of the file being elaborated, so a copy of each downstream module
# with those lines spliced in after its imports is exactly the same experiment run
# one module later.
#
# Coverage is the caller's responsibility: pass the FULL reverse-dependency
# closure of the declaring module. If every module in that closure elaborates, the
# tags do no work anywhere in the development.
#
# Usage: scripts/a5-simp-downstream.sh <names-file> <DownstreamModule> [...]
#   <names-file> holds one fully qualified declaration name per line.
set -e
cd "${0:A:h}/.."
pkg="ScottDomains/ScottDomains"
out="/tmp/claude-1000/-home-milnes-projects-ScottLean4/ab3f8bb9-d928-40ef-b45c-b2c8efc2bd0e/scratchpad/simp-firing"
mkdir -p $out

names=$1; shift
ntags=$(grep -c . $names || true)

for m in "$@"; do
  src="$pkg/$m.lean"
  probe="$out/$(print -r -- $m | tr / _).downstream.lean"
  # Splice `attribute [-simp] …` immediately after the last import line, which is
  # the earliest point at which the names are in scope.
  last=$(grep -n '^import ' $src | tail -1 | cut -d: -f1)
  head -n $last $src > $probe
  while read -r nm; do
    [[ -z "$nm" ]] && continue
    print -r -- "attribute [-simp] $nm" >> $probe
  done < $names
  tail -n +$((last + 1)) $src >> $probe

  if lake -d ScottDomains env lean $probe > $out/$(print -r -- $m | tr / _).downstream.out 2>&1; then
    print -r -- "$m: elaborates with the $ntags tags removed — none of them fires here"
  else
    print -r -- "$m: FAILED, $(grep -c 'error:' $out/$(print -r -- $m | tr / _).downstream.out) errors — at least one tag fires here"
    grep -m 6 'error:' $out/$(print -r -- $m | tr / _).downstream.out || true
  fi
done
