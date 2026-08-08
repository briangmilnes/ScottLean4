#!/usr/bin/env bash
# a5-s7-decls.sh — dump the comment-aware declaration list for every module that
# r0040's §7 coverage audit has to check, into one file in the scratchpad.
#
# Why this exists: round r0040 asks, for each property §7 of Gunter & Scott 1990
# asserts, whether a Lean declaration states it. Answering that needs the names
# of every declaration in the eighteen §7-bearing modules at once, and
# `lean-decls.py --list` over eighteen paths is one long command line that would
# otherwise be typed inline. The project forbids chained shell commands, so the
# loop lives here.
#
# Usage: a5-s7-decls.sh <out-file>
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
src="$root/ScottDomains/ScottDomains"
out="$1"
mkdir -p "$(dirname "$out")"

mods=(
  RecursiveDomain.lean
  UniversalDomain.lean
  Universality.lean
  Powerset.lean
  Combinator.lean
  CombinatorRep.lean
  Dyadic.lean
  Atomless.lean
  PRep.lean
  PRepresentable.lean
  PRepFun.lean
  PRepSum.lean
  Lemma28AtU.lean
  BifiniteUniversal.lean
  Colimit.lean
  LemThirty.lean
  FinitaryProjectionPoset.lean
  NormalProjection.lean
  Projection.lean
  Audit/SectionSeven.lean
)

paths=()
for m in "${mods[@]}"; do paths+=("$src/$m"); done

python3 "$root/scripts/lean-decls.py" --list "${paths[@]}" > "$out"
python3 "$root/scripts/lean-decls.py" --per-file "${paths[@]}"
wc -l "$out"
