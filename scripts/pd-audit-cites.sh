#!/bin/zsh
# pd-audit-cites.sh — r0038 agent4 (Audit.Powerdomains) citation measurement.
#
# Why this exists: `scripts/unused-theorems.sh` answers one bit per name — "is it
# mentioned anywhere but its own declaration?" — and states that it under-reports,
# because it matches on the final name component and two `map_bot`s in different
# namespaces mask each other. The r0038 audit needs more than the bit: for label
# `S` it must *name a citer*, and for label `D`/`W` it must see every mention. So
# this prints, for each theorem/lemma declared in the seven `Audit.Powerdomains`
# modules, the number of mentions outside its own declaration line and the first
# three of them, file:line.
#
# Counting rule for declarations is a superset of `counts.sh`'s: it also picks up
# `protected theorem` / `protected lemma`, which `counts.sh` misses, so the row
# count here exceeds the 197 that `module-counts.sh` reports for these modules.
# The extra rows are marked `[protected]`.
#
# Method: for each declaration, grep the whole package for the final name
# component as a whole word, then drop the hits that are the declaration itself.
# Self-mentions inside the declaring file's own proofs *do* count as citations,
# same as `unused-theorems.sh`; the file:line output lets a reader tell the two
# apart by eye.
#
# Usage: scripts/pd-audit-cites.sh
set -e
cd "${0:A:h}/.."
pkg="ScottDomains/ScottDomains"

mods=(
  IdealCompletion.lean
  Powerdomain/Hoare.lean
  Powerdomain/Smyth.lean
  Powerdomain/Plotkin.lean
  Powerdomain/BoundedComplete.lean
  Powerdomain/Universal.lean
  ContinuousAlgebra.lean
)

allfiles=(${(f)"$(find $pkg -name '*.lean' | sort)"})

for m in $mods; do
  f="$pkg/$m"
  print -r -- "===== $m ====="
  grep -nE '^(@\[[^]]*\] )?(protected )?(theorem|lemma) ' $f | while IFS= read -r line; do
    lno=${line%%:*}
    rest=${line#*:}
    prot=""
    [[ $rest == *"protected "* ]] && prot=" [protected]"
    simp=""
    [[ $rest == "@["*"simp"*"]"* ]] && simp=" [simp]"
    nm=$(print -r -- "$rest" \
      | sed -E 's/^(@\[[^]]*\] )?(protected )?(theorem|lemma) +//; s/[ ({:\[].*$//')
    short=${nm##*.}
    hits=$(grep -n -w -F -- "$short" $allfiles | grep -v "^$f:$lno:" || true)
    n=$(print -r -- "$hits" | grep -c . || true)
    print -r -- "$lno  $nm  cites=$n$simp$prot"
    if (( n > 0 )); then
      print -r -- "$hits" | cut -d: -f1,2 | sed "s|^$pkg/|      |" | head -4
    fi
  done
done
