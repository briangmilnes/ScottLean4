#!/bin/zsh
# bifinite-audit-citations.sh — r0038 agent6 (stream `Audit.Bifinite`).
#
# Why this exists: the r0038 audit labels every theorem in
# {BifiniteUniversal, Colimit, LemThirty, JungSFP, JungFinite, JungNets,
# ContinuousConstruction} as P/S/A/U/D/W. The `S` label requires naming a citing
# declaration, and `U` requires showing that nothing cites the name. Neither is
# answerable from `unused-theorems.sh`, which (a) reports only names cited
# nowhere at all and (b) matches on the final name component, so it under-reports.
#
# What it measures, per declaration in the seven modules:
#   name | simp? | self  = mentions inside its own file, excluding the decl line
#                | ext   = mentions in every other .lean file in the package
#                | files = the other files that mention it (comma separated)
# A declaration with self=0 and ext=0 is cited nowhere; ext>0 names the citer's
# module, which is the evidence the `S` label needs.
#
# Matching is on the bare final component as a whole word (`grep -w`), the same
# rule unused-theorems.sh uses, so cross-namespace collisions inflate rather than
# deflate the counts — a zero here is therefore trustworthy, a positive count is
# a candidate that must be read.
#
# Usage: scripts/bifinite-audit-citations.sh [module.lean ...]
set -e
cd "${0:A:h}/.."
pkg="ScottDomains/ScottDomains"

if (( $# )); then
  mods=($@)
else
  mods=(BifiniteUniversal.lean Colimit.lean LemThirty.lean JungSFP.lean
        JungFinite.lean JungNets.lean ContinuousConstruction.lean)
fi

allfiles=(${(f)"$(find $pkg -name '*.lean' | sort)"})

print -r -- "module|decl|simp|self|ext|files"
for m in $mods; do
  f=$pkg/$m
  # declaration lines: optional single attribute group, then theorem|lemma
  grep -nE '^(@\[[^]]*\] )?(theorem|lemma) ' $f | while IFS= read -r line; do
    lno=${line%%:*}
    rest=${line#*:}
    simp=no
    [[ $rest == '@['*simp* ]] && simp=yes
    nm=$(print -r -- "$rest" | sed -E 's/^(@\[[^]]*\] )?(theorem|lemma) +//; s/[ ({:\[].*$//; s/^.*\.//')
    [[ -z "$nm" ]] && continue
    self=$(grep -c -w -F -- "$nm" $f || true)
    self=$((self - 1))
    ext=0; flist=""
    for g in $allfiles; do
      [[ $g == $f ]] && continue
      c=$(grep -c -w -F -- "$nm" $g || true)
      if (( c > 0 )); then
        ext=$((ext + c))
        flist="$flist,${g#$pkg/}"
      fi
    done
    print -r -- "$m|$nm|$simp|$self|$ext|${flist#,}"
  done
done
