#!/bin/zsh
# bifinite-audit-qualified.sh — r0038 agent6.
#
# Why this exists: bifinite-audit-citations.sh matches on the bare final name
# component, the same rule unused-theorems.sh uses. That rule collides across
# namespaces — `IsJungPatch.monotone` in JungSFP.lean matches all 169 uses of the
# word `monotone` anywhere in the package, which is evidence of nothing. This
# reconstructs the fully-qualified name by tracking the `namespace`/`section`/`end`
# stack, so a declaration can be searched for as `Ns.name` as well as `name`.
#
# Output columns: module | line | fullname | shortname | simp
#
# Usage: scripts/bifinite-audit-qualified.sh <module.lean> [...]
set -e
cd "${0:A:h}/.."
pkg="ScottDomains/ScottDomains"

if (( $# )); then
  mods=($@)
else
  mods=(BifiniteUniversal.lean Colimit.lean LemThirty.lean JungSFP.lean
        JungFinite.lean JungNets.lean ContinuousConstruction.lean)
fi

print -r -- "module|line|fullname|shortname|simp"
for m in $mods; do
  f=$pkg/$m
  ns=()
  lno=0
  while IFS= read -r line; do
    lno=$((lno + 1))
    case "$line" in
      "namespace "*)
        w=${line#namespace }; w=${w%% *}; ns+=($w) ;;
      "end "*)
        w=${line#end }; w=${w%% *}
        if (( ${#ns} )) && [[ ${ns[-1]} == $w ]]; then ns[-1]=(); fi ;;
      "@["*|"theorem "*|"lemma "*)
        print -r -- "$line" | grep -qE '^(@\[[^]]*\] )?(theorem|lemma) ' || continue
        simp=no
        [[ $line == '@['*simp* ]] && simp=yes
        nm=$(print -r -- "$line" | sed -E 's/^(@\[[^]]*\] )?(theorem|lemma) +//; s/[ ({:\[].*$//')
        [[ -z "$nm" ]] && continue
        # skip prose lines in doc comments: a real decl name is an identifier
        print -r -- "$nm" | grep -qE '^[A-Za-z_][A-Za-z0-9_.'"'"'!?₀-₉]*$' || continue
        prefix=${(j:.:)ns}
        if [[ -n $prefix ]]; then full="$prefix.$nm"; else full="$nm"; fi
        short=${nm##*.}
        print -r -- "$m|$lno|$full|$short|$simp" ;;
    esac
  done < $f
done
