#!/bin/zsh
# agent2-citations.sh — for every theorem/lemma declared in agent2's r0038 audit
# area (the projection/bifinite stack), report where else in the development its
# name occurs.
#
# Why this exists: `unused-theorems.sh` answers a yes/no question globally (does
# this name occur more than once?) and under-reports, because it matches on the
# final name component only, so two `map_bot`s in different namespaces mask each
# other. The r0038 audit needs the *citing declaration*, not the count: label `S`
# requires naming one citer, and label `U` requires showing there is none. This
# script therefore prints, per declared name, every file that mentions it and how
# many times, splitting same-file mentions from cross-file ones — a lemma used
# only inside its own file's proofs is still cited, but by a different population
# than one consumed by another module.
#
# Output is TSV: name, module, simp-tag, self-file-uses, other-file-uses, citers.
# `self-file-uses` and `other-file-uses` both exclude the declaration line itself.
#
# Usage: scripts/agent2-citations.sh
set -e
cd "${0:A:h}/.."
pkg="ScottDomains/ScottDomains"

mods=(Projection FinitaryProjection NormalSubposet NormalProjection Theorem6 \
      FinitaryProjectionPoset FinitaryProjectionEmbedding Bifinite \
      MinimalUpperBounds Section62 SFP)

allsrc=(${(f)"$(find $pkg -name '*.lean' | sort)"})

print -r -- "name\tmodule\tsimp\tself\tother\tciters"
for m in $mods; do
  f="$pkg/$m.lean"
  # declaration lines, with the attribute prefix retained so we can spot @[simp]
  while IFS= read -r line; do
    attr=""
    [[ "$line" == @\[* ]] && attr="${line%%\]*}]"
    nm="${line#*(theorem|lemma) }"
    nm=$(print -r -- "$line" | sed -E 's/^(@\[[^]]*\] )?(theorem|lemma) +//; s/[ ({:\[].*$//')
    short="${nm##*.}"
    simp="-"
    [[ "$attr" == *simp* ]] && simp="simp"
    self=0; other=0; citers=""
    for g in $allsrc; do
      c=$(grep -c -w -F -- "$short" "$g" || true)
      (( c == 0 )) && continue
      if [[ "$g" == "$f" ]]; then
        # subtract the declaration occurrence(s) of this exact name
        d=$(grep -cE "^(@\[[^]]*\] )?(theorem|lemma) +($short|[A-Za-z0-9_.]*\.$short)([ ({:\[]|$)" "$g" || true)
        self=$(( c - d ))
      else
        other=$(( other + c ))
        citers="$citers ${g#$pkg/}:$c"
      fi
    done
    print -r -- "$short\t$m\t$simp\t$self\t$other\t$citers"
  done < <(grep -hE '^(@\[[^]]*\] )?(theorem|lemma) ' "$f")
done
