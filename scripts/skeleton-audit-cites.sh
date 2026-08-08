#!/bin/zsh
# skeleton-audit-cites.sh — r0038 Audit.Skeleton stream (agent3).
#
# Why this exists: unused-theorems.sh answers a yes/no question ("is this name
# mentioned anywhere but its own declaration?") over the whole development. The
# r0038 audit needs more per declaration in one area: the `simp` tag, the
# declaring module, and — for the `S` label — *which* declarations cite it, so a
# citer can be named as evidence. It also needs to separate a self-citation
# (used only inside its own file's later proofs) from a cross-module citation,
# because a name cited only by its own file is weaker support than one another
# module consumes.
#
# Method: enumerate `theorem`/`lemma` declarations in the Audit.Skeleton modules
# (Skeleton/*, ClosureProperties*, Isomorphism/*), then grep the whole package
# for each bare final-component name as a whole word. Report, per declaration:
#   module | name | simp? | total mentions | mentions outside the declaring file
#   | up to three citing files
#
# LIMITS, same as unused-theorems.sh and stated for the same reason: matching is
# on the final name component as a whole word, so two same-named declarations in
# different namespaces collide and the count over-reports for that name; `simp`
# may fire a tagged lemma without naming it, so a zero here is not proof of
# deadness for a tagged lemma. Treat as evidence to read, not a verdict.
#
# Usage: scripts/skeleton-audit-cites.sh
set -e
cd "${0:A:h}/.."
pkg="ScottDomains/ScottDomains"

allfiles=(${(f)"$(find $pkg -name '*.lean' | sort)"})
myfiles=(${(f)"$(find $pkg/Skeleton $pkg/ClosureProperties $pkg/Isomorphism -name '*.lean' | sort)"})
myfiles+=($pkg/ClosureProperties.lean)

print -r -- "module|name|simp|total|extern|citers"
for f in ${(o)myfiles}; do
  m=${f#$pkg/}
  grep -nE '^(@\[[^]]*\] )?(theorem|lemma) ' $f | while IFS= read -r line; do
    decl=${line#*:}
    simp=no
    [[ $decl == @\[*simp* ]] && simp=yes
    nm=$(print -r -- "$decl" | sed -E 's/^(@\[[^]]*\] )?(theorem|lemma) +//; s/[ ({:[].*$//')
    short=${nm##*.}
    tot=$(grep -h -o -w -F -- "$short" $allfiles | wc -l | tr -d ' ')
    own=$(grep -h -o -w -F -- "$short" $f | wc -l | tr -d ' ')
    ext=$((tot - own))
    citers=$(grep -l -w -F -- "$short" $allfiles | sed "s|^$pkg/||" | grep -v "^$m\$" | head -3 | tr '\n' ',')
    print -r -- "$m|$nm|$simp|$tot|$ext|${citers%,}"
  done
done
