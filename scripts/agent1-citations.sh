#!/bin/zsh
# agent1-citations.sh — r0038, Audit.Foundations stream.
#
# What it measures: for every `theorem`/`lemma` declared in agent1's 19 modules,
# how many times the name occurs anywhere in the ScottDomains source tree, how
# many of those occurrences are outside the declaring file, and which files those
# are. That is the evidence for the `S` (support — something cites it) label of
# the r0038 classification, and its absence is the evidence for `U`.
#
# Why it exists rather than `scripts/unused-theorems.sh`: that script answers a
# yes/no question ("does this name occur exactly once in the whole tree?") and
# prints no call sites. The audit needs the citing file named, per the plan's
# "name one citing declaration", and needs it for the used names too — not only
# for the ones that occur exactly once.
#
# Output is one pipe-delimited row per declaration:
#   module | name | simp | total | own | extern | first three external files
# `total` counts every whole-word occurrence including the declaration line;
# `own` counts occurrences inside the declaring file other than the declaration
# line (a lemma used only by its own file's later proofs is still used);
# `extern` counts occurrences in other files.
#
# LIMITS, the same shape as unused-theorems.sh states them:
#   * final-component matching collides across namespaces, so a name shared by
#     two declarations shows the union of both call-site sets — this
#     over-reports citations and therefore under-reports the `U` label;
#   * `simp`/`aesop` can fire a tagged lemma without naming it, so extern=0 for a
#     `@[simp]` lemma is not proof that it never fires;
#   * a hit inside a block comment (r0020 commented six declarations out in
#     place, and module docstrings name lemmas in prose) is a mention, not a
#     use. The counts do not distinguish them; the reader checks the row.
# So treat the output as evidence to read, never as a delete list.
#
# Usage: scripts/agent1-citations.sh [--sites <name>]
#   with --sites, print every occurrence of one name as file:line: text.
set -e
cd "${0:A:h}/.."
pkg="ScottDomains/ScottDomains"

mods=(
  WayBelow Domain Powerset ScottHom StepFunction FunctionSpaceDomain
  CompactFunction FunctionSpaceCountable Product Currying Lift StrictHom
  Smash CoalescedSum FixedPoint UniformFixedPoint EffectivePresentation
  ComputableFunction ExistingTheories
)

allfiles=(${(f)"$(find $pkg -name '*.lean' | sort)"})

if [[ "$1" == "--sites" ]]; then
  nm=$2
  for g in $allfiles; do
    grep -n -w -F -- "$nm" $g 2>/dev/null | while IFS= read -r line; do
      print -r -- "${g#$pkg/}:$line"
    done
  done
  exit 0
fi

print -r -- "module|name|simp|total|own|extern|extern_files"
for m in $mods; do
  f="$pkg/$m.lean"
  grep -nE '^(@\[[^]]*\] )?(theorem|lemma) ' $f | while IFS=: read -r ln rest; do
    nm=$(print -r -- "$rest" | sed -E 's/^(@\[[^]]*\] )?(theorem|lemma) +//; s/[ ({:\[].*$//; s/^.*\.//')
    [[ -z "$nm" ]] && continue
    simp=no
    print -r -- "$rest" | grep -qE '^@\[[^]]*simp[^]]*\]' && simp=yes
    total=0; own=0; extern=0; efiles=()
    for g in $allfiles; do
      c=$(grep -c -w -F -- "$nm" $g 2>/dev/null || true)
      (( c == 0 )) && continue
      total=$((total + c))
      if [[ "$g" == "$f" ]]; then
        own=$((own + c - 1))
      else
        extern=$((extern + c)); efiles+=("${g#$pkg/}")
      fi
    done
    print -r -- "$m.lean|$nm|$simp|$total|$own|$extern|${(j:,:)efiles[1,3]}"
  done
done
