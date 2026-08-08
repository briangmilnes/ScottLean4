#!/bin/zsh
# a5-import-cone.sh — transitive `import ScottDomains.*` closure of a module, and
# a membership test.
#
# Why it exists: r0042 stream 5 was told the last `sorry`
# (`Skeleton/Section6.lean:197`) could be closed with a one-line
# `exact JungFinite.thm18_of_propertyM …`. That is only possible if
# `Skeleton.Section6` is NOT in the import cone of `JungFinite` / `JungNets`;
# otherwise the edit is an import cycle and `lake` refuses it. `lake build`
# reports a cycle only after you write the edit, so this measures it first.
#
# usage: a5-import-cone.sh <Module.Name> [Module.To.Look.For]
#   prints the closure, sorted, and — with a second argument — PRESENT/ABSENT.
set -e
pkg="${0:A:h}/../ScottDomains"
root="$1"
needle="$2"

typeset -a queue seen
queue=("$root")
seen=()

while (( ${#queue} )); do
  m="${queue[1]}"
  shift queue
  if (( ${seen[(Ie)$m]} )); then continue; fi
  seen+=("$m")
  f="$pkg/${m//.//}.lean"
  [[ -f "$f" ]] || continue
  for i in ${(f)"$(grep -oE '^import ScottDomains[A-Za-z0-9_.]*' "$f" | cut -d' ' -f2)"}; do
    queue+=("$i")
  done
done

print -l ${(o)seen}
echo "--- modules in cone of $root: ${#seen}"
if [[ -n "$needle" ]]; then
  if (( ${seen[(Ie)$needle]} )); then
    echo "$needle: PRESENT in the cone of $root  (importing $root from $needle is a CYCLE)"
  else
    echo "$needle: ABSENT from the cone of $root  (no cycle)"
  fi
fi
