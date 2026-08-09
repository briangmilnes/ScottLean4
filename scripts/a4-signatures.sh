#!/bin/zsh
# a4-signatures.sh — print the *elaborated* signature of each named declaration,
# read from the built .olean rather than from a source line.
#
# Usage:
#   scripts/a4-signatures.sh ScottDomains.PowerdomainMap.Rep.SmythImageIso …
#
# Why this exists: r0044 measured 218 sites where a cited name does not resolve
# and 40 live docstrings asserting something the code does not say, so a source
# line is not evidence about what a declaration states. `#check @d` against the
# compiled environment is. This is the companion of `scripts/axioms.sh`, which
# answers "what does it depend on"; this one answers "what does it say".
#
# One command, no chaining, no pipes, no heredoc — same shape as axioms.sh so it
# matches the same permission prefix.
set -e
cd "${0:A:h}/.."
root="$PWD"
pkg="$root/ScottDomains"

imports=()
decls=()
while (( $# )); do
  case "$1" in
    -i) imports+=("$2"); shift 2 ;;
    *)  decls+=("$1"); shift ;;
  esac
done

(( $#decls )) || { print -u2 "usage: scripts/a4-signatures.sh [-i module]… <decl>…"; exit 2 }

for d in $decls; do
  parts=(${(s:.:)d})
  while (( $#parts > 1 )); do
    m="${(j:.:)parts[1,-2]}"
    if [[ -f "$pkg/${m//.//}.lean" ]]; then
      imports+=("$m")
      break
    fi
    parts=($parts[1,-2])
  done
done

tmp="$(mktemp /tmp/a4sig-XXXXXX.lean)"
trap 'rm -f "$tmp"' EXIT

typeset -U imports
for m in $imports; do
  [[ -f "$pkg/${m//.//}.lean" ]] && print -- "import $m" >> "$tmp"
done
print -- "" >> "$tmp"
print -- "set_option pp.numericTypes false" >> "$tmp"
for d in $decls; do
  print -- "#check @$d" >> "$tmp"
done

cd "$pkg"
lake env lean "$tmp"
