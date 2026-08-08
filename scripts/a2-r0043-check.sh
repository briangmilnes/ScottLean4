#!/bin/zsh
# a2-r0043-check.sh — for each declaration named on the command line, print its
# elaborated type (`#check @d`) and its axiom dependencies (`#print axioms d`),
# as ONE allowlisted command with no chaining, no pipes and no heredoc.
#
# Why this exists (r0043): `scripts/axioms.sh` prints axioms only. Re-measuring a
# row as `S+P` requires two facts about the named declaration — that it exists in
# the compiled environment, and that its *type* is the paper's proposition. A
# report that quotes a type read out of the source file is quoting the source,
# not the kernel; `#check @d` quotes the kernel, with every implicit argument and
# instance made explicit. `#print axioms` then shows the proof is not a `sorryAx`.
#
# Usage:
#   scripts/a2-r0043-check.sh [-i <module>]… <decl>…
#
#   -i <module>   extra import (repeatable), for a declaration whose namespace
#                 path is not its module path (e.g. `ScottHom.IsEmbedding…`
#                 lives in `ScottDomains.Projection`).
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

(( $#decls )) || { print -u2 "usage: scripts/a2-r0043-check.sh [-i module]… <decl>…"; exit 2 }

for d in $decls; do
  parts=(${(s:.:)d})
  (( $#parts > 1 )) && imports+=("${(j:.:)parts[1,-2]}")
done

tmp="$(mktemp /tmp/a2-r0043-XXXXXX.lean)"
trap 'rm -f "$tmp"' EXIT

typeset -U imports
for m in $imports; do
  [[ -f "$pkg/${m//.//}.lean" ]] && print -- "import $m" >> "$tmp"
done
print -- "" >> "$tmp"
print -- "set_option pp.numericTypes false" >> "$tmp"
print -- "" >> "$tmp"
for d in $decls; do
  print -- "#check @$d" >> "$tmp"
  print -- "#print axioms $d" >> "$tmp"
done

cd "$pkg"
lake env lean "$tmp"
