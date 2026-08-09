#!/bin/zsh
# a1-elab.sh — print the ELABORATED type of each named declaration, plus its
# axiom footprint, as ONE allowlisted command (no chaining, no pipe, no heredoc).
#
# Why this exists (r0044, Class 1, agent1): the round's evidence rule is that a
# claim about a declaration is checked against the built `.olean`, never read off
# a source line. A source line can carry binders that elaborate away, implicit
# instance arguments the reader never sees, and `variable`-block hypotheses that
# do not appear at the point of the `theorem` keyword. `#check @d` forces every
# binder — universe, implicit, instance — into the printed type, so what is
# printed is what the kernel accepted.
#
# Usage:
#   scripts/a1-elab.sh -i ScottDomains.Skeleton.Recovered ScottDomains.Recovered.lem9_3
#
#   -i <module>   module to import (repeatable). Unlike scripts/axioms.sh this
#                 script does NOT guess the module from the namespace: the
#                 declarations this round examines live in modules whose path
#                 differs from their namespace (`ScottDomains.Recovered.lem9_3`
#                 is in `ScottDomains/Skeleton/Recovered.lean`), which is exactly
#                 the case axioms.sh's prefix heuristic gets wrong.
#
# Output per declaration: the `#check @d` type and the `#print axioms d` line.
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

(( $#decls )) || { print -u2 "usage: scripts/a1-elab.sh -i <module>… <decl>…"; exit 2 }

tmp="$(mktemp /tmp/a1-elab-XXXXXX.lean)"
trap 'rm -f "$tmp"' EXIT

typeset -U imports
for m in $imports; do
  [[ -f "$pkg/${m//.//}.lean" ]] && print -- "import $m" >> "$tmp"
done
print -- "" >> "$tmp"
# Full binder detail: no implicit-argument elision, no notation folding away the
# instance arguments that decide whether a statement is a weakening.
print -- "set_option pp.piBinderTypes true" >> "$tmp"
print -- "set_option pp.coercions true" >> "$tmp"
print -- "" >> "$tmp"
for d in $decls; do
  print -- "#check @$d" >> "$tmp"
  print -- "#print axioms $d" >> "$tmp"
done

cd "$pkg"
lake env lean "$tmp"
