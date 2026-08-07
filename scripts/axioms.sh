#!/bin/zsh
# axioms.sh — run `#print axioms` over a list of declarations, as ONE allowlisted
# command with no chaining, no pipes, and no heredoc.
#
# Usage:
#   scripts/axioms.sh ScottDomains.thm22 ScottDomains.lem23 …
#   scripts/axioms.sh -i ScottDomains.Universality -i ScottDomains.IdealCompletion \
#                     ScottDomains.Universality.thm25
#
#   -i <module>   extra import (repeatable). Every module named by a declaration's
#                 leading components is imported automatically, so -i is only for
#                 the composition check — importing modules that no single
#                 declaration forces, which is how r0028's duplicate-name clash
#                 was caught. `lake build` cannot catch that: it never imports two
#                 unrelated modules into one environment.
#
# Why this script exists: the audit used to be run as
#   cd ScottDomains && lake env lean /tmp/…/AxCheck.lean 2>&1 | head
# which is a compound command and therefore prompts for permission every time,
# however many of its parts are allowlisted. This is one command.
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

(( $#decls )) || { print -u2 "usage: scripts/axioms.sh [-i module]… <decl>…"; exit 2 }

# A declaration's module is its namespace path minus the final component; Lean
# resolves the rest, so importing the longest existing prefix is enough.
for d in $decls; do
  parts=(${(s:.:)d})
  (( $#parts > 1 )) && imports+=("${(j:.:)parts[1,-2]}")
done

tmp="$(mktemp /tmp/axioms-XXXXXX.lean)"
trap 'rm -f "$tmp"' EXIT

typeset -U imports                     # dedupe, keep order
for m in $imports; do
  [[ -f "$pkg/${m//.//}.lean" ]] && print -- "import $m" >> "$tmp"
done
print -- "" >> "$tmp"
for d in $decls; do
  print -- "#print axioms $d" >> "$tmp"
done

cd "$pkg"
lake env lean "$tmp"
