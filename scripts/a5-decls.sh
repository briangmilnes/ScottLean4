#!/bin/zsh
# a5-decls.sh — r0038 agent5 audit: enumerate every theorem/lemma declaration in
# the §7 representability stack, with its module, line number, `@[simp]` status,
# and the head of its statement.
#
# Why this exists: the audit deliverable is one table row per theorem across 403
# declarations in 12 modules. Reading 7820 lines of Lean by eye and transcribing
# names is both slow and error-prone; this emits the row skeleton mechanically so
# only the *label* and *evidence* columns are human work.
#
# Counting rule is exactly counts.sh's: a line starting with `theorem` or
# `lemma`, optionally preceded by one attribute group. Totals therefore agree
# with scripts/module-counts.sh.
#
# Output: TSV — module<TAB>line<TAB>simp<TAB>name<TAB>statement-head
# Usage: scripts/a5-decls.sh
set -e
cd "${0:A:h}/.."
pkg="ScottDomains/ScottDomains"

mods=(UniversalDomain Universality RecursiveDomain Combinator CombinatorRep \
      Dyadic Atomless PRepresentable PRep PRepFun PRepSum Lemma28AtU)

for m in $mods; do
  f="$pkg/$m.lean"
  grep -nE '^(@\[[^]]*\] )?(theorem|lemma) ' $f \
    | awk -v M="$m" '
      {
        p = index($0, ":"); ln = substr($0, 1, p-1); r = substr($0, p+1)
        simp = (r ~ /^@\[[^]]*simp/) ? "SIMP" : "no"
        sub(/^@\[[^]]*\] +/, "", r)
        sub(/^(theorem|lemma) +/, "", r)
        nm = r
        sub(/[ ({:\[].*$/, "", nm)
        printf "%s\t%s\t%s\t%s\t%s\n", M, ln, simp, nm, r
      }'
done
