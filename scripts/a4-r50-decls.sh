#!/usr/bin/env bash
# a4-r50-decls.sh — enumerate every top-level declaration whose NAME contains a
# digit, across agent4's r0050 partition of ScottDomains modules.
#
# Why it exists: r0050 renames every numbered-result declaration to the
# theorem_<N>/lemma_<N>/proposition_<N> standard. The candidate set is exactly
# the declarations whose name carries a printed number, so this script prints
# file:line:kind:name for each, sorted by file. It is a discovery aid only — it
# never edits Lean source (renames are Edit-driven and compiler-checked).
set -u
ROOT=/home/milnes/projects/ScottLean4-agent4/ScottDomains/ScottDomains
FILES=$(printf '%s\n' \
  "$ROOT"/Effective/*.lean \
  "$ROOT"/Audit/*.lean \
  "$ROOT"/LemThirty.lean \
  "$ROOT"/BifiniteUniversal.lean \
  "$ROOT"/PRep.lean "$ROOT"/PRepFun.lean "$ROOT"/PRepSum.lean \
  "$ROOT"/PowerdomainMapRep.lean \
  "$ROOT"/Lemma28AtU.lean \
  "$ROOT"/A1Lemma24.lean "$ROOT"/A1Theorem2.lean "$ROOT"/A1R46.lean \
  "$ROOT"/A2Lemma28.lean "$ROOT"/A2Thm29Universal.lean \
  "$ROOT"/A3Lemma30Schemes.lean "$ROOT"/A3Thm29.lean \
  "$ROOT"/A4Lemma17Fun.lean "$ROOT"/A4PowerdomainRep.lean \
  "$ROOT"/A5Thm29Finite.lean "$ROOT"/A5Unfinished.lean \
  "$ROOT"/A6ProjectionBifinite.lean \
  "$ROOT"/A7Thm26Arity.lean "$ROOT"/A7SneqRows.lean)

for f in $FILES; do
  [ -f "$f" ] || { echo "MISSING $f"; continue; }
  grep -nE '^(private |protected |noncomputable |)*(theorem|lemma|def|abbrev|instance|structure|inductive) +[A-Za-z_][A-Za-z0-9_'"'"'.]*' "$f" \
  | awk -v F="$f" '{
      line=$0; sub(/^[0-9]+:/,"",line); n=$0; sub(/:.*/,"",n);
      # strip leading modifiers
      gsub(/^ +/,"",line);
      while (line ~ /^(private|protected|noncomputable) /) sub(/^(private|protected|noncomputable) /,"",line);
      kind=line; sub(/ .*/,"",kind);
      rest=line; sub(/^[a-z]+ +/,"",rest);
      name=rest; sub(/[ ({\[:].*/,"",name);
      if (name ~ /[0-9]/) printf "%s:%s:%s:%s\n", F, n, kind, name;
    }'
done
