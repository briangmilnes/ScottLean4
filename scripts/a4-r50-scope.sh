#!/usr/bin/env bash
# a4-r50-scope.sh — reproduce the r0050 plan's 126-declaration measurement.
#
# The plan tabulates 126 "defining declarations" under five prefixes
# (thm/lem/lemma/theorem/prop). This script recomputes that count over
# ScottDomains/ScottDomains/**/*.lean so agent4 can confirm the exact scope of
# the rename before touching source: the target set is declarations whose name
# BEGINS with one of those prefixes immediately followed by a digit, not every
# declaration whose name merely mentions a number.
set -u
ROOT=/home/milnes/projects/ScottLean4-agent4/ScottDomains/ScottDomains
grep -rhnE '^(private |protected |noncomputable )*(theorem|lemma|def|abbrev) +[A-Za-z_]' --include='*.lean' "$ROOT" \
| awk '{
    line=$0; sub(/^[0-9]+:/,"",line);
    while (line ~ /^(private|protected|noncomputable) /) sub(/^(private|protected|noncomputable) /,"",line);
    rest=line; sub(/^[a-z]+ +/,"",rest);
    name=rest; sub(/[ ({\[:.].*/,"",name);
    if (name ~ /^(thm|lem|lemma|theorem|prop|cor)[0-9]/) {
      p=name; sub(/[0-9].*/,"",p); cnt[p]++; total++;
    }
  }
  END { for (k in cnt) printf "%s\t%d\n", k, cnt[k]; printf "TOTAL\t%d\n", total }'
