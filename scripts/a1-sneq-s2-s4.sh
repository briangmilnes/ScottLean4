#!/bin/zsh
# a1-sneq-s2-s4.sh — reproduce r0044 Class 1 / agent1: the `S≠` rows of Gunter &
# Scott §2, §3 and §4, split into under-specified / incorrectly specified /
# deliberately divergent.
#
# What it does, in order:
#   1. re-derives the row population from the r0040 and r0043 per-agent reports,
#      so the count is read out of the evidence rather than out of the plan;
#   2. prints the ELABORATED type and axiom footprint of every declaration the
#      classification rests on (`#check @d` against the built `.olean`, never a
#      source line);
#   3. runs the three greps that establish the negative halves — no
#      strict-step-function basis, no witness for the paper's `D → E` existential,
#      no second `¬ IsAlgebraic (ScottHom …)`;
#   4. runs the bounded-completeness probe for row 45.
#
# Read-only over the package: it elaborates and greps, and edits no `.lean` file.
# Everything it writes goes to stdout and to the scratchpad probe path.
set -e
cd "${0:A:h}/.."
root="$PWD"
here="${0:A:h}"
pkg="$root/ScottDomains"
scratch="/tmp/claude-1000/-home-milnes-projects-ScottLean4/ab3f8bb9-d928-40ef-b45c-b2c8efc2bd0e/scratchpad"

print -- "=== 1. row population, from the r0040/r0043 per-agent reports ==="
print -- "--- r0040 agent1, §2+§3 (expect 3 S-neq rows: 45, 53, 59) ---"
grep -n 'S≠' "$pkg/reports/r0040-report-from-agent1-to-orchestrator-property-coverage-s2-s3.md"
print -- "--- r0040 agent2, §4 to Lemma 10 (expect 2 S-neq rows: Lem 9.3, 9.5) ---"
grep -n 'S≠' "$pkg/reports/r0040-report-from-agent2-to-orchestrator-property-coverage-s4-lem10.md"
print -- "--- r0043 agent1 and agent2 re-measures, for rows added or moved ---"
grep -n 'S≠' "$pkg/reports/r0043-report-from-agent1-to-orchestrator-remeasure-s2-s3.md"
grep -n 'S≠' "$pkg/reports/r0043-report-from-agent2-to-orchestrator-remeasure-s4.md"

print -- ""
print -- "=== 2. the paper's sentences, printed pages 9, 11, 12 ==="
print -- "(pdftotext renders the strict arrow as '!' and drops 'fi'; see StatementRecovery.md)"
"$here/a5-paper-text.sh" "Gunter Scott 1990" "$scratch/gs1990.txt"
grep -n 'may recover from Gf' "$scratch/gs1990.txt"
grep -n 'such that the cpo D ! E is not a domain' "$scratch/gs1990.txt"
grep -n 'since the strict step functions form a basis' "$scratch/gs1990.txt"

print -- ""
print -- "=== 3. elaborated types and axiom footprints ==="
"$here/a1-elab.sh" \
  -i ScottDomains.Kleene.Graph \
  -i ScottDomains.ContinuousConstruction \
  -i ScottDomains.JungSFP \
  -i ScottDomains.PRepFun \
  ScottDomains.Kleene.sSup_recoverAt \
  ScottDomains.ContinuousConstruction.coe_eq_basisExtension_self \
  ScottDomains.JungSFP.lemma213 \
  ScottDomains.PRepFun.strictHomIsAlgebraic

"$here/a1-elab.sh" \
  -i ScottDomains.Skeleton.Recovered \
  -i ScottDomains.Isomorphism.Counterexample \
  ScottDomains.Recovered.lem9_3 \
  ScottDomains.Recovered.lem9_5 \
  ScottDomains.Isomorphism.lem9_3_printed_false \
  ScottDomains.Isomorphism.lem9_5_printed_false

print -- ""
print -- "=== 4. the negative halves ==="
print -- "--- row 59: any strict-step-function basis in the package? ---"
grep -rniE 'strictStep|stepStrict|strict step' "$pkg/ScottDomains" '--include=*.lean' || print -- "(no hits)"
print -- "--- row 53: every statement of the form (not) IsAlgebraic (ScottHom ...) ---"
grep -rn '¬ IsAlgebraic (ScottHom' "$pkg/ScottDomains" '--include=*.lean' || print -- "(no hits)"
print -- "--- row 53: every use of lemma213 (is it ever instantiated at a concrete pair?) ---"
grep -rn 'lemma213' "$pkg/ScottDomains" '--include=*.lean'

print -- ""
print -- "=== 5. row 45 probe: is [BoundedComplete beta] needed? ==="
"$here/a1-probe.sh" "$here/a1-probe45.lean"
