#!/usr/bin/env bash
# a8-claim-check.sh — THE STANDING CHECK. One command, run once per round after
# the merge build, that re-asks the elaborated environment every question the
# package's prose answers, and prints only what CHANGED since the last round.
#
# ------------------------------------------------------------------------------
# Why this exists, as a measurement
# ------------------------------------------------------------------------------
# r0046 measured eight false proof-claims and found SEVEN OF THE EIGHT were true
# when written. The defect mode is not carelessness; it is staleness. Nothing in
# the toolchain signals it: the claim is prose, so there is no `sorry`, no failed
# elaboration, and no build warning. The package has been at `sorry` 0 for five
# rounds while its prose drifted.
#
# Staleness is also fast. r0046 measured two sites falsified by a LATER COMMIT IN
# THE ROUND THAT WROTE THEM. A per-sweep instrument — one agent, one round,
# hand-driven — cannot catch that; a per-round one can.
#
# ------------------------------------------------------------------------------
# Why a BASELINE and not a report
# ------------------------------------------------------------------------------
# The instruments below emit 69 citation rows and 55 unbackticked absence claims
# on a clean tree. A check that prints 124 rows every round is read once and then
# ignored, and its output is indistinguishable from its own history. So the
# accepted state is committed as `analyses/a8-claim-baseline.tsv` and this script
# prints exactly two lists:
#
#     NEW       a site that is a defect now and was not in the baseline
#     RESOLVED  a baseline site that no longer fires
#
# A round with no prose defect prints two empty lists and exits 0. Reviewing the
# baseline is then the only judgement call, and it happens once per site.
#
# ------------------------------------------------------------------------------
# What is asked, and of what
# ------------------------------------------------------------------------------
# Three questions, all answered against the environment `lake build` produced,
# never against a source line:
#
#   1. DANGLING CITATION — a backticked name in prose that resolves to no
#      constant, or resolves only under a different qualifier. `a7-cite-scan.py`
#      lexes the comments, `a7-resolve.py` matches on COMPONENT BOUNDARIES
#      against 267510 constants. This is the check that would have caught
#      `Colimit.lean:59`'s `etaChain_not_wellDefined` at its FIRST sighting
#      instead of its third.
#
#   2. PROOF-CLAIM vs ENVIRONMENT — `a4-claim-scan.py`'s P1-P4: prose says a
#      Prop-valued `def` is proved and no theorem concludes it, or says it is
#      open and one does, or says a name is absent and the declaring module has
#      it.
#
#   3. ABSENCE-CLAIM LOCUS — `a8-r49-absence.py` partitions the claims detector 2
#      cannot resolve (subject is an English noun phrase) into QUOTE / MATHLIB /
#      PKG / MATH. Only PKG rows carry a standing obligation, and the count of
#      them is the number to watch: it is where r0046's sites 7 and 8 hid, and
#      where r0049 found four more.
#
# ------------------------------------------------------------------------------
# Cost
# ------------------------------------------------------------------------------
# Work: two Lean elaborations over the 118-module import prologue (the
# environment dump and the declaration index) plus three Python passes over 9273
# sentences and 8996 citations. Span: the two elaborations are sequential, the
# second reusing nothing from the first.
#
# Measured, r0049/agent8, after a completed `lake build`, two runs against an
# unchanged baseline: wall 12.31 s and 13.05 s, peak RSS 1974 MiB and 1974 MiB,
# exit 0, NEW 0, RESOLVED 0 both times. The round's own incremental build was
# 6.36 s and its cold build 4:00.97, so the check costs about 5% of a cold build
# and runs once per round.
#
# ------------------------------------------------------------------------------
# Usage
# ------------------------------------------------------------------------------
#     scripts/a8-claim-check.sh [-u]      -u rewrites the baseline from this run
#
# Exit 0 when NEW is empty; exit 1 when it is not. Run it after `lake build`; it
# refuses to run without one, because every question it asks is about the
# `.olean`s.

set -uo pipefail

root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
pkg="$root/ScottDomains"
case "$root" in
  *-agent[0-9]|*-agent[0-9][0-9]) role="agent${root##*-agent}" ;;
  *) role="orchestrator" ;;
esac

update=0
[ "${1:-}" = "-u" ] && update=1

work="${TMPDIR:-/tmp}/a8-claim-check.$$"
mkdir -p "$work"
trap 'rm -rf "$work"' EXIT

stamp=$(date +%Y%m%d-%H%M%S)
log="$pkg/logs/a8-claim-check-$stamp.$role.log"
baseline="$pkg/analyses/a8-claim-baseline.tsv"
# The current run's obligation set is scratch, not a project artifact: on a clean
# tree it is byte-identical to the baseline, and `analyses/` must not hold two
# copies of one thing.
current="$work/a8-claim-current.tsv"

if [ ! -d "$pkg/.lake/build/lib/lean/ScottDomains" ]; then
  echo "a8-claim-check: no build products under $pkg/.lake — run scripts/compile.sh first"
  exit 2
fi

{
  echo "# a8-claim-check $stamp $role"
  echo "# root $root"

  echo "== 1. environment dump =="
  "$root/scripts/a8-r49-env.sh" "$work/env-names.tsv"

  echo "== 2. citation resolution =="
  "$root/scripts/a8-r49-cites.sh" "$work/unresolved.tsv" "$work/env-names.tsv"

  echo "== 3. declaration index =="
  "$root/scripts/a6-env-scan.sh" "$work/decls.tsv" "$root/scripts/a4-decl-query.lean"

  echo "== 4. claim scan =="
  python3 "$root/scripts/a4-claim-scan.py" "$work/decls.tsv" "$pkg" "$work/claims.tsv"

  echo "== 5. absence-claim locus =="
  python3 "$root/scripts/a8-r49-absence.py" "$work/claims.tsv.unresolvable" "$work/absence.tsv"
} > "$log" 2>&1

# One row per standing obligation: kind, site, subject. The `absence-claim` tier
# is excluded by construction — there the name is cited AS EVIDENCE OF ITS OWN
# ABSENCE, so non-resolution is the correct outcome and not a defect.
{
  awk -F'\t' '$5 != "absence-claim" { sub(/.*\/ScottDomains\/ScottDomains\//, "ScottDomains/ScottDomains/", $1);
              print "CITE\t" $1 ":" $2 "\t" $4 "\t" $5 }' "$work/unresolved.tsv"
  awk -F'\t' '{ sub(/.*\/ScottDomains\//, "ScottDomains/", $2);
              print "CLAIM\t" $2 ":" $3 "\t" $5 "\t" $1 }' "$work/claims.tsv"
  awk -F'\t' '$1 == "PKG" { print "ABSENCE\t" $2 "\t" $4 "\t" $1 }' "$work/absence.tsv"
} | LC_ALL=C sort -u > "$current"

if [ ! -f "$baseline" ]; then
  cp "$current" "$baseline"
  echo "a8-claim-check: no baseline — wrote $(wc -l < "$baseline") rows to $baseline"
  echo "a8-claim-check: log $log"
  exit 0
fi

LC_ALL=C comm -13 "$baseline" "$current" > "$work/new.tsv"
LC_ALL=C comm -23 "$baseline" "$current" > "$work/gone.tsv"

echo "a8-claim-check: $(wc -l < "$current") standing obligations, baseline $(wc -l < "$baseline")"
echo "--- NEW ($(wc -l < "$work/new.tsv")) ---"
cat "$work/new.tsv"
echo "--- RESOLVED ($(wc -l < "$work/gone.tsv")) ---"
cat "$work/gone.tsv"
echo "a8-claim-check: log $log"

if [ "$update" = 1 ]; then
  cp "$current" "$baseline"
  echo "a8-claim-check: baseline updated"
  exit 0
fi

[ -s "$work/new.tsv" ] && exit 1
exit 0
