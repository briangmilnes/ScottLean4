#!/usr/bin/env bash
# r0044 / agent3 — elaborate one scripts/*.lean file against the built ScottDomains
# package and log the output.
#
#   scripts/a3-run-lean.sh <stem>            e.g.  a3-diag, a3-vacuity
#
# Runs `lake env lean scripts/<stem>.lean` from the package root so the package's
# oleans and Mathlib/Batteries are on LEAN_PATH, without adding the file to the
# lake target (the build must stay at 1339 jobs / 0 errors / 0 warnings).
# Output is ANSI-stripped and written to
# ScottDomains/logs/<stem>-YYYYMMDD-HHMMSS.<role>.log, then echoed.
#
# Remaining positional arguments are exported as A3_ARGS for the Lean file to
# read with `IO.getEnv "A3_ARGS"` — this is how the vacuity instrument takes its
# module filter, so agent4 and agent5 can point it at their own areas.
set -u

stem=${1:?usage: a3-run-lean.sh <stem> [filter]}
shift || true
root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
pkg="$root/ScottDomains"
case "$root" in
  *-agent[0-9]*) role="agent${root##*-agent}" ;;
  *)             role="orchestrator" ;;
esac
stamp=$(date +%Y%m%d-%H%M%S)
log="$pkg/logs/$stem-$stamp.$role.log"

export A3_ARGS="$*"
cd "$pkg" || exit 2
{
  echo "# r0044 agent3: lake env lean scripts/$stem.lean"
  echo "# A3_ARGS=$A3_ARGS"
  echo "# started $(date -Iseconds)"
} >"$log"
lake env lean "$root/scripts/$stem.lean" 2>&1 \
  | sed 's/\x1b\[[0-9;]*[mGKHABCDEFJST]//g' >>"$log"
rc=${PIPESTATUS[0]}
echo "# lean exit $rc" >>"$log"
cat "$log"
echo "wrote $log"
exit "$rc"
