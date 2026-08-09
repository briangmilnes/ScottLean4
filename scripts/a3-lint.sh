#!/usr/bin/env bash
# r0044 / agent3 — run Batteries' `unusedArguments` environment linter over the
# whole ScottDomains package (instrument 1 of the Class 2 vacuity sweep).
#
# Elaborates scripts/a3-lint.lean under `lake env lean`, which puts the package's
# own oleans plus Mathlib/Batteries on LEAN_PATH without adding the file to the
# build.  Output (the linter's report) goes to
# ScottDomains/logs/a3-lint-YYYYMMDD-HHMMSS.<role>.log per the project logging
# standard, and is echoed to stdout.
#
# Exit status is `lean`'s: 1 when the linter reports failures (it uses logError),
# 0 when every check passes.  Both are results; neither is a script error.
set -u

root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
pkg="$root/ScottDomains"
case "$root" in
  *-agent[0-9]*) role="agent${root##*-agent}" ;;
  *)             role="orchestrator" ;;
esac
stamp=$(date +%Y%m%d-%H%M%S)
log="$pkg/logs/a3-lint-$stamp.$role.log"

cd "$pkg" || exit 2
{
  echo "# r0044 agent3 instrument 1: Batteries unusedArguments over package ScottDomains"
  echo "# started $(date -Iseconds)"
} >"$log"
lake env lean "$root/scripts/a3-lint.lean" 2>&1 \
  | sed 's/\x1b\[[0-9;]*[mGKHABCDEFJST]//g' >>"$log"
rc=${PIPESTATUS[0]}
echo "# lean exit $rc" >>"$log"
cat "$log"
echo "wrote $log"
exit "$rc"
