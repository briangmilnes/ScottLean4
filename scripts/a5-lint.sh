#!/bin/zsh
# a5-lint.sh — run Batteries' environment linters over the whole ScottDomains
# package and write a GRASE log.
#
# Why this exists: r0044 Class 2 asks for a mechanical sweep for theorems whose
# hypotheses go unused. Batteries' `unusedArguments` linter answers exactly that
# question against the *elaborated* declaration (the stored proof term), not
# against source text, so it is the instrument to try before writing one.
#
# Usage: scripts/a5-lint.sh [lean-file]
#   lean-file  defaults to scripts/a5-lint-unused.lean
#
# The driver file must live outside ScottDomains/ScottDomains/ so that
# scripts/counts.sh and `lake build` do not see it.
#
# Log: <checkout>/ScottDomains/logs/a5-lint-YYYYMMDD-HHMMSS.<role>.log
# (LoggingStandard.md naming; role from the worktree path, never a flag).
set -e

root="${0:A:h}/.."
cd "$root"
root="$PWD"

case "$root" in
  *-agent<->) role="${root##*-}" ;;
  *)          role="orchestrator" ;;
esac

src="${1:-$root/scripts/a5-lint-unused.lean}"
pkg="$root/ScottDomains"
logdir="$pkg/logs"
mkdir -p "$logdir"
stamp="$(date '+%Y%m%d-%H%M%S')"
log="$logdir/a5-lint-$stamp.$role.log"

{
  print -- "# $role — lake env lean $src"
  print -- "# checkout: $root"
  print -- "# started: $(date '+%Y-%m-%dT%H:%M:%S%:z')"
  print -- "# lean: $(cat "$pkg/lean-toolchain")"
  print -- "### === lint ==="
} > "$log"

cd "$pkg"
set +e
lake env lean "$src" 2>&1 | sed 's/\x1b\[[0-9;]*[mGKHABCDEFJST]//g' >> "$log"
rc=${pipestatus[1]}
set -e

hits=$(grep -cE '^#(check|print)|unused argument' "$log" || true)
print -- "--- times ---" >> "$log"
print -- "finished: $(date '+%Y-%m-%dT%H:%M:%S%:z')" >> "$log"
print -- "exit status: $rc" >> "$log"

print -- "a5-lint: exit $rc · lines $(wc -l < "$log") · 'unused argument' lines $hits"
print -- "a5-lint: log $log"
exit $rc
