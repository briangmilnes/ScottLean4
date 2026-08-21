#!/bin/zsh
# compile-scott1972.sh — build Ericson's Scott 1972 package under measurement.
#
# Why this exists: compile.sh builds one package, ScottDomains, at a path fixed
# in the script. Ericson/scott1972 is a separate lake package with its own
# toolchain pin (leanprover/lean4:v4.30.0, two point releases behind the v4.32.2
# the rest of the repo uses) and its own Mathlib checkout, so it needs its own
# invocation. Building it answers a question the editor cannot: whether every
# module elaborates from a cold start, independent of what the VS Code Lean
# server managed to do before it died.
#
# Log: <checkout>/ScottDomains/logs/compile-scott1972-YYYYMMDD-HHMMSS.<role>.log
#   per ~/projects/GRASE/standards/LoggingStandard.md. ANSI escapes are stripped
#   (GRASE rule 4.4). Exit status is `lake build`'s own.
#
# Usage: scripts/compile-scott1972.sh [-r rNNNN] [lake target ...]
set -e

root="${0:A:h}/.."
cd "$root"
root="$PWD"

round=""
if [[ "$1" == "-r" ]]; then
  round="$2"; shift 2
fi

case "$root" in
  *-agent<->) role="${root##*-}" ;;
  *)          role="orchestrator" ;;
esac

pkg="$root/Ericson/scott1972"
logdir="$root/ScottDomains/logs"
mkdir -p "$logdir"

stamp="$(date '+%Y%m%d-%H%M%S')"
log="$logdir/$(basename "$0" .sh)-$stamp.$role.log"
metrics="$(mktemp)"
raw="$(mktemp)"
trap 'rm -f "$metrics" "$raw"' EXIT

{
  [[ -n "$round" ]] && print -- "# $round"
  print -- "# $role — lake build ${@:-(whole library)}"
  print -- "# package: $pkg"
  print -- "# started: $(date '+%Y-%m-%dT%H:%M:%S%:z')"
  print -- "# lean: $(cat "$pkg/lean-toolchain")"
  print -- "# host: $(uname -sr) $(uname -m), $(nproc) cores"
  print -- "### === lake build ${@} ==="
} > "$log"

set +e
cd "$pkg"
/usr/bin/time -v -o "$metrics" lake build "$@" > "$raw" 2>&1
rc=$?
set -e
cd "$root"

sed 's/\x1b\[[0-9;]*[mGKHABCDEFJST]//g' "$raw" >> "$log"

# Lean diagnostics carry a source position; Lake's own summary lines do not.
# Counting them together inflates the error count, so they are counted apart.
jobs=$(grep -oE 'Build completed successfully \([0-9]+ jobs\)' "$log" | grep -oE '[0-9]+' | tail -1)
diags=$(grep -cE '^error: [^ ]+\.lean:[0-9]+:[0-9]+:' "$log" || true)
errlines=$(grep -cE '^error:' "$log" || true)
lakeerrs=$(( errlines - diags ))
warns=$(grep -cE "^warning:.*declaration uses .sorry" "$log" || true)
otherwarns=$(grep -cE '^warning:' "$log" || true)
otherwarns=$(( otherwarns - warns ))

wall=$(grep -E 'Elapsed \(wall clock\)' "$metrics" | sed 's/.*: //')
rsskb=$(grep -E 'Maximum resident set size' "$metrics" | sed 's/.*: //')
rssmb=$(( rsskb / 1024 ))

{
  print -- "--- times ---"
  print -- "Elapsed (wall clock): $wall"
  print -- "Maximum resident set size (kbytes): $rsskb"
  print -- "--- build ---"
  print -- "finished:         $(date '+%Y-%m-%dT%H:%M:%S%:z')"
  print -- "exit status:      $rc"
  print -- "jobs:             ${jobs:-n/a}"
  print -- "lean diagnostics: $diags"
  print -- "lake errors:      $lakeerrs"
  print -- "sorry decls:      $warns"
  print -- "other warnings:   $otherwarns"
} >> "$log"

print -- "compile-scott1972: exit $rc · wall $wall · mem ${rssmb} MiB · jobs ${jobs:-n/a} · diagnostics $diags · lake errors $lakeerrs · sorry $warns · other warnings $otherwarns"
print -- "compile-scott1972: log $log"
exit $rc
