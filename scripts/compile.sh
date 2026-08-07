#!/bin/zsh
# compile.sh — run `lake build` under measurement and write a GRASE log.
#
# Why this exists: the cost of checking this development is not visible from a
# build's stdout. This wrapper records wall time, CPU time, peak resident set
# size, and the counts that matter (jobs, errors, warnings, `sorry`s), so build
# cost can be tracked across rounds rather than guessed at.
#
# Usage:
#   scripts/compile.sh [-r rNNNN] [lake build target ...]
#     -r rNNNN   round tag; written as the log's first line (GRASE rule 4.5)
#     targets    passed through to `lake build` (default: the whole library)
#
# Log: <checkout>/ScottDomains/logs/compile-YYYYMMDD-HHMMSS.<role>.log
#   Second-resolution stamp per ~/projects/GRASE/standards/LoggingStandard.md,
#   which supersedes GRASE rule 4.1's minute-resolution form; the trailing
#   .<role> slot is retained because these logs must be attributed to an agent.
#   <role> is agentN when the checkout path ends in -agentN, else orchestrator
#   (GRASE rules 0.6, 1.3). ANSI escapes are stripped (rule 4.4).
#
# Execution telemetry belongs in logs/, not analyses/ — this is a transcript of
# a run, not a data-product about the codebase.
#
# Exit status is `lake build`'s own, so this is a drop-in replacement in any
# check that tests whether the build succeeded.
set -e

root="${0:A:h}/.."                     # checkout root (this script lives in scripts/)
cd "$root"
root="$PWD"

round=""
if [[ "$1" == "-r" ]]; then
  round="$2"; shift 2
fi

# GRASE role slot: the worktree path decides it, never a flag.
case "$root" in
  *-agent<->) role="${root##*-}" ;;
  *)          role="orchestrator" ;;
esac

pkg="$root/ScottDomains"
logdir="$pkg/logs"
mkdir -p "$logdir"

stamp="$(date '+%Y%m%d-%H%M%S')"
log="$logdir/$(basename "$0" .sh)-$stamp.$role.log"
metrics="$(mktemp)"
trap 'rm -f "$metrics"' EXIT

{
  [[ -n "$round" ]] && print -- "# $round"
  print -- "# $role — lake build ${@:-(whole library)}"
  print -- "# checkout: $root"
  print -- "# started: $(date '+%Y-%m-%dT%H:%M:%S%:z')"
  print -- "# lean: $(cd "$pkg" && cat lean-toolchain)"
  print -- "# host: $(uname -sr) $(uname -m), $(nproc) cores"
  print -- "### === lake build ${@} ==="
} > "$log"

# GNU time writes its report to a separate file so it cannot interleave with
# build output. `set -e` is suspended for the build itself: a failing build must
# still produce a complete log and its own exit status.
set +e
cd "$pkg"
/usr/bin/time -v -o "$metrics" lake build "$@" 2>&1 \
  | sed 's/\x1b\[[0-9;]*[mGKHABCDEFJST]//g' \
  | tee -a "$log"
rc=${pipestatus[1]}
set -e
cd "$root"

# Counts come from the log, so they describe exactly what was recorded.
jobs=$(grep -oE 'Build completed successfully \([0-9]+ jobs\)' "$log" | grep -oE '[0-9]+' | tail -1)
errors=$(grep -cE '^error:' "$log" || true)
warns=$(grep -cE "^warning:.*declaration uses .sorry" "$log" || true)
otherwarns=$(grep -cE '^warning:' "$log" || true)
otherwarns=$(( otherwarns - warns ))

wall=$(grep -E 'Elapsed \(wall clock\)' "$metrics" | sed 's/.*: //')
user=$(grep -E '^\s*User time' "$metrics" | sed 's/.*: //')
sys=$(grep -E '^\s*System time' "$metrics" | sed 's/.*: //')
cpu=$(grep -E 'Percent of CPU' "$metrics" | sed 's/.*: //')
rsskb=$(grep -E 'Maximum resident set size' "$metrics" | sed 's/.*: //')
rssmb=$(( rsskb / 1024 ))

# The two `--- times ---` field names are verbatim from the logging standard, so
# one parser reads every project's logs. The build-specific counts follow.
{
  print -- "--- times ---"
  print -- "Elapsed (wall clock): $wall"
  print -- "Maximum resident set size (kbytes): $rsskb"
  print -- "--- build ---"
  print -- "finished:       $(date '+%Y-%m-%dT%H:%M:%S%:z')"
  print -- "exit status:    $rc"
  print -- "user cpu:       ${user}s"
  print -- "system cpu:     ${sys}s"
  print -- "cpu use:        $cpu"
  print -- "peak rss:       ${rssmb} MiB"
  print -- "jobs:           ${jobs:-n/a}"
  print -- "errors:         $errors"
  print -- "sorry decls:    $warns"
  print -- "other warnings: $otherwarns"
} >> "$log"

print -- "compile: exit $rc · wall $wall · peak rss ${rssmb} MiB · jobs ${jobs:-n/a} · errors $errors · sorry $warns · other warnings $otherwarns"
print -- "compile: log $log"
exit $rc
