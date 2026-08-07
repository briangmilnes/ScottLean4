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
metrics="$(mktemp)"                    # GNU time -v report
raw="$(mktemp)"                        # unfiltered build output, streamed from
rssfile="$(mktemp)"                    # peak process-group RSS, from the sampler
trap 'rm -f "$metrics" "$raw" "$rssfile"' EXIT

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
#
# Two memory figures are recorded, because they answer different questions.
# GNU time's "Maximum resident set size" is the peak of the single largest
# process in the tree — it does NOT add up concurrent Lean workers, so it
# understates what a parallel build needs. The sampler below sums RSS across the
# build's own process group every 200 ms and keeps the maximum, which is the
# figure to size RAM against. `setsid` puts the build in its own process group so
# the sum excludes builds running concurrently in the agent worktrees.
set +e
cd "$pkg"
setsid /usr/bin/time -v -o "$metrics" lake build "$@" > "$raw" 2>&1 &
bpid=$!
pgid=$(ps -o pgid= -p $bpid | tr -d ' ')

(
  peakrss=0
  peakpss=0
  while kill -0 $bpid 2>/dev/null; do
    pids=(${(f)"$(ps -eo pid=,pgid= | awk -v g="$pgid" '$2==g {print $1}')"})
    rss=0
    pss=0
    for p in $pids; do
      # Pss apportions each shared page by the number of processes mapping it,
      # so summing it does not double-count Mathlib's mmap'd .oleans. Summing
      # Rss does. Both are recorded; Pss is the true footprint.
      read -r r s <<< "$(awk '/^Rss:/ {rr+=$2} /^Pss:/ {pp+=$2} END {print rr+0, pp+0}' \
        /proc/$p/smaps_rollup 2>/dev/null)"
      (( rss += r ))
      (( pss += s ))
    done
    (( rss > peakrss )) && peakrss=$rss
    (( pss > peakpss )) && peakpss=$pss
    sleep 0.2
  done
  print -- "$peakrss $peakpss" > "$rssfile"
) &
spid=$!

# Stream the build live while it runs; `tail --pid` exits when the build does.
tail -n +1 -f --pid=$bpid "$raw" \
  | sed 's/\x1b\[[0-9;]*[mGKHABCDEFJST]//g' \
  | tee -a "$log"
wait $bpid; rc=$?
wait $spid
set -e
cd "$root"

# Counts come from the log, so they describe exactly what was recorded.
#
# Lean diagnostics carry a source position (`error: File.lean:12:0: …`); Lake's
# own summary lines (`error: build failed`, `error: Lean exited with code 1`) do
# not. Counting both together inflates the error count — two bad theorems
# reported 6 — so they are counted separately.
jobs=$(grep -oE 'Build completed successfully \([0-9]+ jobs\)' "$log" | grep -oE '[0-9]+' | tail -1)
diags=$(grep -cE '^error: [^ ]+\.lean:[0-9]+:[0-9]+:' "$log" || true)
errlines=$(grep -cE '^error:' "$log" || true)
lakeerrs=$(( errlines - diags ))
warns=$(grep -cE "^warning:.*declaration uses .sorry" "$log" || true)
otherwarns=$(grep -cE '^warning:' "$log" || true)
otherwarns=$(( otherwarns - warns ))

wall=$(grep -E 'Elapsed \(wall clock\)' "$metrics" | sed 's/.*: //')
user=$(grep -E '^\s*User time' "$metrics" | sed 's/.*: //')
sys=$(grep -E '^\s*System time' "$metrics" | sed 's/.*: //')
cpu=$(grep -E 'Percent of CPU' "$metrics" | sed 's/.*: //')
rsskb=$(grep -E 'Maximum resident set size' "$metrics" | sed 's/.*: //')
rssmb=$(( rsskb / 1024 ))
read -r treersskb treepsskb <<< "$(cat "$rssfile" 2>/dev/null || print '0 0')"
if (( treepsskb > 0 )); then
  treerssmb=$(( treersskb / 1024 ))
  treepssmb=$(( treepsskb / 1024 ))
  treetxt="${treepssmb} MiB"
else
  # Build finished inside one 200 ms sampling interval.
  treerssmb=0
  treepssmb=0
  treetxt="not sampled (build shorter than one 200 ms interval)"
fi

# The two `--- times ---` field names are verbatim from the logging standard, so
# one parser reads every project's logs. The build-specific counts follow.
{
  print -- "--- times ---"
  print -- "Elapsed (wall clock): $wall"
  print -- "Maximum resident set size (kbytes): $rsskb"
  print -- "--- build ---"
  print -- "finished:         $(date '+%Y-%m-%dT%H:%M:%S%:z')"
  print -- "exit status:      $rc"
  print -- "user cpu:         ${user}s"
  print -- "system cpu:       ${sys}s"
  print -- "cpu use:          $cpu"
  print -- "peak rss single:  ${rssmb} MiB (largest one process, GNU time)"
  print -- "peak pss tree:    $treetxt (process group, shared pages apportioned)"
  print -- "peak rss tree:    ${treerssmb} MiB (process group, shared pages counted per process)"
  print -- "jobs:             ${jobs:-n/a}"
  print -- "lean diagnostics: $diags"
  print -- "lake errors:      $lakeerrs"
  print -- "sorry decls:      $warns"
  print -- "other warnings:   $otherwarns"
} >> "$log"

print -- "compile: exit $rc · wall $wall · mem ${rssmb} MiB single / $treetxt tree pss / ${treerssmb} MiB tree rss · jobs ${jobs:-n/a} · diagnostics $diags · lake errors $lakeerrs · sorry $warns · other warnings $otherwarns"
print -- "compile: log $log"
exit $rc
