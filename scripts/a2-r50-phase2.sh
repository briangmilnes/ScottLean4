#!/bin/zsh
# a2-r50-phase2.sh — drive the r0050 phase-2 rename to a fixed point.
#
# Why this exists: deleting the 140 phase-1 `alias` statements makes the
# elaborator report every stale reference site, but it reports them one layer of
# the import DAG at a time — a module that fails to build hides the sites in the
# modules that import it. Reaching zero therefore takes as many build/fix cycles
# as the DAG is deep below the deleted aliases. This loop runs those cycles.
#
# Each cycle: build (scripts/compile.sh, which writes the GRASE log), then hand
# that log to a2-r50-fixsites.py, which repoints exactly the identifiers the
# compiler named, at exactly the offsets it named. No search decides anything.
#
# The loop stops when the build succeeds, when a cycle fixes no site (which means
# the remaining errors are not stale references and need a human), or after
# MAXCYCLES.
#
# Usage: a2-r50-phase2.sh [max-cycles]   (default 20)
set -u
root="${0:A:h}/.."
max="${1:-20}"

for i in $(seq 1 $max); do
  print -- "=== cycle $i: build ==="
  out="$($root/scripts/compile.sh -r r0050 2>&1)"
  rc=$?
  log="${out##*compile: log }"
  print -- "${out##*compile: exit}" | head -1
  if (( rc == 0 )); then
    print -- "=== build succeeded on cycle $i ==="
    exit 0
  fi
  print -- "=== cycle $i: fix sites named in $log ==="
  fix="$(python3 $root/scripts/a2-r50-fixsites.py "$log" 2>&1)"
  print -- "$fix"
  n="${$(print -- "$fix" | grep -E '^total sites fixed:')##*: }"
  if [[ "${n:-0}" == "0" ]]; then
    print -- "=== cycle $i fixed no site; stopping for inspection ==="
    exit 1
  fi
done
print -- "=== reached max cycles ($max) without a clean build ==="
exit 1
