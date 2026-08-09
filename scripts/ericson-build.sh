#!/usr/bin/env bash
# ericson-build.sh — build one of Ericson's four formalizations, sharing the
# single Mathlib build that already exists under Ericson/scott1972.
#
#   scripts/ericson-build.sh scott_models
#
# Why the symlink: all four repos pin toolchain v4.30.0 AND Mathlib revision
# c5ea00351c28e24afc9f0f84379aa41082b1188f, so one `.lake/packages` (7.1 GiB,
# already built under scott1972) serves all four. Without sharing, each project
# would fetch its own copy and the disk — 19 GiB free at 96% full — does not hold
# four. Lake reads `.lake/packages` and writes only `.lake/build`, so sharing is
# safe; scott1972's own build output is 11 MiB for 4,478 lines, which is the real
# per-project cost.
#
# Writes Ericson/logs/ericson-build-<repo>-YYYYMMDD-HHMMSS.<role>.log per the
# project LoggingStandard, with a --- times --- footer from /usr/bin/time -v.
# Reports jobs, errors, warnings and `sorry` count, and never appends.
#
# `cd` is unavoidable here — lake resolves its project root from the working
# directory and `--dir` does not switch toolchains — which is exactly why this
# is a script rather than an inline command.

set -uo pipefail
repo="${1:?usage: scripts/ericson-build.sh <scott1972|scott1980|scott1982|scott_models>}"
root=/home/milnes/projects/ScottLean4
eric="$root/Ericson"
proj="$eric/$repo"
shared="$eric/scott1972/.lake/packages"

[ -d "$proj" ] || { echo "no such repo: $proj" >&2; exit 2; }

case "$PWD" in *-agent[0-9]*) role="${PWD##*-}" ;; *) role=orchestrator ;; esac
stamp=$(date +%Y%m%d-%H%M%S)
mkdir -p "$eric/logs"
log="$eric/logs/ericson-build-$repo-$stamp.$role.log"

# Share the one Mathlib build. Never clobber a real directory.
if [ "$repo" != scott1972 ]; then
  mkdir -p "$proj/.lake"
  if [ -e "$proj/.lake/packages" ] && [ ! -L "$proj/.lake/packages" ]; then
    echo "refusing: $proj/.lake/packages exists and is not a symlink" >&2
    exit 3
  fi
  ln -sfn "$shared" "$proj/.lake/packages"
fi

before=$(df -k /home/milnes/projects | tail -1 | awk '{print $4}')

{
  echo "# ericson-build $repo"
  echo "# toolchain: $(tr -d '\n' < "$proj/lean-toolchain")"
  echo "# head:      $(git -C "$proj" log --oneline -1)"
  echo "# packages:  $(readlink -f "$proj/.lake/packages")"
  echo
} > "$log"

cd "$proj" || exit 4
/usr/bin/time -v lake build 2>&1 \
  | sed 's/\x1b\[[0-9;]*[mGKHABCDEFJST]//g' >> "$log"
status=${PIPESTATUS[0]}

after=$(df -k /home/milnes/projects | tail -1 | awk '{print $4}')

errors=$(grep -c '^error' "$log")
warns=$(grep -c '^warning' "$log")
jobs=$(grep -oE '\[[0-9]+/[0-9]+\]' "$log" | tail -1 | tr -d '[]')
sorries=$(grep -c "declaration uses 'sorry'" "$log")
srcsorry=$(grep -rn '\bsorry\b' "$proj" --include='*.lean' \
             --exclude-dir=.lake 2>/dev/null | wc -l)
build=$(du -sh "$proj/.lake/build" 2>/dev/null | cut -f1)

{
  echo
  echo "--- times ---"
  echo "exit status:      $status"
  echo "lake jobs:        ${jobs:-unknown}"
  echo "errors:           $errors"
  echo "warnings:         $warns"
  echo "sorry warnings:   $sorries"
  echo "sorry in source:  $srcsorry"
  echo "build dir:        ${build:-none}"
  echo "disk consumed:    $(( (before - after) / 1024 )) MiB"
} >> "$log"

printf '%s: exit %s · jobs %s · errors %s · warnings %s · sorry %s (source %s) · build %s · disk %s MiB\n' \
  "$repo" "$status" "${jobs:-?}" "$errors" "$warns" "$sorries" "$srcsorry" \
  "${build:-none}" "$(( (before - after) / 1024 ))"
echo "log $log"
exit "$status"
