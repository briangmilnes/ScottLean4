#!/usr/bin/env bash
# a5-r46-probe.sh — r0046 / agent5. Elaborate one probe `.lean` file against the
# built package, as ONE allowlisted command.
#
#   scripts/a5-r46-probe.sh <path-to-probe.lean>
#
# Why this exists: deciding a necessity claim ("hypothesis H is indispensable")
# means deleting H and asking the kernel to re-accept the proof. Deciding an
# absence claim ("Mathlib has no X") means asking the elaborator to resolve X.
# Both are elaborations of a file that must NOT be inside `ScottDomains/`, or it
# would enter `lake build` and change the package's job count. This runs such a
# file. Copied in shape from `scripts/a1-probe.sh` (r0044/agent1), rewritten for
# bash because this worktree's zsh is not guaranteed.
#
# Exit status is the elaborator's: 0 = every declaration in the probe was
# accepted, nonzero = at least one was rejected. For a deletion probe those two
# outcomes are the two verdicts, so the status IS the measurement.
set -u
root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
probe="$1"
[[ -f "$probe" ]] || { echo "a5-r46-probe.sh: no such file: $probe" >&2; exit 2; }
cd "$root/ScottDomains" || exit 2
lake env lean "$probe"
echo "--- a5-r46-probe.sh: elaborator exit status $? ---"
