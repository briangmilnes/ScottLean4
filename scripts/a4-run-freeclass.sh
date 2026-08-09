#!/bin/zsh
# a4-run-freeclass.sh — build the probe (package imports + scripts/a4-freeclass.lean)
# and elaborate it against the built oleans.
#
# Usage: scripts/a4-run-freeclass.sh [out.lean]
#
# Zero errors from this run is the verdict: every FREE claim is a `theorem` the
# kernel accepted, and every NOT FREE claim names a counterexample that already
# type-checks in the package.
set -e
here="${0:A:h}"
mkdir -p "$here/../ScottDomains/.lake/a4-probes"
out="${1:-$here/../ScottDomains/.lake/a4-probes/a4-freeclass-probe.lean}"
"$here/a4-mkprobe.sh" "$out" >/dev/null
cat "$here/a4-freeclass.lean" >> "$out"
"$here/a4-lint.sh" "$out"
