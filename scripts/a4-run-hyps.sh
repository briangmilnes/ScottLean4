#!/bin/zsh
# a4-run-hyps.sh — build the probe (package imports + scripts/a4-hyps.lean) and
# elaborate it against the built oleans.
#
# Usage: scripts/a4-run-hyps.sh [out.lean]
#
# The probe is assembled outside ScottDomains/ScottDomains/ so the round's frozen
# counts (100 modules / 37300 lines / 1773 theorems) are untouched; only
# `lake env lean` sees it.
set -e
here="${0:A:h}"
# Default under .lake/, which is gitignored: the probe is a generated build
# input, not execution telemetry, so it does not belong in logs/.
mkdir -p "$here/../ScottDomains/.lake/a4-probes"
out="${1:-$here/../ScottDomains/.lake/a4-probes/a4-hyps-probe.lean}"
"$here/a4-mkprobe.sh" "$out" >/dev/null
cat "$here/a4-hyps.lean" >> "$out"
"$here/a4-lint.sh" "$out"
