#!/bin/zsh
# a4-run-delete.sh — build the probe (package imports + scripts/a4-delete.lean)
# and elaborate it against the built oleans.
#
# Usage: scripts/a4-run-delete.sh [out.lean]
#
# Zero errors means the kernel accepted each weakened statement, i.e. the deleted
# hypothesis was unnecessary. An error naming an unsynthesizable instance means
# the hypothesis is load-bearing and must stay.
set -e
here="${0:A:h}"
mkdir -p "$here/../ScottDomains/.lake/a4-probes"
out="${1:-$here/../ScottDomains/.lake/a4-probes/a4-delete-probe.lean}"
"$here/a4-mkprobe.sh" "$out" >/dev/null
cat "$here/a4-delete.lean" >> "$out"
"$here/a4-lint.sh" "$out"
