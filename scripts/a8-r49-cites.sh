#!/usr/bin/env bash
# a8-r49-cites.sh — resolve every backticked declaration name cited in the
# package's prose against the elaborated environment, in agent8's worktree.
#
# This is scripts/a7-sweep.sh (r0044, agent7) retargeted: a7's copy hard-codes
# ScottLean4-agent7 and that session's scratchpad. The scanner (a7-cite-scan.py),
# the resolver (a7-resolve.py) and the stoplist (a7-stoplist.txt) are reused
# unchanged.
#
# Why r0049 runs it again: `Colimit.lean:59` cites `etaChain_not_wellDefined`,
# which resolves nowhere — a THIRD sighting across r0044, r0047 and r0049's plan.
# A citation that resolved when written and does not now is exactly the staleness
# mode r0046 measured (7 of 8 false proof-claims were true when written), and it
# is decidable by one environment dump plus one lexical pass.
#
# Run scripts/a8-r49-env.sh first (it needs a completed `lake build`).
#
# Work: O(|corpus| + |citations| * |name components|); span: one Python pass.
#
# Usage: scripts/a8-r49-cites.sh [unresolved-out] [env-names.tsv]
#
# Output (scratch, not project artifacts):
#   <dir of unresolved-out>/a8-citations.tsv  every scanned citation
#   <unresolved-out>                          path, line, kind, name, tier, nearest

set -uo pipefail

wt=/home/milnes/projects/ScottLean4-agent8
pkg="$wt/ScottDomains"
scratch=/tmp/claude-1000/-home-milnes-projects-ScottLean4/98e1d10d-3eb9-440a-82f5-e930a0a93589/scratchpad
unres="${1:-$scratch/a8-unresolved.tsv}"
env_tsv="${2:-$scratch/env-names.tsv}"
cites="$(dirname "$unres")/a8-citations.tsv"

if [ ! -s "$env_tsv" ]; then
  echo "a8-r49-cites: $env_tsv missing — run scripts/a8-r49-env.sh first"
  exit 1
fi

list="$(dirname "$unres")/a8-files.txt"
: > "$list"
find "$pkg/ScottDomains" -type f -name '*.lean' >> "$list"

tr '\n' '\0' < "$list" \
  | xargs -0 python3 "$wt/scripts/a7-cite-scan.py" > "$cites"

echo "a8-r49-cites: scanned $(cut -f1 "$cites" | sort -u | wc -l) files, $(wc -l < "$cites") citations"

python3 "$wt/scripts/a7-resolve.py" \
  "$env_tsv" "$cites" "$wt/scripts/a7-stoplist.txt" "$unres"
