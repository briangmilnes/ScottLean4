#!/usr/bin/env bash
# collect-orchestrator-logs.sh — move build logs the orchestrator produced inside
# agent worktrees back into the main checkout's ScottDomains/logs/.
#
# Why this exists: the orchestrator verifies each agent's report by running that
# worktree's compile.sh before merging. The wrapper detects its role from the
# checkout path, so the log lands in the *agent's* worktree as
# `compile-<stamp>.agentN.log` and is untracked there — which makes
# worktree-sync.sh skip that worktree as dirty on the next round. Measured in
# r0037: four of six worktrees skipped for exactly this reason, twice.
#
# The logs are telemetry and are committed (LoggingStandard), so they are moved
# rather than deleted. The `.agentN` role slot in the filename stays accurate:
# the run did happen in that worktree.
#
# Idempotent: with no such logs it moves nothing and says so. Run before
# worktree-sync.sh at the end of a round.
set -u
root=/home/milnes/projects/ScottLean4
dest="$root/ScottDomains/logs"

moved=0
for wt in "$root"-agent*; do
  [ -d "$wt/ScottDomains/logs" ] || continue
  n=$(basename "$wt"); n=${n##*-}
  # Only untracked logs — anything git knows about belongs to that branch.
  while IFS= read -r f; do
    [ -n "$f" ] || continue
    mv "$wt/$f" "$dest/" && echo "collected $n: $(basename "$f")"
    moved=$((moved + 1))
  done < <(git -C "$wt" ls-files --others --exclude-standard -- 'ScottDomains/logs/*.log')
done
echo "collect-orchestrator-logs: $moved file(s) moved to $dest"
