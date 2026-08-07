#!/usr/bin/env bash
# collect-agent-plans.sh rNNNN — move this round's per-agent plan files out of the
# agent worktrees and into the main checkout's ScottDomains/plans/.
#
# GRASE rule 1.7 has the orchestrator write an agentN plan in agentN's worktree,
# but the plans of rounds r0030-r0032 all ended up on main, and that is the form
# that works: a plan committed on main reaches every worktree through the ordinary
# fast-forward, so each agent sees the whole round rather than only its own stream.
# Leaving the file in the worktree instead leaves six untracked files that block
# the next checkout.
#
# Moves, does not copy — the worktree copy is removed so the tree stays clean.
# Verify afterwards with scripts/worktree-sync.sh (dirty should read 0).

set -u
root=/home/milnes/projects/ScottLean4
round=${1:?usage: collect-agent-plans.sh rNNNN}
dest="$root/ScottDomains/plans"

moved=0
for wt in "$root"-agent*; do
  [ -d "$wt/ScottDomains/plans" ] || continue
  for f in "$wt/ScottDomains/plans/$round-plan-"*.md; do
    [ -e "$f" ] || continue
    mv "$f" "$dest/"
    echo "collected $(basename "$f")"
    moved=$((moved + 1))
  done
done
echo "collect-agent-plans: $moved file(s) moved to $dest"
