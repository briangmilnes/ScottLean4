#!/usr/bin/env bash
# sync-worktrees.sh — fast-forward every agentN worktree's branch to main.
#
# Why this exists: after the orchestrator merges the agent branches into main,
# each agentN branch still points at its own last commit. The next round's agents
# would then start from a stale tree and re-measure against code the merge
# already changed. This brings every agent branch to main.
#
# Fast-forward ONLY. If an agent branch has a commit main does not contain, the
# ff fails loudly and the branch is left alone -- that is unmerged work, and
# silently resetting it would destroy it.
#
# Multi-step logic in a script rather than inline, per CLAUDE.md: one `cd` and a
# loop cannot be allowlisted as a command prefix.

set -uo pipefail
main=/home/milnes/projects/ScottLean4

printf '%-9s %-10s %s\n' branch result head
printf '%-9s %-10s %s\n' --------- ---------- ----
for wt in "$main"-agent*; do
  [ -d "$wt" ] || continue
  agent=${wt##*-}
  if out=$(git -C "$wt" merge --ff-only main 2>&1); then
    case "$out" in
      *"Already up to date"*) res=current ;;
      *)                      res=fast-fwd ;;
    esac
  else
    res=BLOCKED
  fi
  printf '%-9s %-10s %s\n' "$agent" "$res" "$(git -C "$wt" rev-parse --short HEAD)"
  if [ "$res" = BLOCKED ]; then
    printf '  %s\n' "$out"
    blocked=1
  fi
done
exit "${blocked:-0}"
