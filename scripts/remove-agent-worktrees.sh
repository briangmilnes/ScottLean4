#!/bin/zsh
# remove-agent-worktrees.sh — remove agent worktrees 2..8, keeping agent1.
#
# DESTRUCTIVE. Run scripts/salvage-agent-worktrees.sh first: three of these
# worktrees hold working-tree state that is committed nowhere, and
# `git worktree remove --force` deletes it without asking.
#
# --force is required because agent3, agent5 and agent8 are dirty; git refuses
# to remove a dirty worktree without it. Every branch here is already fully
# merged into main (`git branch --merged main` lists all eight), so no commit is
# lost by removing the directory.
#
# The **branches are left in place**. Removing a worktree and deleting its
# branch are separate acts; the branch is a few bytes of ref and keeps the
# per-agent history addressable. GRASE rule 2.4 makes branch lifetime the
# user's call.
#
# Usage: scripts/remove-agent-worktrees.sh
set -e

root="${0:A:h}/.."
cd "$root"
root="$PWD"

for n in 2 3 4 5 6 7 8; do
  wt="$HOME/projects/ScottLean4-agent$n"
  if [[ -d "$wt" ]]; then
    print -- "removing $wt"
    git -C "$root" worktree remove --force "$wt"
  else
    print -- "absent, skipping: $wt"
  fi
done

git -C "$root" worktree prune

print -- "=== remaining worktrees ==="
git -C "$root" worktree list
print -- "=== branches (all retained) ==="
git -C "$root" branch
