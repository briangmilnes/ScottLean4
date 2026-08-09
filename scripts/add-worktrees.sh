#!/usr/bin/env bash
# add-worktrees.sh — create agentN worktrees at ~/projects/ScottLean4-agentN on
# branch agentN, for each N given on the command line.
#
#   scripts/add-worktrees.sh 7 8
#
# Why this exists: `git worktree add -b agentN <path> main` plus the branch-exists
# check is multi-step, and GRASE rule 2.5 makes worktree creation an explicit
# operation rather than something delegation does implicitly. Idempotent: an N
# whose worktree already exists is reported and skipped, never recreated (rule
# 2.4 -- worktree lifetime is the user's responsibility).

set -uo pipefail
main=/home/milnes/projects/ScottLean4

for n in "$@"; do
  wt="$main-agent$n"
  if [ -d "$wt" ]; then
    printf 'agent%s: exists, skipped (%s)\n' "$n" "$wt"
    continue
  fi
  if git -C "$main" show-ref --verify --quiet "refs/heads/agent$n"; then
    git -C "$main" worktree add "$wt" "agent$n"
  else
    git -C "$main" worktree add -b "agent$n" "$wt" main
  fi
done

git -C "$main" worktree list
