#!/bin/zsh
# worktree-status.sh — report what would be lost if an agent worktree were removed.
#
# Why this exists: `git worktree remove` refuses a dirty worktree but `--force`
# does not, and untracked files are invisible in `git log`. Before removing a
# worktree the two questions are (a) does its branch hold commits not in main,
# and (b) does the working tree hold modified or untracked files that exist
# nowhere else. This answers both for every worktree in one pass, so the
# decision is made from data rather than from the assumption that a merged
# branch means an empty directory.
#
# Read-only: runs no destructive git command.
#
# Usage: scripts/worktree-status.sh
set -e

root="${0:A:h}/.."
cd "$root"
root="$PWD"

git -C "$root" worktree list --porcelain | awk '/^worktree /{print $2}' | while read -r wt; do
  [[ "$wt" == "$root" ]] && continue
  branch=$(git -C "$wt" rev-parse --abbrev-ref HEAD 2>/dev/null || echo '?')
  ahead=$(git -C "$root" rev-list --count "main..$branch" 2>/dev/null || echo '?')
  modified=$(git -C "$wt" status --porcelain --untracked-files=no 2>/dev/null | wc -l)
  untracked=$(git -C "$wt" status --porcelain --untracked-files=all 2>/dev/null | grep -c '^??' || true)
  size=$(du -sh "$wt" 2>/dev/null | cut -f1)
  print -- "$branch  path=$wt"
  print -- "    commits ahead of main: $ahead"
  print -- "    modified tracked files: $modified"
  print -- "    untracked files:        $untracked"
  print -- "    disk:                   $size"
done
