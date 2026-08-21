#!/bin/zsh
# salvage-agent-worktrees.sh — copy out the files that exist only inside an
# agent worktree, before that worktree is removed.
#
# Why this exists: every agent branch is fully merged into main, so `git log`
# shows nothing at risk — but three worktrees carry working-tree state that was
# never committed and would be destroyed with the directory:
#
#   agent3  4 untracked build logs from 2026-08-09 (round r47)
#   agent5  1 modified tracked file, ScottDomains/analyses/a5-r47-conditional.txt
#   agent8  1 untracked scratch module, scripts/a8-r49-decide.lean
#
# The destination is outside the repository, so salvaging does not add untracked
# files to a checkout that is about to be reviewed. A __pycache__/*.pyc in
# agent8 is deliberately not salvaged: it is a regenerable build artifact.
#
# Read-only with respect to the worktrees: copies out, deletes nothing.
#
# Usage: scripts/salvage-agent-worktrees.sh
set -e

dest="$HOME/projects/ScottLean4-agent-salvage"
mkdir -p "$dest/agent3" "$dest/agent5" "$dest/agent8"

for f in \
  ScottDomains/logs/a3-r47-qvac-20260809-121840.agent3.log \
  ScottDomains/logs/a3-r47-qvac-20260809-122143.agent3.log \
  ScottDomains/logs/a3-r47-qvac-20260809-122355.agent3.log \
  ScottDomains/logs/compile-20260809-121420.agent3.log
do
  cp "$HOME/projects/ScottLean4-agent3/$f" "$dest/agent3/"
done

cp "$HOME/projects/ScottLean4-agent5/ScottDomains/analyses/a5-r47-conditional.txt" "$dest/agent5/"
cp "$HOME/projects/ScottLean4-agent8/scripts/a8-r49-decide.lean" "$dest/agent8/"

print -- "=== salvaged to $dest ==="
find "$dest" -type f -printf '%10s  %p\n' | sort -k2
