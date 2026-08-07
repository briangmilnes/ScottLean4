#!/usr/bin/env bash
# init-worktree.sh N — create the agentN worktree at ~/projects/ScottLean4-agentN
# on branch agentN, following the layout every existing agent worktree uses.
#
# Two steps, which is why this is a script rather than an inline command:
#
#   1. git worktree add, branching agentN from main (GRASE rule 2.2: the branch
#      name matches the agent).
#   2. symlink ScottDomains/.lake/packages at the main checkout's copy. Without
#      it each worktree carries its own ~7 GiB of Mathlib and its own from-scratch
#      build; with it the tree costs 327 MiB and reuses the built packages.
#      ScottDomains/ is the lake root for this work, not the repo root.
#
# Idempotent: an existing worktree or an existing symlink is left alone.
# Verify the result with scripts/worktree-sync.sh.

set -u
root=/home/milnes/projects/ScottLean4
n=${1:?usage: init-worktree.sh N}
wt="$root-agent$n"

if [ -d "$wt" ]; then
  echo "init-worktree: $wt already exists, leaving it alone"
else
  git -C "$root" worktree add -b "agent$n" "$wt" main || exit 1
  echo "init-worktree: created $wt on branch agent$n"
fi

link="$wt/ScottDomains/.lake/packages"
target="$root/ScottDomains/.lake/packages"
if [ -e "$link" ] || [ -L "$link" ]; then
  echo "init-worktree: $link already present"
else
  mkdir -p "$wt/ScottDomains/.lake"
  ln -s "$target" "$link"
  echo "init-worktree: symlinked packages at $target"
fi
