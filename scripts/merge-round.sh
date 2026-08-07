#!/usr/bin/env bash
# merge-round.sh — merge every agent branch into main, in order, stopping at the
# first conflict so a human resolves it rather than a script guessing.
#
# One round produces up to six branches that must land together before the
# composition check can run: `lake build` never imports two unrelated modules
# into one environment, so a cross-agent name clash is invisible until every
# module sits in the same checkout (r0028 lost a round to exactly this, at 971
# green jobs). Merging one branch at a time by hand costs one permission prompt
# and one context round-trip each; this does the sequence and prints a per-branch
# result line.
#
# Each merge is --no-ff so the branch structure of the round stays legible in the
# history, and --no-edit so no editor opens.
#
# On conflict: the script stops with the branch named and leaves the working tree
# mid-merge for inspection. It never runs `git merge --abort` — discarding a
# partial merge is a decision, not a default.

set -u
root=/home/milnes/projects/ScottLean4

for n in 1 2 3 4 5 6; do
  br="agent$n"
  if ! git -C "$root" rev-parse --verify --quiet "$br" >/dev/null; then
    echo "$br: no such branch, skipped"
    continue
  fi
  if git -C "$root" merge-base --is-ancestor "$br" HEAD; then
    echo "$br: already merged, nothing to do"
    continue
  fi
  ahead=$(git -C "$root" rev-list --count "HEAD..$br")
  if git -C "$root" merge --no-ff --no-edit "$br" >/dev/null 2>&1; then
    echo "$br: merged ($ahead commit(s))"
  else
    echo "$br: CONFLICT after $ahead commit(s) — stopping, tree left mid-merge"
    git -C "$root" diff --name-only --diff-filter=U
    exit 1
  fi
done
echo "merge-round: all branches merged; now run the composition check"
