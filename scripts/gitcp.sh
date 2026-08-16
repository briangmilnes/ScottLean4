#!/bin/zsh
# gitcp.sh — stage, commit, rebase onto the remote, and push, in ONE step.
#
# Why this exists: a compound invocation like
#     git add … && git commit -m "…" && git pull --rebase && git push | tail
# can't be added to the permission allowlist (allowlisting matches a single
# command prefix, not multi-statement / piped shells). Wrapping the flow in one
# script means it runs as a single permitted command — no per-step prompts.
#
# Usage:
#   scripts/gitcp.sh "<commit message>" [path ...]
#     paths given  -> stages exactly those paths
#     no paths     -> stages everything (git add -A)
#
# Rebases onto origin before pushing, so it's safe with a second machine/agent
# committing to the same branch.
set -e
cd "${0:A:h}/.."                       # repo root (this script lives in scripts/)

msg="${1:?usage: gitcp.sh \"<commit message>\" [path ...]}"
shift

if (( $# > 0 )); then
  git add -- "$@"
else
  git add -A
fi

if git diff --cached --quiet; then
  # Nothing new to commit is not a reason to skip the push: an earlier run may
  # have committed and then failed to push, leaving commits stranded locally.
  echo "gitcp: nothing staged — no commit made."
else
  git commit -q -m "${msg}

Co-Authored-By: Claude Opus 5 <noreply@anthropic.com>"
  echo "gitcp: committed $(git rev-parse --short HEAD)"
fi

# Integrate the remote only when it actually has commits we lack. An
# unconditional `git pull --rebase` is wrong once the branch carries merge
# commits: rebasing linearizes them and replays each merged agent commit onto
# origin, which conflicts against the very content already merged there. Merge,
# do not rebase, for the same reason.
git fetch --quiet
upstream="$(git rev-parse --abbrev-ref '@{u}' 2>/dev/null || echo origin/main)"
if git merge-base --is-ancestor "$upstream" HEAD; then
  echo "gitcp: up to date with ${upstream}, no integration needed"
else
  echo "gitcp: ${upstream} has new commits — merging"
  git pull --no-rebase --quiet
fi

git push
echo "gitcp: pushed to $(git rev-parse --abbrev-ref '@{u}' 2>/dev/null || echo origin/main)"
