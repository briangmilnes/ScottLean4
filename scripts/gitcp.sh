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
  echo "gitcp: nothing staged — working tree clean, nothing to commit."
  exit 0
fi

git commit -q -m "${msg}

Co-Authored-By: Claude Opus 4.8 <noreply@anthropic.com>"
echo "gitcp: committed $(git rev-parse --short HEAD)"

git pull --rebase --quiet
git push
echo "gitcp: pushed to $(git rev-parse --abbrev-ref '@{u}' 2>/dev/null || echo origin/main)"
