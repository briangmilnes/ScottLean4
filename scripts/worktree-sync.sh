#!/usr/bin/env bash
# worktree-sync.sh — report, for every agentN worktree, whether it is safe to
# launch a new round in it.
#
# Resume step 5 of the session-restart plan says to *verify* worktree sync
# rather than assert it: three agents across two rounds found their worktree
# behind while the plan claimed otherwise. This measures four things per tree:
#
#   merged   — is the branch tip an ancestor of main? (nothing unmerged is lost)
#   behind   — how many commits main is ahead of the branch tip
#   dirty    — count of modified/untracked paths in the worktree
#   packages — is ScottDomains/.lake/packages a symlink into the main checkout
#              (327 MiB instead of ~7 GiB), per the plan's worktree convention.
#              ScottDomains/ is the lake root for this work, not the repo root.
#
# With --ff, each worktree that is clean and whose tip is an ancestor of main is
# fast-forwarded to main before the row is printed, so the reported tip is the
# post-sync one. A worktree that is dirty or holds unmerged commits is left
# untouched and its row says why — --ff never discards work.
#
# Exit status is 0 always; this is a report, not an acceptance check.

set -u
root=/home/milnes/projects/ScottLean4
main_tip=$(git -C "$root" rev-parse main)
ff=no
[ "${1:-}" = "--ff" ] && ff=yes

printf '%-8s %-10s %-8s %-7s %-6s %-9s %s\n' agent tip merged behind dirty packages synced
for wt in "$root"-agent*; do
  [ -d "$wt" ] || continue
  n=${wt##*-agent}

  synced=-
  if [ "$ff" = yes ]; then
    if [ -n "$(git -C "$wt" status --porcelain)" ]; then
      synced=skip-dirty
    elif ! git -C "$wt" merge-base --is-ancestor HEAD "$main_tip"; then
      synced=skip-unmerged
    elif [ "$(git -C "$wt" rev-parse HEAD)" = "$main_tip" ]; then
      synced=already
    elif git -C "$wt" merge --ff-only main >/dev/null 2>&1; then
      synced=ff
    else
      synced=FAILED
    fi
  fi

  tip=$(git -C "$wt" rev-parse --short HEAD)
  if git -C "$wt" merge-base --is-ancestor HEAD "$main_tip"; then
    merged=yes
  else
    merged=NO
  fi
  behind=$(git -C "$wt" rev-list --count "HEAD..$main_tip")
  dirty=$(git -C "$wt" status --porcelain | wc -l)
  if [ -L "$wt/ScottDomains/.lake/packages" ]; then
    packages=symlink
  elif [ -d "$wt/ScottDomains/.lake/packages" ]; then
    packages=REAL-DIR
  else
    packages=absent
  fi

  printf '%-8s %-10s %-8s %-7s %-6s %-9s %s\n' \
    "agent$n" "$tip" "$merged" "$behind" "$dirty" "$packages" "$synced"
done
