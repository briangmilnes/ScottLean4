#!/bin/sh
# git credential helper that answers as one named gh account.
#
# Why this exists: `gh` on this machine holds two GitHub accounts (briangmilnes,
# DanaSScott) and git was using the osxkeychain helper, which stores one token per
# host. Every push to a briangmilnes repository therefore authenticated as
# DanaSScott and 403'd. `gh auth git-credential` does not fix it either: it answers
# with whichever account is *active*, so it makes the identity global state.
#
# This helper takes the account name as its first argument, so the identity can be
# bound per URL in git config instead:
#
#   [credential "https://github.com/briangmilnes"]
#       helper = !/Users/scott/projects/ScottLean4/scripts/git-credential-gh-user.sh briangmilnes
#
# Git appends the operation (get/store/erase) after the arguments given in the
# config line, so $1 is the account and $2 is the operation. Only `get` is
# answered; `store` and `erase` are no-ops, because gh owns the token and git must
# not write it anywhere else.
#
# The token is written to git's stdin and never to a terminal.

account=$1
operation=$2

[ -n "$account" ] || exit 1
[ "$operation" = get ] || exit 0

token=$(gh auth token --user "$account" 2>/dev/null) || exit 0
[ -n "$token" ] || exit 0

printf 'username=%s\n' "$account"
printf 'password=%s\n' "$token"
