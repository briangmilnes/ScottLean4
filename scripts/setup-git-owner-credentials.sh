#!/bin/sh
# Bind a GitHub identity per repository owner AND per exact repository URL.
#
# Problem: git used the osxkeychain helper, which holds one token per host, so
# every github.com push authenticated as whichever account the keychain held —
# DanaSScott — and pushes to briangmilnes repositories returned 403. Switching
# with `gh auth switch` makes the identity global mutable state and breaks the
# other owner instead.
#
# Fix: git matches `credential.<url>.*` config against the *path* of the request
# (the path is dropped only afterwards, when the request is handed to a helper),
# so the URL selects the helper. Two levels are written:
#
#   1. owner prefix  https://github.com/<owner>            — catches every repo of
#                                                            that owner, including
#                                                            ones not yet cloned
#   2. exact URL     https://github.com/<owner>/<repo>.git — one entry per clone
#                                                            found under $ROOT
#
# The exact-URL entries are redundant with the prefix entries today; they exist so
# that a repository whose identity must differ from its owner's can be overridden
# in one place, and so `git config --global --get-regexp '^credential\.'` reads as
# an explicit inventory of what pushes as whom.
#
# No token is read or written by this script; each entry names a gh account and
# the helper fetches that account's token at push time.
#
# Global config is read before repository-local config, and git stops at the first
# helper returning both a username and a password, so these entries take
# precedence over any repo-local `credential.helper = osxkeychain`.
#
# Idempotent: --replace-all overwrites rather than appends.

set -e

HELPER=/Users/scott/projects/ScottLean4/scripts/git-credential-gh-user.sh
ROOT=${1:-/Users/scott/projects}

bind() {
    key="credential.$1"
    account=$2
    git config --global --replace-all "$key.username" "$account"
    git config --global --replace-all "$key.helper"   "!$HELPER $account"
    printf '  %-56s -> %s\n' "$1" "$account"
}

echo "owner prefixes:"
for account in briangmilnes DanaSScott; do
    bind "https://github.com/$account" "$account"
done

echo
echo "exact repository URLs found under $ROOT:"
find "$ROOT" -maxdepth 3 -name .git -type d 2>/dev/null | while read -r dot; do
    url=$(git -C "$dot/.." remote get-url origin 2>/dev/null) || continue
    case $url in
        https://github.com/*/*) ;;
        *) continue ;;
    esac
    owner=$(printf '%s\n' "$url" | cut -d/ -f4)
    bind "$url" "$owner"
done | sort -u

echo
echo "resulting global entries:"
git config --global --get-regexp '^credential\.' | sed 's/^/  /' | sort
