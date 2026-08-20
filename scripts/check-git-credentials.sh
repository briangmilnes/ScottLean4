#!/bin/sh
# Show which GitHub identity git resolves for every repository under $ROOT.
#
# Runs `git credential fill` once per origin URL and prints the resolved username
# and the *length* of the token. The token itself is never printed — only its
# character count, which is enough to confirm a credential came back. A line is
# marked FAIL when the resolved username is not the URL's owner, which is exactly
# the condition that produced the 403 on briangmilnes/ScottBibliography.
#
# Usage: check-git-credentials.sh [root]     (default /Users/scott/projects)

ROOT=${1:-/Users/scott/projects}
fails=0

printf '%-52s %-14s %-14s %s\n' URL OWNER RESOLVED TOKEN
find "$ROOT" -maxdepth 3 -name .git -type d 2>/dev/null | sort | while read -r dot; do
    dir=$dot/..
    url=$(git -C "$dir" remote get-url origin 2>/dev/null) || continue
    case $url in https://github.com/*/*) ;; *) continue ;; esac

    owner=$(printf '%s\n' "$url" | cut -d/ -f4)
    path=$(printf '%s\n' "$url" | cut -d/ -f4-)
    out=$(printf 'protocol=https\nhost=github.com\npath=%s\n\n' "$path" |
          git -C "$dir" credential fill 2>/dev/null)
    user=$(printf '%s\n' "$out" | sed -n 's/^username=//p')
    pass=$(printf '%s\n' "$out" | sed -n 's/^password=//p')

    mark=ok
    [ "$user" = "$owner" ] || mark=FAIL
    printf '%-52s %-14s %-14s %2d chars  %s\n' \
           "${url#https://github.com/}" "$owner" "${user:-<none>}" "${#pass}" "$mark"
done
