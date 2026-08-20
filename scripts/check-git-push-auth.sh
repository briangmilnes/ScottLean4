#!/bin/sh
# End-to-end authentication check: `git push --dry-run` against every clone.
#
# `git credential fill` proves which identity git *resolves*; only a real request
# to git-receive-pack proves GitHub *accepts* it. --dry-run negotiates and
# authenticates but transfers nothing, so this is safe to run at any time.
#
# Usage: check-git-push-auth.sh [root]     (default /Users/scott/projects)

ROOT=${1:-/Users/scott/projects}

find "$ROOT" -maxdepth 3 -name .git -type d 2>/dev/null | sort | while read -r dot; do
    dir=$dot/..
    url=$(git -C "$dir" remote get-url origin 2>/dev/null) || continue
    case $url in https://github.com/*/*) ;; *) continue ;; esac

    out=$(git -C "$dir" push --dry-run 2>&1)
    case $out in
        *403*|*denied*|*fatal*) status="DENIED  — $(printf '%s' "$out" | sed -n 's/.*remote: //p' | head -1)" ;;
        *)                      status="ok      — $(printf '%s' "$out" | head -1)" ;;
    esac
    printf '%-44s %s\n' "${url#https://github.com/}" "$status"
done
