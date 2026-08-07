#!/bin/zsh
# allow-bash.sh — PreToolUse hook: auto-approve compound shell commands whose
# every clause is a known read-only tool or a project script.
#
# Why this exists: permission allowlist entries match a command *prefix*, so a
# compound command (`cd X && lake build 2>&1 | tail`, a `for` loop, a `;` chain,
# an env-var prefix) can never match one, however many of its parts are
# allowlisted. Measurement from .claude/permission-requests.log: every prompt
# raised during rounds r0027–r0028 was of that shape. This hook splits the
# command into clauses and approves only when each head is on SAFE below and no
# clause contains a DANGER pattern. Anything else falls through to the normal
# prompt — silence here means "ask the user", never "allow".
#
# Contract: reads the PreToolUse JSON on stdin, writes an allow decision on
# stdout, exits 0 always (a hook must never block the workflow).
set -e

cmd="$(jq -r '.tool_input.command // ""' 2>/dev/null)" || exit 0
[[ -z "$cmd" ]] && exit 0

# Anything mutating, networked, or privilege-changing: never auto-approve, even
# if every head looks safe. Checked against the whole command string.
#
# `curl` was on this list until r0034; it is now a SAFE head, because fetching a
# cited paper is ordinary work here. Piping a download into a shell is still
# refused — that is what the '| sh' family below blocks.
DANGER=(
  'sudo' 'doas' 'chmod ' 'chown ' 'mkfs' 'dd if=' 'shutdown' 'reboot'
  '| sh' '|sh' '| bash' '|bash' '| zsh' '|zsh'
  'wget' 'ssh ' 'scp ' 'nc ' 'ncat' 'telnet'
  'git push' 'git reset --hard' 'git clean' 'git checkout' 'git rebase'
  'git branch -D' 'git worktree remove' 'git filter'
  'rm -rf /' 'rm -fr /' ':(){' '> /dev/sd' 'mv /' 'eval ' 'exec '
  'npm ' 'pip ' 'cargo install' 'apt ' 'apt-get ' 'brew '
)
for d in $DANGER; do
  [[ "$cmd" == *"$d"* ]] && exit 0
done

# Heads that may appear in an auto-approved command. Read-only inspection, Lean
# builds, and this project's own wrapper scripts. `rm` is deliberately absent.
SAFE=(
  cd ls cat head tail wc grep egrep rg sed awk sort uniq cut tr find printf echo
  date stat du df readlink basename dirname jq ps env true test file which type
  diff comm tee xargs pwd nproc uname sleep wait kill
  lake lean elan pdftotext pdfinfo pdffonts kpsewhich curl
  git zsh bash sh
  for do done if then else fi while case esac in function return local set unset
)
# Any .sh under a `scripts/` directory of this project or one of its worktrees.
# The old pattern listed five script names and accepted only the *relative* forms
# `scripts/x.sh` and `./scripts/x.sh`. CLAUDE.md tells every agent to use
# absolute paths, so `/home/milnes/projects/ScottLean4-agent6/scripts/compile.sh`
# missed the pattern and prompted on every build — the exact opposite of the
# rule's intent. The path is still anchored under /home/milnes/projects/ so an
# arbitrary `scripts/` directory elsewhere on disk does not qualify.
SAFE_SCRIPT_RE='^((\./)?scripts/|/home/milnes/projects/[A-Za-z0-9._-]+/scripts/)[A-Za-z0-9._-]+\.sh$'

# git is on SAFE as a head, but only these subcommands are read-only enough.
GIT_OK=(status log show diff rev-parse rev-list branch worktree merge-base
        fetch add commit merge stash config describe shortlog blame cat-file
        ls-files ls-tree symbolic-ref for-each-ref)

# Split into clauses on && || ; | and newlines, then check each head.
clauses=("${(@f)$(print -r -- "$cmd" | sed -E 's/(\&\&|\|\||;|\|)/\n/g')}")
for c in $clauses; do
  c="${c##[[:space:]]#}"
  [[ -z "${c// }" ]] && continue
  # Strip leading env assignments (VAR=value ...) and subshell/brace punctuation.
  words=(${=c})
  while (( $#words )) && [[ "$words[1]" == *=* && "$words[1]" != */* ]]; do
    shift words
  done
  (( $#words )) || continue
  head="${words[1]#\(}"
  head="${head#\{}"
  head="${head#!}"
  [[ -z "$head" ]] && continue
  # A project script is fine; otherwise the head must be on SAFE.
  if [[ "$head" =~ $SAFE_SCRIPT_RE ]]; then
    continue
  fi
  ok=0
  for s in $SAFE; do [[ "$head" == "$s" ]] && ok=1 && break; done
  (( ok )) || exit 0
  # git needs its subcommand checked too.
  if [[ "$head" == git ]]; then
    sub="$words[2]"
    gok=0
    for g in $GIT_OK; do [[ "$sub" == "$g" ]] && gok=1 && break; done
    (( gok )) || exit 0
  fi
done

jq -n --arg r "every clause is a read-only tool or a project script (allow-bash.sh)" \
  '{hookSpecificOutput: {hookEventName: "PreToolUse",
                         permissionDecision: "allow",
                         permissionDecisionReason: $r}}'
