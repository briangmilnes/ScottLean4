#!/bin/sh
# Send one file as an attachment through Mail.app, by AppleScript.
#
# Exists because this machine has no other mail path: no email MCP connector is
# registered, and stock postfix has no relay, so /usr/bin/mail would queue to
# nowhere. Mail.app, once it holds a configured account, is the only transport
# that can actually deliver, and AppleScript is the only way to drive it.
#
# Usage: email-file.sh <to-address> <subject> <file> [body]
#
# The message is created visible, so it appears on screen as it is sent rather
# than going out silently. This script never touches credentials: Mail.app holds
# the account, and if no account is configured the send fails loudly here.

set -e

to=$1; subject=$2; file=$3
body=${4:-"Attached: $(basename "$file")"}

[ -n "$to" ] && [ -n "$subject" ] && [ -f "$file" ] || {
    echo "usage: email-file.sh <to-address> <subject> <file> [body]" >&2
    exit 2
}

accounts=$(osascript -e 'tell application "Mail" to count of accounts' 2>/dev/null || echo 0)
if [ "$accounts" -lt 1 ]; then
    echo "Mail.app has no account configured -- nothing can be sent." >&2
    echo "Open Mail, add the account, then re-run this script." >&2
    exit 1
fi

osascript \
  -e 'on run {addr, subj, path, bod}' \
  -e '  tell application "Mail"' \
  -e '    set msg to make new outgoing message with properties {subject:subj, content:bod & return & return, visible:true}' \
  -e '    tell msg' \
  -e '      make new to recipient at end of to recipients with properties {address:addr}' \
  -e '      tell content to make new attachment with properties {file name:(POSIX file path) as alias} at after the last paragraph' \
  -e '    end tell' \
  -e '    delay 1' \
  -e '    send msg' \
  -e '  end tell' \
  -e '  return "sent"' \
  -e 'end run' \
  -- "$to" "$subject" "$file" "$body"
