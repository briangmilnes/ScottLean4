#!/bin/zsh
# save-prompts.sh — reconstruct GRASE prompt files from Claude Code's session
# recording, rather than from the assistant's context (which compaction truncates).
#
# Usage: scripts/save-prompts.sh
#
# Idempotent: re-running rewrites every file from the recording, picking up
# interactions that have happened since the last run. Safe to run at any point,
# and the right thing to run before `grase stop` or at end of day.
#
# One file per interaction: prompts/pNNNN-YYYY-MMDD-HH:MM.user-to-orchestrator.txt
# User turns verbatim; assistant prose verbatim; tool calls one per line as
# `<Tool> <first arg>` per GRASE rule 3.12. Subagent (sidechain) records are
# excluded — those are agent transcripts, not user↔assistant interaction.
set -e

# Paths are DERIVED, not hardcoded: this repo is worked from a Linux box and a
# Mac whose $HOME and user name differ. ROOT comes from the script's own
# location; Claude Code names its session directory after the project path with
# every "/" replaced by "-".
ROOT=${0:A:h}/..
OUT=$ROOT/ScottDomains/prompts
SRC=~/.claude/projects/${${ROOT:A}//\//-}
mkdir -p "$OUT"

if [[ ! -d "$SRC" ]]; then
  print -u2 -- "save-prompts: no session directory at $SRC"
  exit 1
fi

# `date -d` is GNU-only and BSD date cannot parse ISO-8601 without contortions,
# so timestamp formatting goes through python3, which both machines have.
fmt_ts() {  # $1 = ISO-8601 instant, $2 = "stamp" | "iso"
  python3 -c '
import sys, datetime
from zoneinfo import ZoneInfo
d = datetime.datetime.fromisoformat(sys.argv[1].replace("Z", "+00:00"))
d = d.astimezone(ZoneInfo("America/Los_Angeles"))
print(d.strftime("%Y-%m%d-%H:%M") if sys.argv[2] == "stamp" else d.isoformat())
' "$1" "$2"
}

# Sessions in chronological order of first record.
# Key on the earliest timestamp anywhere in the file: the first record of a
# resumed session is a summary line with no timestamp, which sorted that session
# to the front and put the day's last interaction at p0001.
files=(${(f)"$(for f in $SRC/*.jsonl; do
  printf '%s\t%s\n' "$(jq -r 'select(.timestamp) | .timestamp' $f 2>/dev/null | sort | head -1)" "$f"
done | sort | cut -f2)"})

events=$(mktemp)
GEN=$(mktemp -d)
trap 'rm -f $events; rm -rf $GEN' EXIT

for f in $files; do
  jq -c --arg sid "$(basename $f .jsonl)" '
    select((.isSidechain // false) == false) |
    . as $r |
    if .type == "user" and (.message.content | type == "string")
       and (.message.content | startswith("<") | not) then
      {ts: $r.timestamp, sid: $sid, kind: "USER", body: .message.content}
    elif .type == "assistant" then
      (.message.content[]? |
        if .type == "text" and (.text | length > 0) then
          {ts: $r.timestamp, sid: $sid, kind: "TEXT", body: .text}
        elif .type == "tool_use" then
          {ts: $r.timestamp, sid: $sid, kind: "TOOL",
           body: (.name + " " +
                  ((.input.command // .input.file_path // .input.pattern //
                    .input.description // .input.skill // .input.query // "")
                   | tostring | .[0:150] | gsub("\n"; " ")))}
        else empty end)
    else empty end' $f 2>/dev/null >> $events || true
done

total=$(jq -s '[.[] | select(.kind=="USER")] | length' $events)
print -- "user turns found: $total"

# Segment into interactions and write one file each.
jq -s '
  [ range(0; length) as $i | {i: $i, e: .[$i]} ] as $idx |
  [ $idx[] | select(.e.kind == "USER") | .i ] as $starts |
  [ range(0; ($starts|length)) as $k |
    { start: $starts[$k],
      end: (if $k + 1 < ($starts|length) then $starts[$k+1] else ($idx|length) end),
      events: [ $idx[ $starts[$k] : (if $k+1 < ($starts|length) then $starts[$k+1] else ($idx|length) end) ][] | .e ] } ]
' $events > $events.grouped

# Ids are assigned over the UNION of interactions on disk, not over the local
# session store alone — see the renumbering block below. Each interaction is
# first written under its generation index, and gets its `pNNNN` only once the
# union is sorted, so the frontmatter carries a placeholder until then.
n=$(jq 'length' $events.grouped)
for k in {0..$((n-1))}; do
  id="pending"
  ts=$(jq -r ".[$k].events[0].ts" $events.grouped)
  local_stamp=$(fmt_ts "$ts" stamp)
  last_ts=$(jq -r ".[$k].events[-1].ts" $events.grouped)
  close_stamp=$(fmt_ts "$last_ts" stamp)
  sid=$(jq -r ".[$k].events[0].sid" $events.grouped | cut -c1-8)
  subj=$(jq -r ".[$k].events[0].body" $events.grouped \
          | head -1 | tr 'A-Z' 'a-z' | sed -E 's/[^a-z0-9 ]//g; s/  +/ /g' \
          | cut -c1-40 | sed -E 's/ +$//; s/ /-/g')
  [[ -z "$subj" ]] && subj="interaction"
  file="$GEN/g$(printf '%04d' $k)-$local_stamp"

  {
    print -- "---"
    print -- "prompt: $id"
    print -- "type: interaction"
    print -- "opened: $local_stamp"
    print -- "closed: $close_stamp"
    print -- "subject: $subj"
    print -- "session: $sid"
    print -- "---"
    print -- "# Reconstructed from Claude Code's session recording"
    print -- "# ($SRC/$sid….jsonl),"
    print -- "# not from context: this conversation was compacted, so the assistant's"
    print -- "# own recollection covers only its tail. Timestamps are the recorded"
    print -- "# per-message times in America/Los_Angeles, second resolution."
    print -- ""
    jq -r ".[$k].events[] |
      if .kind == \"USER\" then \"## turn — user \" + .ts + \"\n\n\" + .body + \"\n\"
      elif .kind == \"TEXT\" then \"## turn — assistant \" + .ts + \"\n\n\" + .body + \"\n\"
      else \"    \" + .body end" $events.grouped \
    | python3 -c '
import sys, datetime
from zoneinfo import ZoneInfo
LA = ZoneInfo("America/Los_Angeles")
for line in sys.stdin:
    parts = line.rstrip("\n").split(" ")
    if len(parts) >= 5 and parts[0] == "##" and parts[1] == "turn" and parts[3] in ("user", "assistant"):
        d = datetime.datetime.fromisoformat(parts[4].replace("Z", "+00:00")).astimezone(LA)
        print("## turn — " + parts[3] + " " + d.isoformat())
    else:
        print(line, end="")
' 
  } > "$file"
done

# --- Carry forward interactions recorded on the *other* machine --------------
#
# This repo is worked from a Linux box and a Mac, and each holds only its own
# session recordings. Numbering per-machine therefore produced two colliding
# `p0001…` series: measured 2026-0817, 332 files carrying 84 duplicate ids, the
# Linux series (Aug 6–7, 84 files, committed) against the Mac series (Aug 1–17,
# 248 files, untracked).
#
# A prompt file whose `session:` is not one of the local recordings is FOREIGN:
# its source .jsonl is not on this machine, so it cannot be regenerated and is
# copied forward verbatim. Session id discriminates exactly — the two machines'
# session sets are disjoint by construction, where the minute-resolution stamp
# does not (9 stamps carry two interactions apiece).
local_sids=$(for f in $SRC/*.jsonl; do basename $f .jsonl | cut -c1-8; done | sort -u)

foreign=0
for p in $OUT/p*.user-to-orchestrator.txt(N); do
  sid=$(grep -m1 '^session:' $p | awk '{print $2}')
  if ! print -- "$local_sids" | grep -qx -- "$sid"; then
    stamp=$(grep -m1 '^opened:' $p | awk '{print $2}')
    cp $p "$GEN/f$(printf '%04d' $foreign)-$stamp"
    foreign=$((foreign+1))
  fi
done
print -- "regenerated here: $n   carried forward from the other machine: $foreign"

rm -f $OUT/p*.user-to-orchestrator.txt(N)

# --- Renumber chronologically over the union ---------------------------------
#
# A *stable* sort on the minute-resolution stamp: interactions sharing a minute
# keep the order they were generated in, so the ids do not permute between runs.
i=0
for entry in ${(f)"$(for g in $GEN/g*(N) $GEN/f*(N); do
      printf '%s\t%s\n' "${${g:t}#?????-}" "$g"
    done | sort -s -k1,1 | cut -f2)"}; do
  i=$((i+1))
  id=$(printf 'p%04d' $i)
  stamp=${${entry:t}#?????-}
  # Restricted to the frontmatter block, and matching any prior value: a
  # carried-forward file still holds the id the *other* machine gave it.
  sed "1,8s/^prompt: .*\$/prompt: $id/" $entry \
    > "$OUT/$id-$stamp.user-to-orchestrator.txt"
done
print -- "wrote $i files to $OUT"
