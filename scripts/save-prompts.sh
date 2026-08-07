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

SRC=~/.claude/projects/-home-milnes-projects-ScottLean4
OUT=/home/milnes/projects/ScottLean4/ScottDomains/prompts
mkdir -p "$OUT"

# Sessions in chronological order of first record.
# Key on the earliest timestamp anywhere in the file: the first record of a
# resumed session is a summary line with no timestamp, which sorted that session
# to the front and put the day's last interaction at p0001.
files=(${(f)"$(for f in $SRC/*.jsonl; do
  printf '%s\t%s\n' "$(jq -r 'select(.timestamp) | .timestamp' $f 2>/dev/null | sort | head -1)" "$f"
done | sort | cut -f2)"})

events=$(mktemp); trap 'rm -f $events' EXIT

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

n=$(jq 'length' $events.grouped)
for k in {0..$((n-1))}; do
  id=$(printf "p%04d" $((k+1)))
  ts=$(jq -r ".[$k].events[0].ts" $events.grouped)
  local_stamp=$(TZ=America/Los_Angeles date -d "$ts" '+%Y-%m%d-%H:%M')
  iso_open=$(TZ=America/Los_Angeles date -d "$ts" '+%Y-%m-%dT%H:%M:%S%:z')
  last_ts=$(jq -r ".[$k].events[-1].ts" $events.grouped)
  iso_close=$(TZ=America/Los_Angeles date -d "$last_ts" '+%Y-%m-%dT%H:%M:%S%:z')
  close_stamp=$(TZ=America/Los_Angeles date -d "$last_ts" '+%Y-%m%d-%H:%M')
  sid=$(jq -r ".[$k].events[0].sid" $events.grouped | cut -c1-8)
  subj=$(jq -r ".[$k].events[0].body" $events.grouped \
          | head -1 | tr 'A-Z' 'a-z' | sed -E 's/[^a-z0-9 ]//g; s/  +/ /g' \
          | cut -c1-40 | sed -E 's/ +$//; s/ /-/g')
  [[ -z "$subj" ]] && subj="interaction"
  file="$OUT/$id-$local_stamp.user-to-orchestrator.txt"

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
    print -- "# (~/.claude/projects/-home-milnes-projects-ScottLean4/$sid….jsonl),"
    print -- "# not from context: this conversation was compacted, so the assistant's"
    print -- "# own recollection covers only its tail. Timestamps are the recorded"
    print -- "# per-message times in America/Los_Angeles, second resolution."
    print -- ""
    jq -r ".[$k].events[] |
      if .kind == \"USER\" then \"## turn — user \" + .ts + \"\n\n\" + .body + \"\n\"
      elif .kind == \"TEXT\" then \"## turn — assistant \" + .ts + \"\n\n\" + .body + \"\n\"
      else \"    \" + .body end" $events.grouped \
    | TZ=America/Los_Angeles awk '
        /^## turn — (user|assistant) / {
          role=$4; ts=$5
          cmd="TZ=America/Los_Angeles date -d \"" ts "\" \"+%Y-%m-%dT%H:%M:%S%:z\""
          cmd | getline pretty; close(cmd)
          print "## turn — " role " " pretty
          next
        }
        { print }'
  } > "$file"
done

print -- "wrote $n files to $OUT"
