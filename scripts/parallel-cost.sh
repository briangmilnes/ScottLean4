#!/bin/zsh
# Measure how the whole-library build scales when N checkouts build at once.
# Each checkout has its own .lake/build but shares .lake/packages by symlink,
# which is exactly the r0028 five-agent layout.
set -e

roots=(/home/milnes/projects/ScottLean4 \
       /home/milnes/projects/ScottLean4-agent1 \
       /home/milnes/projects/ScottLean4-agent2 \
       /home/milnes/projects/ScottLean4-agent3 \
       /home/milnes/projects/ScottLean4-agent4 \
       /home/milnes/projects/ScottLean4-agent5)

cold () {   # drop only our library's artifacts, keep Mathlib
  local r=$1
  rm -rf $r/ScottDomains/.lake/build/lib/lean/ScottDomains \
         $r/ScottDomains/.lake/build/lib/lean/ScottDomains.olean \
         $r/ScottDomains/.lake/build/lib/lean/ScottDomains.ilean \
         $r/ScottDomains/.lake/build/lib/lean/ScottDomains.trace 2>/dev/null || true
}

run () {
  local n=$1
  local pids=()
  for i in {1..$n}; do cold ${roots[$i]}; done
  local t0=$(date +%s.%N)
  for i in {1..$n}; do
    ( cd ${roots[$i]} && ./scripts/compile.sh -r parallel-probe ${=JOBS:-} > /dev/null 2>&1 ) &
    pids+=($!)
  done
  local fails=0
  for p in $pids; do wait $p || fails=$((fails + 1)); done
  local t1=$(date +%s.%N)
  printf "N=%d  span=%.2fs  failures=%d  loadavg=%s\n" \
    $n $((t1 - t0)) $fails "$(cut -d' ' -f1 /proc/loadavg)"
}

for n in ${=NS:-1 2 3 6}; do run $n; done
