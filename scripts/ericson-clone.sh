#!/usr/bin/env bash
# ericson-clone.sh — assemble Ericson/, the vendored checkouts of Lars Ericson's
# four Lean 4 formalizations of Dana Scott's papers.
#
# Sources (from Ericson's letter to Scott, quoted in Ericson/README.md):
#   scott1972      Continuous Lattices (1972)          — on arXiv
#   scott1980      Lambda Calculus: Some Models (1980) — ~1500 pages of Lean
#   scott1982      Domains for Denotational Semantics (1982)
#   scott_models   the interconversion between the three
#
# Clones SOURCE ONLY — no `lake exe cache get`, no `lake build`. Those are done
# separately by ericson-build.sh, because each built project costs ~7 GiB of
# Mathlib oleans and the disk does not hold four of them at once.
#
# Idempotent: an existing checkout is fetched, not re-cloned.

set -uo pipefail
root=/home/milnes/projects/ScottLean4
eric="$root/Ericson"
repos="scott1972 scott1980 scott1982 scott_models"

mkdir -p "$eric"

# The pre-existing scott1972 checkout lives at the repo root; move it in rather
# than re-cloning 7.2 GiB.
if [ -d "$root/scott1972" ] && [ ! -d "$eric/scott1972" ]; then
  mv "$root/scott1972" "$eric/scott1972"
  echo "moved scott1972 into Ericson/"
fi

for r in $repos; do
  if [ -d "$eric/$r/.git" ]; then
    echo "== $r: present, fetching"
    git -C "$eric/$r" fetch --all --quiet
  else
    echo "== $r: cloning"
    git -C "$eric" clone --quiet "https://github.com/catskillsresearch/$r.git"
  fi
done

echo
printf '%-14s %-10s %-12s %s\n' repo size toolchain head
printf '%-14s %-10s %-12s %s\n' -------------- ---------- ------------ ----
for r in $repos; do
  d="$eric/$r"
  [ -d "$d" ] || continue
  tc=$( [ -f "$d/lean-toolchain" ] && tr -d '\n' < "$d/lean-toolchain" || echo "-" )
  printf '%-14s %-10s %-12s %s\n' \
    "$r" \
    "$(du -sh "$d" 2>/dev/null | cut -f1)" \
    "${tc#leanprover/lean4:}" \
    "$(git -C "$d" log --oneline -1 2>/dev/null | cut -c1-50)"
done

echo
echo "lean files and lines per repo:"
for r in $repos; do
  d="$eric/$r"
  [ -d "$d" ] || continue
  n=$(find "$d" -name '*.lean' -not -path '*/.lake/*' | wc -l)
  l=$(find "$d" -name '*.lean' -not -path '*/.lake/*' -exec cat {} + 2>/dev/null | wc -l)
  printf '  %-14s %5s files %9s lines\n' "$r" "$n" "$l"
done

echo
df -h /home/milnes/projects | tail -1
