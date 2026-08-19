#!/bin/zsh
# move-scottdomains.sh — copy the ScottDomains *Lean package* from ScottLean4
# into ScottProjects, leaving ScottLean4's GRASE process record behind.
#
# Usage: scripts/move-scottdomains.sh
#
# What moves and why. `ScottLean4/ScottDomains/` holds 1499 tracked files, of
# which only 146 are Lean sources; the rest is process history belonging to
# ScottLean4 (707 logs, 334 prompts, 78 plans, 122 reports, 37 analyses). The
# Lean library is self-contained: measured with `import-closure.sh`, its only
# external dependency is Mathlib, and no Lean file outside the package imports
# it. So the package copies as a directory with no edit to any `import` line.
#
# Copies, does not delete. The source is removed in a separate step once the
# destination is built, so a failed build never leaves the work in neither
# place.
set -e

SRC=${0:A:h}/../ScottDomains
DST=~/projects/ScottProjects/ScottDomains

if [[ -e $DST ]]; then
  print -u2 -- "move-scottdomains: $DST already exists; refusing to overwrite"
  exit 1
fi

mkdir -p $DST

# The package proper: root module, sources, and the three Lake config files.
cp $SRC/ScottDomains.lean   $DST/
cp $SRC/lakefile.toml       $DST/
cp $SRC/lake-manifest.json  $DST/
cp $SRC/lean-toolchain      $DST/
cp -R $SRC/ScottDomains     $DST/ScottDomains

# Documentation and the cited sources travel with the library: module docstrings
# name papers by the package-relative path `ScottDomains/papers/…`, which stays
# correct only if `papers/` moves alongside the modules.
cp $SRC/README.md  $DST/
cp $SRC/README.pdf $DST/
cp -R $SRC/docs    $DST/docs
cp -R $SRC/papers  $DST/papers

# Anything Lake built in the source tree is not carried over; the destination
# rebuilds from scratch against its own pinned Mathlib.
rm -rf $DST/ScottDomains/.lake

print -- "copied to $DST"
print -- "  lean sources: $(find $DST/ScottDomains -name '*.lean' | wc -l | tr -d ' ')"
print -- "  lines:        $(find $DST/ScottDomains -name '*.lean' -exec cat {} + | wc -l | tr -d ' ')"
print -- "  docs:         $(ls -1 $DST/docs | wc -l | tr -d ' ')"
print -- "  papers:       $(ls -1 $DST/papers | wc -l | tr -d ' ')"
print -- ""
print -- "left in ScottLean4/ScottDomains (process record, not moved):"
for d in logs prompts plans reports analyses GunterScott90Images; do
  [[ -d $SRC/$d ]] && print -- "  $d/  $(ls -1 $SRC/$d | wc -l | tr -d ' ') files"
done
