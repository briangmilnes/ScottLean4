#!/bin/zsh
# scottprojects-cache.sh — materialize ScottDomains' dependencies and fetch the
# Mathlib olean cache, in the ScottProjects checkout.
#
# Why this exists: ScottDomains moved to ~/projects/ScottProjects/ScottDomains
# (ScottLean4 r0094), so a fresh clone on this machine has no .lake/packages and
# no oleans. Running `lake build` first would elaborate all of Mathlib from
# source — hours of work — instead of downloading the prebuilt oleans. This
# fetches the dependency checkouts at their pinned revisions and then pulls the
# olean cache, so scripts/compile.sh only has to elaborate ScottDomains itself.
#
# Requires a cd into the package (lake resolves its root from the working
# directory), which is why this is a script and not a terminal command: a
# compound `cd … && lake …` has no allowlistable prefix.
#
# Usage: scripts/scottprojects-cache.sh
set -e

pkg="$HOME/projects/ScottProjects/ScottDomains"
cd "$pkg"

print -- "=== lake exe cache get (also materializes .lake/packages) ==="
lake exe cache get
print -- "=== done ==="
du -sh "$pkg/.lake/packages" 2>/dev/null || true
