#!/bin/zsh
# a4-lint.sh — run a standalone Lean probe file against the built ScottDomains
# oleans, without adding a module to the package.
#
# Usage: scripts/a4-lint.sh <probe.lean>
#
# Why it exists (r0044, Class 2 vacuity sweep): the sweep needs to ask the Lean
# *environment* questions — `#lint only unusedArguments in ScottDomains`,
# `#check @d`, `#synth`, `example : C X := by infer_instance` — and every such
# question must be asked of the built artifact, not of a source line. Adding a
# probe module under ScottDomains/ScottDomains/ would change the round's frozen
# counts (100 modules / 37300 lines / 1773 theorems), so the probe lives outside
# the package and is elaborated by `lake env lean`, which sets LEAN_PATH from the
# lakefile so `import ScottDomains.…` resolves against .lake/build/lib.
#
# Cost: elaborating the probe is dominated by loading the import closure
# (~10 s for the whole package); the linter pass over ~1.8e3 declarations
# dominates for `#lint`.
set -e
probe="$1"
if [[ -z "$probe" ]]; then
  print -u2 "usage: a4-lint.sh <probe.lean>"
  exit 2
fi
cd "${0:A:h}/../ScottDomains"
lake env lean "$probe" 2>&1 | sed 's/\x1b\[[0-9;]*[mGKHABCDEFJST]//g'
