#!/usr/bin/env bash
# r0047 / agent3 — regenerate and run the quantifier-vacuity detector.
#
#   scripts/a3-r47-qvac.sh
#
# Two steps, in one allowlisted command: `scripts/a5-gen-driver.sh` prepends one
# `import` line per package module to `scripts/a3-r47-qvac-body.lean` (the body
# holds the metaprogram and its four controls), then `scripts/a3-run-lean.sh`
# elaborates the result under `lake env lean` and logs the output to
# ScottDomains/logs/a3-r47-qvac-YYYYMMDD-HHMMSS.<role>.log.
#
# The import block is regenerated from the file tree on every run, so a module
# added after the last sweep cannot silently drop out of the population. That is
# the failure mode this project has hit five times: `import ScottDomains` alone
# yields a Mathlib-only environment and every sweep over it reports zero.
set -eu
root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
"$root/scripts/a5-gen-driver.sh" "$root/scripts/a3-r47-qvac-body.lean" "$root/scripts/a3-r47-qvac.lean"
"$root/scripts/a3-run-lean.sh" a3-r47-qvac
