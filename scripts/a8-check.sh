#!/usr/bin/env bash
# a8-check.sh — r0044 Class 4 (reading half), agent8.
#
# Elaborates a scratch .lean file against the built package, so a claim about a
# declaration is checked against the `.olean` the kernel produced rather than
# against a source line.  r0044's evidence rule requires this: a source line can
# assert something it does not elaborate to.
#
# The scratch file lives outside ScottDomains/, so no package .lean file is
# touched.  Modelled on scripts/check-thm18-composition.sh.
#
# Usage: scripts/a8-check.sh <absolute path to scratch .lean file>
set -e
cd /home/milnes/projects/ScottLean4-agent8/ScottDomains
lake env lean "$1"
