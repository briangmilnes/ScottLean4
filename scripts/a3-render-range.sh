#!/usr/bin/env bash
# a3-render-range.sh — render a page range of a PDF to PNGs in one command.
#
# Why this exists: scripts/pdf-render.sh renders a single page, and classifying
# the r0039 diagram candidates means looking at every page in an agent's range
# (agent3 has 34-44, sixteen candidate regions across ten pages). Reading the
# whole page rather than each candidate rectangle also measures the detector's
# false negatives — a diagram it never proposed is only visible in the full
# page. One allowlisted command instead of ten, per the project's
# no-chaining rule.
#
# Usage: a3-render-range.sh <pdf> <first> <last> <out-prefix> [dpi]
set -euo pipefail
pdftoppm -png -r "${5:-150}" -f "$2" -l "$3" "$1" "$4"
ls -la "$(dirname "$4")"
