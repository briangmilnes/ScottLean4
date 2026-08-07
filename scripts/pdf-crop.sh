#!/usr/bin/env bash
# pdf-crop.sh — render a rectangular crop of one PDF page to PNG at high dpi.
#
# Why this exists: distinguishing ♯ from ♮ from ♭ in `Gunter Scott 1990.pdf`
# needs more pixels than a whole-page render survives after downscaling. The
# glyphs differ by one stroke, and the operator list of Lemma 28 turns on which
# of the three is printed. `pdftoppm`'s -x/-y/-W/-H crop is in pixels at the
# chosen -r, so the caller gives dpi-scaled coordinates. One allowlisted
# command, per the project's no-chaining rule.
#
# Usage: pdf-crop.sh <pdf> <page> <dpi> <x> <y> <w> <h> <out-prefix>
set -euo pipefail
pdftoppm -png -r "$3" -f "$2" -l "$2" -x "$4" -y "$5" -W "$6" -H "$7" "$1" "$8"
ls -la "$(dirname "$8")"
