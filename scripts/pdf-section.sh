#!/usr/bin/env bash
# pdf-section.sh — extract a page range of a PDF as text for reading in-context.
#
# Why this exists: `Gunter Scott 1990.pdf` uses Type 3 bitmap fonts whose glyph
# names do not map to Unicode, so `pdftotext` mangles the operator symbols
# (`♮`/`♯`/`♭` come out as `\`/`]`/`[`, and both `→` and `◦→` come out as `!`).
# Reading the raw extraction alone therefore misreports Lemma 28's operator list,
# which is exactly the defect r0034 and r0036 were sent to fix. This script does
# the extraction in one allowlisted command (the project forbids chained shell
# commands) and writes the result under the scratchpad so it can be Read.
#
# Usage: pdf-section.sh <pdf> <first-page> <last-page> <out-file>
set -euo pipefail
pdftotext -f "$2" -l "$3" -layout "$1" "$4"
wc -l "$4"
