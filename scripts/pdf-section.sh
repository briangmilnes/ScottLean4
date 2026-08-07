#!/usr/bin/env bash
# Extract a page range of a PDF in ScottDomains/papers/ to plain text under the
# scratchpad, then print it.  Exists because reading §7.4 of the source paper
# requires pdftotext plus a page window, which is two commands and a pipe — and
# the project's shell discipline puts anything multi-step into scripts/.
#
# Usage: scripts/pdf-section.sh <pdf-basename> <first-page> <last-page>
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
pdf="$root/ScottDomains/papers/$1"
out="/tmp/claude-1000/-home-milnes-projects-ScottLean4/pdf-section.txt"
mkdir -p "$(dirname "$out")"
pdftotext -layout -f "$2" -l "$3" "$pdf" "$out"
cat "$out"
