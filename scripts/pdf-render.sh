#!/usr/bin/env bash
# pdf-render.sh — render one PDF page to a PNG so an agent can Read the glyphs.
#
# Why this exists: `Gunter Scott 1990.pdf` embeds Type 3 bitmap fonts with no
# usable ToUnicode map, so `pdftotext` silently drops or substitutes the
# mathematical operator symbols — `♮`/`♯`/`♭` come out as `\`/`]`/`[`, `→` and
# `⇸` both come out as `!`, and `×`/`⊗`/`⊕` come out as nothing at all. Two
# rounds of this project recorded operator lists that disagreed because they
# were read off that extraction. Rendering the page and looking at it is the
# only reliable decoding available here. One allowlisted command, per the
# project's no-chaining rule.
#
# Usage: pdf-render.sh <pdf> <page> <out-prefix> [dpi]
set -euo pipefail
pdftoppm -png -r "${4:-200}" -f "$2" -l "$2" "$1" "$3"
ls -la "$(dirname "$3")"
