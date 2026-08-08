#!/usr/bin/env bash
# extract-figures.sh — render the four figures of Gunter & Scott 1990 to PNG.
#
# Why this renders rather than extracts: `pdfimages -list` on the source reports
# one embedded image per page, every one a 2550x3298 JBIG2 grayscale mask of
# 30-486 bytes — near-empty full-page scan layers, not figures. The paper's
# figures are drawn with the same Type 3 bitmap fonts and vector line art that
# carry its mathematics, so `pdfimages` yields nothing usable and rendering the
# page is the only way to get the picture. Same reason `pdf-render.sh` exists for
# reading the operator glyphs.
#
# Figure pages, each confirmed by locating the *caption* on that page rather than
# a reference to it. That distinction matters and cost one wrong pass: grepping
# for "Figure 3" returns physical pages 31 and 33, which merely *mention* it,
# while all three parts 3a, 3b and 3c sit together on page 32 with the caption.
#
#   Figure 1  Examples of cpo's                                  physical page  5
#   Figure 2  The lift of a cpo                                  physical page 21
#   Figure 3  Posets that are not Plotkin orders (a, b, c)       physical page 32
#   Figure 4  A domain for representing operators on bifinites   physical page 44
#
# Physical page N is printed page N-1 in this scan.
#
# Figure 3 is the one the development cites most: 3a is Jung's property m, 3b is
# property M, and 3c has `U^\infty(u)` infinite — the three cases of Theorem 18,
# and the reason `MinimalUpperBounds.lean` exists. It gets a cropped version too,
# with coordinates measured off the 300 dpi render.
#
# Usage: extract-figures.sh [dpi]     (default 300)
set -euo pipefail

root=/home/milnes/projects/ScottLean4
pdf="$root/ScottDomains/papers/Gunter Scott 1990.pdf"
out="$root/GunterScott90Images"
dpi="${1:-300}"

mkdir -p "$out"

render() {  # render <physical-page> <name>
  pdftoppm -png -r "$dpi" -f "$1" -l "$1" "$pdf" "$out/$2"
}

render  5 figure-1-examples-of-cpos
render 21 figure-2-lift-of-a-cpo
render 32 figure-3-posets-not-plotkin-orders
render 44 figure-4-domain-for-operators-on-bifinites

# Figure 3's drawing alone, without the surrounding text. Coordinates are in
# pixels at $dpi and were measured on the 300 dpi page render; they scale with
# dpi, so pass 600 for a larger crop of the same region.
s=$(( dpi / 300 )); [ "$s" -lt 1 ] && s=1
pdftoppm -png -r "$dpi" -f 32 -l 32 \
  -x $((250 * s)) -y $((400 * s)) -W $((2100 * s)) -H $((1080 * s)) \
  "$pdf" "$out/figure-3-crop"

ls -la "$out"
