#!/usr/bin/env python3
"""find-diagrams.py — locate every diagram in Gunter & Scott 1990.

Why this is a geometry problem and not a content-stream one, measured before
writing any of it:

  * `pdfimages -list` reports one embedded image per page, each a near-empty
    JBIG2 mask of 30-486 bytes. There are no embedded figures to extract.
  * `mutool draw -F trace` on the figure page reports 1430 glyphs, 223 spans,
    one image and **zero path operators**. The diagrams are not vector art.
    They are drawn from TeX's line and circle fonts as glyph pieces, which is
    how a 1990 LaTeX `picture` environment works.
  * `pdffonts` gives every Type 3 font the name `T8`..`T20` with Custom
    encoding, so the font cannot discriminate diagram glyphs from text glyphs
    either.

What does discriminate: body text sets as short horizontal ink runs at a
regular vertical pitch — a line of type is ~10 px tall at 100 dpi with a gap
below it. A diagram has ink in almost every row over its whole height, because
its edges run vertically. So a contiguous run of inked rows taller than about
two text lines is a diagram, and that is what this finds.

Reads a PBM (P4) rendered by pdftoppm -mono with the standard library only;
no numpy, no PIL, nothing to install.

Usage:
    find-diagrams.py <pdf> [first-page] [last-page]

Emits one TSV row per detected diagram:
    page  y0  y1  x0  x1  height  rows_inked   (all in pixels at DPI)
"""

import os
import subprocess
import sys
import tempfile

DPI = 100
# The discriminator is ink *density* per row, not run height. A first attempt
# used contiguous inked-row runs with a 12 px gap tolerance and returned one run
# covering all 1100 rows of every page: body text sets at ~16 px pitch with ~6 px
# interline gaps, so any tolerance large enough to hold a picture together also
# welds every paragraph into one blob.
#
# Density separates them cleanly. A line of type at 100 dpi over a 6-inch measure
# inks 100-400 pixels in its row. A diagram row is a handful of thin strokes —
# two to six crossings, well under 60 pixels — because a Hasse diagram is mostly
# white space with a few edges running through it.
# Overridable from the environment so the thresholds can be tuned by measurement
# on a known page rather than guessed: DENSE_MIN=90 find-diagrams.py … 32 32
DENSE_MIN = int(os.environ.get("DENSE_MIN", 60))         # rows this inked are body text
MIN_INK_PER_ROW = int(os.environ.get("MIN_INK_PER_ROW", 1))
MIN_RUN_PX = int(os.environ.get("MIN_RUN_PX", 40))       # taller than a displayed formula
MIN_SPARSE_ROWS = int(os.environ.get("MIN_SPARSE_ROWS", 25))
DEBUG = os.environ.get("DEBUG_INK")                       # page number: dump row ink


# Grayscale, not bilevel. `pdftoppm -mono` dithers the near-white JBIG2 page
# mask, which put a 213-pixel ink row every 20th row of every page — a perfectly
# periodic artifact that swamps the signal. Rendering gray and thresholding here
# removes it: the background sits near 255 and never crosses INK_MAX.
INK_MAX = int(os.environ.get("INK_MAX", 160))


def render_pgm(pdf, page, out):
    subprocess.run(
        ["pdftoppm", "-gray", "-r", str(DPI), "-f", str(page), "-l", str(page),
         pdf, out],
        check=True, capture_output=True)
    for suffix in ("-%02d.pgm" % page, "-%03d.pgm" % page, "-%d.pgm" % page):
        if os.path.exists(out + suffix):
            return out + suffix
    raise SystemExit("find-diagrams: no PGM produced for page %d" % page)


def read_pgm(path):
    """Return (width, height, rows) with rows a list of bytes, one per pixel."""
    with open(path, "rb") as fh:
        data = fh.read()
    if not data.startswith(b"P5"):
        raise SystemExit("find-diagrams: expected a P5 PGM")
    fields, i = [], 2
    while len(fields) < 3:            # width, height, maxval
        while i < len(data) and data[i:i + 1].isspace():
            i += 1
        if data[i:i + 1] == b"#":
            while data[i:i + 1] not in (b"\n", b""):
                i += 1
            continue
        j = i
        while j < len(data) and not data[j:j + 1].isspace():
            j += 1
        fields.append(int(data[i:j]))
        i = j
    i += 1                            # one whitespace byte after the header
    w, h, _maxval = fields
    rows = [data[i + r * w:i + (r + 1) * w] for r in range(h)]
    return w, h, rows


def row_ink(row, w):
    """Number of pixels dark enough to count as ink."""
    return sum(1 for v in row if v <= INK_MAX)


def col_extent(rows, y0, y1, w):
    """Leftmost and rightmost inked column over rows [y0, y1)."""
    lo, hi = w, -1
    for y in range(y0, y1):
        row = rows[y]
        for x, v in enumerate(row):
            if v <= INK_MAX:
                if x < lo:
                    lo = x
                if x > hi:
                    hi = x
    return lo, hi


def diagrams_on_page(pdf, page, tmpdir):
    pbm = render_pgm(pdf, page, os.path.join(tmpdir, "pg"))
    w, h, rows = read_pgm(pbm)
    ink = [row_ink(rows[y], w) for y in range(h)]
    if DEBUG and int(DEBUG) == page:
        for y in range(0, h, 5):
            print("ink\t%d\t%d" % (y, ink[y]), file=sys.stderr)
    dense = [v >= DENSE_MIN for v in ink]
    inked = [v >= MIN_INK_PER_ROW for v in ink]

    # Maximal bands containing no body-text row. A picture lives inside one.
    bands, start = [], None
    for y in range(h):
        if not dense[y]:
            if start is None:
                start = y
        elif start is not None:
            bands.append((start, y))
            start = None
    if start is not None:
        bands.append((start, h))

    out = []
    for b0, b1 in bands:
        # Trim the blank margins so the crop is the picture, not the band.
        ys = [y for y in range(b0, b1) if inked[y]]
        if not ys:
            continue
        y0, y1 = ys[0], ys[-1] + 1
        if y1 - y0 < MIN_RUN_PX or len(ys) < MIN_SPARSE_ROWS:
            continue
        x0, x1 = col_extent(rows, y0, y1, w)
        if x1 < x0:
            continue
        out.append((page, y0, y1, x0, x1, y1 - y0, len(ys)))
    os.remove(pbm)
    return out


def main():
    if len(sys.argv) < 2:
        raise SystemExit(__doc__)
    pdf = sys.argv[1]
    npages = int(subprocess.run(["pdfinfo", pdf], check=True, capture_output=True,
                                text=True).stdout.split("Pages:")[1].split()[0])
    first = int(sys.argv[2]) if len(sys.argv) > 2 else 1
    last = int(sys.argv[3]) if len(sys.argv) > 3 else npages

    print("page\ty0\ty1\tx0\tx1\theight\trows_inked\tdpi=%d" % DPI)
    with tempfile.TemporaryDirectory() as tmpdir:
        for page in range(first, last + 1):
            for row in diagrams_on_page(pdf, page, tmpdir):
                print("\t".join(str(v) for v in row))


if __name__ == "__main__":
    main()
