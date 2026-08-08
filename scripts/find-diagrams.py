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
# A run of inked rows taller than this is a diagram rather than a line of type.
# Body text at 100 dpi sets ~10 px tall with ~5 px leading; the tallest single
# text run measured in this paper is 22 px (a displayed formula with a fraction).
MIN_RUN_PX = 30
# Rows with less ink than this are treated as blank, which keeps a stray
# descender from welding two text lines into a false diagram.
MIN_INK_PER_ROW = 2
# Gap in blank rows tolerated inside one diagram: the parts of Figure 3 are
# separated by white space but belong to one picture.
MAX_GAP_PX = 12


def render_pbm(pdf, page, out):
    subprocess.run(
        ["pdftoppm", "-mono", "-r", str(DPI), "-f", str(page), "-l", str(page),
         pdf, out],
        check=True, capture_output=True)
    for suffix in ("-%02d.pbm" % page, "-%03d.pbm" % page, "-%d.pbm" % page):
        if os.path.exists(out + suffix):
            return out + suffix
    raise SystemExit("find-diagrams: no PBM produced for page %d" % page)


def read_pbm(path):
    """Return (width, height, rows) with rows a list of bytearrays, 1 = ink."""
    with open(path, "rb") as fh:
        data = fh.read()
    if not data.startswith(b"P4"):
        raise SystemExit("find-diagrams: expected a P4 PBM")
    # Header: P4, then width height, skipping '#' comments; single whitespace
    # separators after the magic.
    fields, i = [], 2
    while len(fields) < 2:
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
    i += 1  # exactly one whitespace byte after the header
    w, h = fields
    stride = (w + 7) // 8
    rows = [data[i + r * stride:i + (r + 1) * stride] for r in range(h)]
    return w, h, rows


def row_ink(row, w):
    """Number of inked pixels in a packed PBM row (bit set = black)."""
    return sum(bin(b).count("1") for b in row)


def col_extent(rows, y0, y1, w):
    """Leftmost and rightmost inked column over rows [y0, y1)."""
    stride = (w + 7) // 8
    lo, hi = w, -1
    for y in range(y0, y1):
        row = rows[y]
        for bi in range(stride):
            b = row[bi]
            if not b:
                continue
            for bit in range(8):
                if b & (0x80 >> bit):
                    x = bi * 8 + bit
                    if x < lo:
                        lo = x
                    if x > hi:
                        hi = x
    return lo, hi


def diagrams_on_page(pdf, page, tmpdir):
    pbm = render_pbm(pdf, page, os.path.join(tmpdir, "pg"))
    w, h, rows = read_pbm(pbm)
    inked = [row_ink(rows[y], w) >= MIN_INK_PER_ROW for y in range(h)]

    # Contiguous inked runs, tolerating short blank gaps.
    runs, start, gap = [], None, 0
    for y in range(h):
        if inked[y]:
            if start is None:
                start = y
            gap = 0
        elif start is not None:
            gap += 1
            if gap > MAX_GAP_PX:
                runs.append((start, y - gap))
                start, gap = None, 0
    if start is not None:
        runs.append((start, h))

    out = []
    for y0, y1 in runs:
        if y1 - y0 < MIN_RUN_PX:
            continue
        x0, x1 = col_extent(rows, y0, y1, w)
        if x1 < x0:
            continue
        out.append((page, y0, y1, x0, x1, y1 - y0,
                    sum(1 for y in range(y0, y1) if inked[y])))
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
