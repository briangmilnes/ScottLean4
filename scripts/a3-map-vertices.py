#!/usr/bin/env python3
"""a3-map-vertices.py — put the 1989 scan's measured circles into 1990 page coordinates.

Why this exists: Figure 4 of `Gunter Scott 1990.pdf` has exact vertex positions
(from `mutool draw -F trace`, the Type 3 circle glyphs T14/14 = open, T14/15 =
filled) but no edges: the page's raster layer is an empty 30-byte JBIG2 stub, so
the connecting lines were dropped by the Paper Capture rebuild. The same figure
in the 1989 tech report (Figure 1.4, physical page 54) is a real scan and does
have its lines, but is skewed and at a slightly different scale.

This fits a 2x2 affine from 1989 image pixels to 1990 PDF points using three
landmark vertices (the three diagrams' bottom elements, which share a page row,
plus the top of the I+++ column for the vertical), maps every measured circle
through it, and reports the nearest 1990 trace vertex with the residual. A small
residual everywhere means the two drawings share a vertex set, so edges read off
the 1989 scan may be drawn at the 1990 coordinates.

Cost: O(|detected| * |trace|) = 27 * 27 distance evaluations.

Usage: a3-map-vertices.py
"""

# 1990 trace vertices: label, x, y (PDF points), kind.
TRACE = [
    ("A1", 119.76, 251.75, "filled"), ("A2", 119.76, 395.75, "open"),
    ("B1", 191.76, 251.75, "filled"), ("B2", 191.76, 323.75, "open"),
    ("B3", 191.76, 395.75, "filled"), ("B4", 191.76, 467.75, "open"),
    ("B5", 299.76, 467.75, "open"),
    ("C1", 407.76, 251.75, "filled"), ("C2", 407.76, 287.75, "open"),
    ("C3", 407.76, 323.75, "filled"), ("C4", 407.76, 359.75, "open"),
    ("C5", 407.76, 395.75, "filled"), ("C6", 407.76, 431.75, "open"),
    ("C7", 407.76, 467.75, "filled"), ("C8", 407.76, 503.75, "open"),
    ("L1", 321.36, 431.75, "open"),
    ("L2", 371.76, 359.75, "open"), ("L3", 371.76, 431.75, "open"),
    ("L4", 386.16, 273.35, "open"), ("L5", 386.16, 345.35, "open"),
    ("L6", 386.16, 417.35, "open"),
    ("R1", 443.76, 287.75, "open"), ("R2", 443.76, 359.75, "open"),
    ("R3", 443.76, 431.75, "open"), ("R4", 479.76, 395.75, "open"),
    ("R5", 515.76, 467.75, "filled"), ("R6", 533.76, 503.75, "open"),
]

# Circles measured by a3-find-circles.py in the 600 dpi crop of the 1989 scan
# (page 54, crop origin 930,690), R=22 stride=2.
DET = [
    (2547.4, 148.7, "open"), (3614.6, 431.1, "open"), (2552.7, 445.3, "filled"),
    (734.4, 464.7, "open"), (3439.4, 731.1, "filled"), (2555.9, 747.3, "open"),
    (1620.8, 753.8, "open"), (2135.1, 856.6, "open"), (2353.8, 904.1, "open"),
    (1686.5, 949.4, "open"), (2913.7, 1030.3, "open"), (2559.9, 1048.4, "filled"),
    (743.6, 1067.8, "filled"), (131.1, 1076.6, "open"), (2966.7, 1318.3, "open"),
    (2563.1, 1341.5, "open"), (2141.4, 1371.2, "open"), (3025.5, 1440.9, "open"),
    (2326.6, 1480.0, "open"), (2568.1, 1638.7, "filled"), (753.6, 1659.2, "open"),
    (2985.0, 1888.4, "open"), (2574.6, 1936.6, "open"), (2209.4, 1957.0, "open"),
    (2579.2, 2236.4, "filled"), (762.4, 2257.4, "filled"), (150.6, 2263.0, "filled"),
]

# Landmarks: A1, B1, C1 share PDF y (the three bottom elements); C7 fixes the
# vertical.  u0,v0 is A1 in image pixels; x0,y0 is A1 in PDF points.
U0, V0, X0, Y0 = 150.6, 2263.0, 119.76, 251.75
EX = (8.4326, -0.09236)     # image displacement per +1 pt of PDF x
EY = (-0.12269, -8.2921)    # image displacement per +1 pt of PDF y
DETM = EX[0] * EY[1] - EY[0] * EX[1]


def to_pdf(u, v):
    du, dv = u - U0, v - V0
    dx = (du * EY[1] - EY[0] * dv) / DETM
    dy = (EX[0] * dv - du * EX[1]) / DETM
    return X0 + dx, Y0 + dy


print("scan_u\tscan_v\tkind\tpdf_x\tpdf_y\tnearest\tdx\tdy\tdist\tkind_ok")
used = {}
for u, v, kind in DET:
    x, y = to_pdf(u, v)
    best = min(TRACE, key=lambda t: (x - t[1]) ** 2 + (y - t[2]) ** 2)
    d = ((x - best[1]) ** 2 + (y - best[2]) ** 2) ** 0.5
    used.setdefault(best[0], []).append(d)
    print("%.1f\t%.1f\t%s\t%.2f\t%.2f\t%s\t%+.2f\t%+.2f\t%.2f\t%s"
          % (u, v, kind, x, y, best[0], x - best[1], y - best[2], d,
             "yes" if kind == best[3] else "NO"))

dupes = [k for k, v in used.items() if len(v) > 1]
missing = [t[0] for t in TRACE if t[0] not in used]
print("\n# matched %d/%d trace vertices; duplicates: %s; unmatched: %s"
      % (len(used), len(TRACE), dupes or "none", missing or "none"))
