#!/usr/bin/env python3
"""a3-find-circles.py — locate the vertex glyphs of a scanned Hasse diagram.

Why this exists: `Gunter Scott 1990.pdf` is a Paper-Capture rebuild whose page
image is an empty 30-byte JBIG2 stub, so the *edges* of Figure 4 are gone from
that file (only the Type 3 circle glyphs survive; `mutool draw -F trace` proves
it). The edges do survive in the 1989 tech-report scan of the same figure. To
transcribe them the vertex centres must be measured, not eyeballed: a
downscaled render gives +/- 5 pt reading error, which is enough to confuse the
21.6 pt and 36 pt offsets the drawing uses.

Method. A vertex is either an open circle (a ring) or a filled disc; a line
crossing a point is neither. Sample 32 points on a circle of radius R about a
candidate centre and count how many land on ink. A ring or a disc scores 32; a
straight line scores about 4. Take connected clusters of high-scoring centres
and report each cluster's centroid, then classify: ink at the centroid means a
filled disc, background means an open circle.

Cost: O(W*H*32/stride^2) ink tests, all integer indexing into one bytes object.
At 300 dpi with stride 2 that is about 10^7 operations for a figure-sized crop,
a few seconds of CPython.

Usage: a3-find-circles.py <png> <radius-px> [threshold 0-255] [stride]
Output: one TSV row per vertex — x, y, filled/open, ring score, cluster size.
"""
import sys
from math import cos, sin, pi
from PIL import Image


def main() -> int:
    path = sys.argv[1]
    R = float(sys.argv[2])
    thresh = int(sys.argv[3]) if len(sys.argv) > 3 else 128
    stride = int(sys.argv[4]) if len(sys.argv) > 4 else 2

    im = Image.open(path).convert("L")
    W, H = im.size
    px = im.tobytes()

    NS = 32
    ring = [(int(round(R * cos(2 * pi * k / NS))), int(round(R * sin(2 * pi * k / NS))))
            for k in range(NS)]

    def ink(x, y):
        return px[y * W + x] < thresh

    hits = set()
    m = int(R) + 1
    for y in range(m, H - m, stride):
        for x in range(m, W - m, stride):
            n = 0
            for dx, dy in ring:
                if px[(y + dy) * W + x + dx] >= thresh:
                    break               # one gap in the ring disqualifies it
                n += 1
            if n == NS:
                hits.add((x, y))

    # cluster the hits by 8-connectivity on the stride grid
    seen = set()
    out = []
    for h in sorted(hits):
        if h in seen:
            continue
        stack, comp = [h], []
        seen.add(h)
        while stack:
            cx, cy = stack.pop()
            comp.append((cx, cy))
            for dx in (-stride, 0, stride):
                for dy in (-stride, 0, stride):
                    n = (cx + dx, cy + dy)
                    if n in hits and n not in seen:
                        seen.add(n)
                        stack.append(n)
        sx = sum(p[0] for p in comp) / len(comp)
        sy = sum(p[1] for p in comp) / len(comp)
        out.append((sx, sy, len(comp)))

    print("x\ty\tkind\tclustersize")
    for sx, sy, n in sorted(out, key=lambda t: (round(t[1]), round(t[0]))):
        kind = "filled" if ink(int(round(sx)), int(round(sy))) else "open"
        print("%.1f\t%.1f\t%s\t%d" % (sx, sy, kind, n))
    print("# %d vertices, image %dx%d, R=%g stride=%d" % (len(out), W, H, R, stride),
          file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main())
