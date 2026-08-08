#!/usr/bin/env python3
"""a3-ring-profile.py — radial ink profile about a point, to calibrate a3-find-circles.py.

Why this exists: a3-find-circles.py detects a vertex by requiring all 32 samples
on a circle of radius R to land on ink, so R must sit inside the annulus the
scanned glyph's stroke occupies. Guessing R from a downscaled view failed (R=13
and R=17 both found only the filled discs). This prints, for radii 1..Rmax, how
many of 32 ring samples are inked, so the open circle's stroke annulus can be
read off directly.

Usage: a3-ring-profile.py <png> <cx> <cy> <rmax> [threshold]
"""
import sys
from math import cos, sin, pi
from PIL import Image

im = Image.open(sys.argv[1]).convert("L")
cx, cy, rmax = int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
thresh = int(sys.argv[5]) if len(sys.argv) > 5 else 128
W, H = im.size
px = im.tobytes()
NS = 32
print("r\tinked/32")
for r in range(1, rmax + 1):
    n = 0
    for k in range(NS):
        x = cx + int(round(r * cos(2 * pi * k / NS)))
        y = cy + int(round(r * sin(2 * pi * k / NS)))
        if 0 <= x < W and 0 <= y < H and px[y * W + x] < thresh:
            n += 1
    print("%d\t%d" % (r, n))
