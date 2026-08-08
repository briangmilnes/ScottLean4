#!/usr/bin/env python3
"""a3-find-edges.py — recover the covering relation of a scanned Hasse diagram.

Why this exists: Figure 4 of `Gunter Scott 1990.pdf` has exact vertex positions
but no edges (the page's raster layer is an empty 30-byte JBIG2 stub). The 1989
tech-report scan of the same figure keeps its lines, and a3-find-circles.py has
already measured all 27 vertex centres in that scan. Reading twenty-odd lines
out of a crowded fan by eye is unreliable, so test each pair instead: a segment
between two vertices is an edge exactly when every sample along it lands on ink.

A straight line drawn between two non-adjacent vertices crosses white paper
almost immediately, so the test has a large margin; the two failure modes are
(a) collinear triples, where u-w is fully covered by the drawn u-v and v-w, and
(b) a chord that happens to run along another edge. Both are handled by
discarding any pair whose segment passes close to a third vertex, which is
reported separately rather than silently dropped.

Cost: O(P * S * (2t+1)^2) byte tests for P pairs, S samples, tolerance t.
For 27 vertices at 600 dpi that is about 10^7 tests, a few seconds.

Usage: a3-find-edges.py <png> [threshold] [tolerance-px] [skip-px]
"""
import sys
from PIL import Image

# label, x, y in the 600 dpi crop of the 1989 scan (page 54, origin 930,690),
# as measured by a3-find-circles.py with R=22.
V = [
    ("C8", 2547.4, 148.7), ("R6", 3614.6, 431.1), ("C7", 2552.7, 445.3),
    ("B4", 734.4, 464.7), ("R5", 3439.4, 731.1), ("C6", 2555.9, 747.3),
    ("B5", 1620.8, 753.8), ("L3", 2135.1, 856.6), ("L6", 2353.8, 904.1),
    ("L1", 1686.5, 949.4), ("rc", 2913.7, 1030.3), ("C5", 2559.9, 1048.4),
    ("B3", 743.6, 1067.8), ("A2", 131.1, 1076.6), ("rd", 2966.7, 1318.3),
    ("C4", 2563.1, 1341.5), ("L2", 2141.4, 1371.2), ("re", 3025.5, 1440.9),
    ("L5", 2326.6, 1480.0), ("C3", 2568.1, 1638.7), ("B2", 753.6, 1659.2),
    ("rf", 2985.0, 1888.4), ("C2", 2574.6, 1936.6), ("L4", 2209.4, 1957.0),
    ("C1", 2579.2, 2236.4), ("B1", 762.4, 2257.4), ("A1", 150.6, 2263.0),
]


def main() -> int:
    im = Image.open(sys.argv[1]).convert("L")
    thresh = int(sys.argv[2]) if len(sys.argv) > 2 else 128
    tol = int(sys.argv[3]) if len(sys.argv) > 3 else 5
    skip = float(sys.argv[4]) if len(sys.argv) > 4 else 30.0
    W, H = im.size
    px = im.tobytes()

    def near_ink(x, y):
        for dy in range(-tol, tol + 1):
            yy = int(y) + dy
            if not (0 <= yy < H):
                continue
            row = yy * W
            for dx in range(-tol, tol + 1):
                xx = int(x) + dx
                if 0 <= xx < W and px[row + xx] < thresh:
                    return True
        return False

    def dist_point_seg(p, a, b):
        ax, ay = a
        bx, by = b
        vx, vy = bx - ax, by - ay
        L2 = vx * vx + vy * vy
        t = ((p[0] - ax) * vx + (p[1] - ay) * vy) / L2
        t = max(0.0, min(1.0, t))
        return ((ax + t * vx - p[0]) ** 2 + (ay + t * vy - p[1]) ** 2) ** 0.5

    print("u\tv\tcovered\tsamples\tverdict\tblocked_by")
    for i in range(len(V)):
        for j in range(i + 1, len(V)):
            ln, ax, ay = V[i]
            bn, bx, by = V[j]
            L = ((bx - ax) ** 2 + (by - ay) ** 2) ** 0.5
            if L <= 2 * skip + 10:
                continue
            n = max(20, int((L - 2 * skip) / 4))
            t0, t1 = skip / L, 1.0 - skip / L
            ok = 0
            for k in range(n + 1):
                t = t0 + (t1 - t0) * k / n
                if near_ink(ax + t * (bx - ax), ay + t * (by - ay)):
                    ok += 1
            frac = ok / (n + 1)
            if frac < 0.97:
                continue
            blockers = [V[m][0] for m in range(len(V))
                        if m != i and m != j
                        and dist_point_seg((V[m][1], V[m][2]), (ax, ay), (bx, by)) < 26]
            print("%s\t%s\t%.3f\t%d\t%s\t%s"
                  % (ln, bn, frac, n + 1,
                     "edge" if not blockers else "via", ",".join(blockers) or "-"))
    return 0


if __name__ == "__main__":
    sys.exit(main())
