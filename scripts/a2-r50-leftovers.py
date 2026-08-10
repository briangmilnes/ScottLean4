#!/usr/bin/env python3
"""a2-r50-leftovers.py — report token occurrences of the 140 retired names.

Why this exists: the elaborator finds every stale *reference site*, but it cannot
see a retired name written inside a docstring or a comment. After phase 2 builds
clean, any surviving token occurrence of a retired name is prose citing a
declaration that no longer exists. This measures them so the report can state a
number instead of a guess; it does not modify anything.

Output: one line per occurrence, then a per-name tally.
"""
import re
from collections import Counter
from pathlib import Path

ROOT = Path("/home/milnes/projects/ScottLean4-agent2/ScottDomains/ScottDomains")
MAP_TSV = ROOT.parent / "analyses" / "a2-r50-aliases.tsv"

IDENT = r"[A-Za-z0-9_'!?]"
olds = set()
for line in MAP_TSV.read_text().splitlines():
    if line and not line.startswith("#"):
        olds.add(line.split("\t")[3])

pat = re.compile(r"(?<!" + IDENT + r")(" + "|".join(
    sorted(map(re.escape, olds), key=len, reverse=True)) + r")(?!" + IDENT + r")")

tally = Counter()
for path in sorted(ROOT.rglob("*.lean")):
    for i, row in enumerate(path.read_text().splitlines(), 1):
        for mo in pat.finditer(row):
            tally[mo.group(1)] += 1
            print(f"{path.relative_to(ROOT)}:{i}\t{mo.group(1)}\t{row.strip()[:110]}")
print("--- per name ---")
for name, n in tally.most_common():
    print(f"{n}\t{name}")
print(f"total: {sum(tally.values())}")
