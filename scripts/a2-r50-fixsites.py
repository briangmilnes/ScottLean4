#!/usr/bin/env python3
"""a2-r50-fixsites.py — apply the renames the Lean elaborator asked for.

Why this exists: r0050 phase 2 deletes 140 `alias <old> := <new>` statements and
then has to repoint roughly 700 reference sites. The rename is compiler-driven:
`grep` decides nothing. Every site fixed by this script is a site where the
elaborator emitted

    error: <file>:<line>:<col>: unknown identifier '<name>'

so the *position* and the *identifier* both come from Lean's own parser, not from
a textual search. This script only performs the substitution the compiler named,
at the exact codepoint offset the compiler named, and refuses to act when the
text at that offset is not the identifier reported (which would mean the position
model is wrong and the run must stop rather than corrupt a proof).

Usage:
    a2-r50-fixsites.py <compile-log> [--dry-run]

The alias map is read from the phase-2 inventory TSV written by
a2-r50-aliases.py (columns: file, start, end, old, new).

Cost: O(E + L) for E reported errors over L source lines of the affected files;
one pass per build cycle, and the number of cycles is the depth of the import DAG
below the deleted aliases, not the number of sites.
"""
import re
import sys
from collections import Counter
from pathlib import Path

ROOT = Path("/home/milnes/projects/ScottLean4-agent2")
PKG = ROOT / "ScottDomains"
MAP_TSV = PKG / "analyses" / "a2-r50-aliases.tsv"

# Lean 4.32 spells these `Unknown identifier `x`` / `Unknown constant `x``;
# earlier releases used `unknown identifier 'x'`. Accept both spellings.
# Lean 4.32 spells these ``Unknown identifier `x` ``; earlier releases used
# `unknown identifier 'x'`. A Lean identifier may itself end in `'`, so the
# backtick form must be scanned to its closing backtick, not to the first quote.
ERR = re.compile(
    r"^error: (\S+\.lean):(\d+):(\d+): [Uu]nknown (?:identifier|constant) "
    r"(?:`([^`]+)`|'([^']+)')")
IDENT_CHARS = set(
    "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_'!?ₓ")


def load_map():
    m = {}
    for line in MAP_TSV.read_text().splitlines():
        if not line or line.startswith("#"):
            continue
        _f, _s, _e, old, new = line.split("\t")
        m[old] = new
    return m


def resolve(name, m):
    """Map a written dotted name to its new spelling.

    The renamed declaration can sit anywhere inside the dotted name: preceded by
    namespace components the author spelled out (`SFP.thm14_forward`) and followed
    by projection or dot-notation components (`Recovered.thm14.mpr`). Replace the
    longest earliest contiguous span that the alias map knows, and leave the rest.
    """
    parts = name.split(".")
    n = len(parts)
    for k in range(n):
        for j in range(n, k, -1):
            cand = ".".join(parts[k:j])
            if cand in m:
                return ".".join(parts[:k] + [m[cand]] + parts[j:])
    return None


def main():
    log = Path(sys.argv[1])
    dry = "--dry-run" in sys.argv
    m = load_map()

    sites = {}          # file -> {line -> [(col, old, new)]}
    unmapped = Counter()
    seen = set()
    for line in log.read_text().splitlines():
        mo = ERR.match(line)
        if not mo:
            continue
        rel, ln, col = mo.group(1), int(mo.group(2)), int(mo.group(3))
        name = mo.group(4) if mo.group(4) is not None else mo.group(5)
        key = (rel, ln, col, name)
        if key in seen:
            continue
        seen.add(key)
        new = resolve(name, m)
        if new is None:
            unmapped[name] += 1
            continue
        sites.setdefault(rel, {}).setdefault(ln, []).append((col, name, new))

    fixed = Counter()
    already = Counter()
    refused = []
    for rel, bylines in sorted(sites.items()):
        path = PKG / rel
        text = path.read_text()
        lines = text.split("\n")
        for ln in sorted(bylines):
            row = lines[ln - 1]
            for col, old, new in sorted(bylines[ln], reverse=True):
                # The compiler's column is a 0-based codepoint offset, but the name
                # it reports is the fully-qualified one it tried to resolve, which
                # may carry namespace components the source does not spell out.
                # Take the longest dotted suffix of the reported name that occurs
                # literally at that offset and ends on a token boundary; that is
                # what the author wrote, and it is what gets replaced.
                parts = old.split(".")
                written = None
                for k in range(len(parts)):
                    cand = ".".join(parts[k:])
                    end = col + len(cand)
                    if row[col:end] == cand and (end >= len(row)
                                                 or row[end] not in IDENT_CHARS):
                        written = cand
                        break
                if written is None:
                    # Already repointed by an earlier run over the same log.
                    if any(m[p] in row
                           for p in (".".join(parts[k:]) for k in range(len(parts)))
                           if p in m):
                        already[old] += 1
                        continue
                    refused.append((rel, ln, col, old, row))
                    continue
                repl = resolve(written, m)
                if repl is None:
                    refused.append((rel, ln, col, old, row))
                    continue
                end = col + len(written)
                row = row[:col] + repl + row[end:]
                fixed[written] += 1
            lines[ln - 1] = row
        if not dry:
            path.write_text("\n".join(lines))
        print(f"{rel}\t{sum(len(v) for v in bylines.values())} sites")

    print("--- per identifier ---")
    for name, n in fixed.most_common():
        print(f"{n}\t{name}\t-> {m.get(name, resolve(name, m))}")
    print(f"total sites fixed: {sum(fixed.values())}")
    if already:
        print(f"already repointed by an earlier run: {sum(already.values())}")
    if unmapped:
        print("--- unknown identifiers with no alias entry (inspect by hand) ---")
        for name, n in unmapped.most_common():
            print(f"{n}\t{name}")
    if refused:
        print("--- refused (text at the reported column is not the identifier) ---")
        for rel, ln, col, old, row in refused:
            print(f"{rel}:{ln}:{col}\t{old}\t{row!r}")
        sys.exit(1)


main()
