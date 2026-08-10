#!/usr/bin/env python3
"""a2-r50-aliases.py — inventory and then delete the `alias <old> := <new>`
scaffolding that r0050 phase 1 left beside each renamed numbered-result
declaration.

Why this exists: phase 2 deletes all 140 alias declarations and must then fix
every stale reference site. The *decision* about which sites are stale belongs to
the Lean elaborator, not to this script (see a2-r50-fixsites.py) — this one only
handles the alias statements themselves. An alias statement is recognized by an
`alias` keyword at column 0, which is unambiguous in Lean's grammar: `alias` is a
command and commands start at column 0, so no expression, string literal, or
comment body can be mistaken for one. A statement may spill onto a second line
when the new name is long.

Modes:
  (default)  write a TSV inventory to stdout: file, start_line, end_line, old, new
  --delete   remove exactly those line ranges from the files

Deleting whole, fully-identified statements is a line operation, not a rewrite of
Lean expressions; no identifier inside any declaration is touched here.
"""
import re
import sys
from pathlib import Path

ROOT = Path("/home/milnes/projects/ScottLean4-agent2/ScottDomains/ScottDomains")


def scan(path):
    """Return [(start_index, end_index, old, new)] with 0-based inclusive indices."""
    lines = path.read_text().splitlines()
    out = []
    i = 0
    while i < len(lines):
        m = re.match(r"^alias\s+(\S+)\s*:=\s*(\S*)\s*$", lines[i])
        if m:
            old, new = m.group(1), m.group(2)
            end = i
            if not new:
                end = i + 1
                new = lines[end].strip()
            out.append((i, end, old, new))
            i = end + 1
            continue
        i += 1
    return lines, out


def main():
    delete = "--delete" in sys.argv
    total = 0
    for path in sorted(ROOT.rglob("*.lean")):
        lines, found = scan(path)
        if not found:
            continue
        total += len(found)
        if not delete:
            for s, e, old, new in found:
                print(f"{path}\t{s+1}\t{e+1}\t{old}\t{new}")
            continue
        drop = set()
        for s, e, _old, _new in found:
            drop.update(range(s, e + 1))
            # A blank separator line immediately after the statement goes with it,
            # but only when the line before the statement is also blank, so the
            # surrounding vertical spacing is preserved rather than collapsed.
            after = e + 1
            before = s - 1
            if (after < len(lines) and lines[after].strip() == ""
                    and before >= 0 and lines[before].strip() == ""):
                drop.add(after)
        kept = [ln for i, ln in enumerate(lines) if i not in drop]
        path.write_text("\n".join(kept) + "\n")
        print(f"{path}\t{len(found)} deleted")
    print(f"# {total} alias declarations", file=sys.stderr)


main()
