#!/usr/bin/env python3
"""a2-r50-rename-token.py — rename one identifier token across the package.

Why this exists: r0050 phase 3 renames three modules whose names also occur as
namespaces (`ScottDomains.Thm18`, `ScottDomains.LemThirty`) and as text in
`import` lines, in the package root `ScottDomains.lean`, in qualified references,
and in docstrings. `git mv` moves the file; every one of those other occurrences
has to move with it, and Lean will only report the `import` lines — a qualified
reference through the old namespace fails with a different message, and a
docstring citation fails silently.

Each rename here is of a name that, once the module and namespace are renamed,
exists nowhere: `Thm18`, `JungCor136`, `LemThirty` denote no module, no
namespace, and no declaration. So every token occurrence is a reference to the
renamed thing. Matching is anchored on Lean identifier boundaries, so `Thm18`
never fires inside `thm18_of_propertyM` or `A5Thm137`.

The build is the check: run it after each rename, before starting the next.

Usage: a2-r50-rename-token.py <old> <new> [--dry-run]
"""
import re
import sys
from collections import Counter
from pathlib import Path

PKG = Path("/home/milnes/projects/ScottLean4-agent2/ScottDomains")
IDENT = r"[A-Za-z0-9_'!?]"


def main():
    old, new = sys.argv[1], sys.argv[2]
    dry = "--dry-run" in sys.argv
    pat = re.compile(r"(?<!" + IDENT + r")" + re.escape(old) + r"(?!" + IDENT + r")")

    files = sorted(PKG.joinpath("ScottDomains").rglob("*.lean"))
    files.append(PKG / "ScottDomains.lean")
    total = Counter()
    for path in files:
        text = path.read_text()
        n = len(pat.findall(text))
        if not n:
            continue
        if not dry:
            path.write_text(pat.sub(new, text))
        total[str(path.relative_to(PKG))] = n
        print(f"{path.relative_to(PKG)}\t{n}")
    print(f"total occurrences of `{old}` -> `{new}`: {sum(total.values())} "
          f"in {len(total)} files")


main()
