#!/usr/bin/env python3
"""a6-decls.py — comment-aware lexer for EVERY Lean declaration kind, not just
`theorem`/`lemma`.

`scripts/lean-decls.py` counts proofs, so its opener regex matches only
`theorem` and `lemma`. Round r0044's Class-3 stream (agent6) has to find the
declaration kinds that a `sorry` count cannot see:

  * `axiom`            — an assumed proposition, discharged by nothing;
  * `def … : Prop`     — a claim written down as a definition, so the kernel
                         never asks for a proof;
  * `structure`/`class`— an obligation that is discharged only when some term
                         instantiates it, and never if none does.

It reuses `lean-decls.py`'s `strip_comments` lexer verbatim (nested `/- … -/`,
`--`, string literals) so declarations sitting inside block comments are not
counted — the defect r0038 found three times.

Output is `path:line<TAB>kind<TAB>name<TAB>attrs`, one line per declaration,
where `attrs` is the raw attribute group if one was on the opener line or the
line above, else `-`. Names are UNQUALIFIED, exactly as written in the source;
join to the Lean environment by (module, suffix), never by name alone.

Usage:
    a6-decls.py <file.lean> …            every declaration
    a6-decls.py --kind def <file.lean> … only that kind (repeatable)
"""

import importlib.util
import os
import re
import sys

# `lean-decls.py` is not an importable module name (hyphen), so load it by path.
_spec = importlib.util.spec_from_file_location(
    "lean_decls", os.path.join(os.path.dirname(os.path.abspath(__file__)), "lean-decls.py"))
_ld = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_ld)
strip_comments = _ld.strip_comments

KINDS = (
    "axiom", "theorem", "lemma", "def", "abbrev", "instance", "structure",
    "class", "inductive", "opaque", "example",
)

OPENER = re.compile(
    r"^(\s*)(?:(@\[[^\]]*\])\s*)?"
    r"((?:private\s+|protected\s+|nonrec\s+|noncomputable\s+|scoped\s+|partial\s+|unsafe\s+|local\s+)*)"
    r"(" + "|".join(KINDS) + r")(\s+([^\s({\[:]+))?(?=\s|$|:|\(|\{|\[)")
ATTR = re.compile(r"^\s*(@\[[^\]]*\])\s*$")


def decls(path):
    with open(path, encoding="utf-8") as fh:
        lines = strip_comments(fh.read()).split("\n")
    for idx, line in enumerate(lines):
        m = OPENER.match(line)
        if not m:
            continue
        # `class inductive`, `structure`-in-`class` etc.: report the first word.
        kind = m.group(4)
        name = m.group(6) or "_"
        attrs = m.group(2)
        if not attrs and idx > 0:
            a = ATTR.match(lines[idx - 1])
            attrs = a.group(1) if a else None
        yield idx + 1, kind, name, attrs or "-"


def main():
    args = sys.argv[1:]
    wanted = set()
    paths = []
    i = 0
    while i < len(args):
        if args[i] == "--kind":
            wanted.add(args[i + 1])
            i += 2
        else:
            paths.append(args[i])
            i += 1
    if not paths:
        raise SystemExit(__doc__)
    for p in paths:
        for ln, kind, name, attrs in decls(p):
            if wanted and kind not in wanted:
                continue
            print("%s:%d\t%s\t%s\t%s" % (p, ln, kind, name, attrs))


if __name__ == "__main__":
    main()
