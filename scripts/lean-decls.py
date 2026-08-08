#!/usr/bin/env python3
"""lean-decls.py — count theorem-ish declarations in Lean sources, correctly.

Round r0038's audit found three independent defects in the grep rule that
`counts.sh` and `module-counts.sh` used, `^(@\\[…\\] )?(theorem|lemma) `:

  1. declarations inside `/- … -/` block comments were counted — r0020
     commented out five speculative declarations in place, and all five were
     still being counted, including both `@[simp]` ones attributed to
     `ScottHom.lean`  (found by agent1 and agent2);
  2. docstring prose lines beginning "theorem"/"lemma" at column 0 were counted
     — at least eight, e.g. "lemma graded by ℕ …"  (agent3, agent5, agent6);
  3. `protected theorem` was missed — `IdealCompletion` under-reported by four
     (agent4).

Net, the 1308 headline was wrong in both directions. This fixes all three by
lexing away comments before matching, and by widening the modifier set.

**What this is and is not.** It is a lexer, not a parser: it tracks nested
`/- … -/` and `--` comments and string literals, then matches declaration
openers. That is enough to be right about comments, which is what the three
defects were. It is *not* an authority on what the kernel accepts — the
authoritative count is the Lean environment itself, enumerated after
elaboration. Where a number is load-bearing, get it from `#print axioms` or an
environment dump, not from here. This exists so that a size metric quoted in
docs and reports is at least not counting prose.

Usage:
    lean-decls.py --count <file.lean> …      total across the files
    lean-decls.py --per-file <file.lean> …   "<count>\\t<path>" per file
    lean-decls.py --list <file.lean> …       "<path>:<line>\\t<name>" per decl
    lean-decls.py --simp <file.lean> …       count only @[simp]-tagged ones
"""

import re
import sys

# `theorem` and `lemma` only — the metric counts proofs, not definitions.
OPENER = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)*"
    r"(?:private\s+|protected\s+|nonrec\s+|noncomputable\s+|scoped\s+)*"
    r"(theorem|lemma)\s+([^\s({\[:]+)")
SIMP = re.compile(r"^\s*@\[[^\]]*\bsimp\b[^\]]*\]")


def strip_comments(text):
    """Blank out `--` line comments and nested `/- … -/` blocks, preserving
    line structure so line numbers stay meaningful. String literals are honoured
    so a `"--"` inside a string does not start a comment."""
    out = []
    depth = 0
    i, n = 0, len(text)
    in_str = False
    while i < n:
        ch = text[i]
        nxt = text[i + 1] if i + 1 < n else ""
        if depth == 0 and not in_str and ch == '"':
            in_str = True
            out.append(ch)
            i += 1
            continue
        if in_str:
            if ch == "\\" and nxt:
                out.append("  ")
                i += 2
                continue
            if ch == '"':
                in_str = False
            out.append(ch)
            i += 1
            continue
        if ch == "/" and nxt == "-":
            depth += 1
            out.append("  ")
            i += 2
            continue
        if ch == "-" and nxt == "/" and depth > 0:
            depth -= 1
            out.append("  ")
            i += 2
            continue
        if depth == 0 and ch == "-" and nxt == "-":
            while i < n and text[i] != "\n":
                out.append(" ")
                i += 1
            continue
        out.append(" " if depth > 0 and ch != "\n" else ch)
        i += 1
    return "".join(out)


def decls(path):
    """Yield (line-number, name, is_simp) for each declaration in the file."""
    with open(path, encoding="utf-8") as fh:
        raw = fh.read()
    lines = strip_comments(raw).split("\n")
    for idx, line in enumerate(lines):
        m = OPENER.match(line)
        if not m:
            continue
        # An attribute group may sit on the preceding line.
        tagged = bool(SIMP.match(line))
        if not tagged and idx > 0:
            tagged = bool(SIMP.match(lines[idx - 1]))
        yield idx + 1, m.group(2), tagged


def main():
    if len(sys.argv) < 3:
        raise SystemExit(__doc__)
    mode, paths = sys.argv[1], sys.argv[2:]
    total = 0
    for p in paths:
        found = list(decls(p))
        if mode == "--per-file":
            print("%d\t%s" % (len(found), p))
        elif mode == "--list":
            for ln, name, _ in found:
                print("%s:%d\t%s" % (p, ln, name))
        elif mode == "--simp":
            total += sum(1 for _, _, t in found if t)
        else:
            total += len(found)
    if mode in ("--count", "--simp"):
        print(total)


if __name__ == "__main__":
    main()
