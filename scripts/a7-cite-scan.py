#!/usr/bin/env python3
"""a7-cite-scan.py — extract every backticked declaration citation from Lean
comments and from markdown/log/tex prose, with file and line.

Why this exists: r0044 class 4 is "artifacts asserting things that are false".
Seven sites were known and every one was found incidentally. The mechanical half
of the class is a cited declaration name that does not exist — e.g.
`FlatPowerdomain.lean:34` names `smyth_oneBot_eq_bot` and `smyth_bot_eq_bot`,
neither of which is a declaration; the real one is
`smyth_oneBot_eq_bot_eq_unit_bot`. `scripts/r0043-verify-citations.sh` did this
for the five r0043 reports only. This generalizes the extraction half to the
whole tree; `a7-resolve.py` is the matching half.

What counts as a citation. Only a **whole backtick span that is exactly a Lean
identifier**. "`plotkin_le_iff`" is a citation; "`#check @d`" and "`u ⊢♮ v`" are
not, because the span is not an identifier. Taking sub-tokens out of prose
inside backticks was tried and is what makes such a sweep unusable, so it is
deliberately not done. Precision is bought at a known cost in recall, recorded
in the r0044 report.

For `.lean` files only comment text is scanned — `/-- … -/` docstrings, `/-! … -/`
module docs, `/- … -/` blocks and `--` line comments. Code is blanked out first,
so a declaration's own name is never mistaken for a citation of it. The lexer is
the one `lean-decls.py` uses, inverted: it tracks nesting and string literals so
a `"--"` inside a string does not open a comment.

For markdown, fenced code blocks (```) are skipped. They hold Lean source, and
in `plans/` that source is often a *proposed* statement naming declarations that
intentionally do not exist yet. Scanning them would report intent as defect.
This is a deliberate recall limit, reported as such.

Usage:
    a7-cite-scan.py <file> …        emits "path<TAB>line<TAB>kind<TAB>name"

`kind` is one of: lean-doc (a `/-- … -/` or `/-! … -/` docstring — documentation
of live code, the most severe site), lean-comment (a `/- … -/` block or `--`
line comment), prose (markdown/log/tex outside a code fence).
"""

import re
import sys

# Lean identifier: ASCII letters/digits/_/'/./!/?, plus the subscript digits and
# Greek letters that appear in this development's names (e.g. `f₀`, `ε_lemma`).
IDENT = re.compile(
    "\\A[A-Za-z_\u03b1-\u03c9\u0391-\u03a9]"
    "[A-Za-z0-9_.'!?\u2080-\u2089\u03b1-\u03c9\u0391-\u03a9]*\\Z"
)

# A backtick span: one or more backticks, content without backticks, closing run.
SPAN = re.compile(r"`+([^`\n]+)`+")

# Tokens that look like identifiers but name a file, not a declaration.
FILE_EXT = re.compile(r"\.(lean|md|sh|py|log|tex|pdf|json|toml|olean|txt|yml|yaml)\Z")


def comment_mask(text):
    """Return `text` with every non-comment character replaced by a space and
    comment text kept, preserving line structure so line numbers stay exact.

    Returns (masked_text, doc_flags) where doc_flags[i] is True when line i sits
    inside a `/-- … -/` or `/-! … -/` docstring rather than a plain comment.
    This is `lean-decls.py`'s strip_comments run the other way round.
    """
    out = []
    depth = 0
    i, n = 0, len(text)
    in_str = False
    in_line_comment = False
    # Track, per character emitted, whether we are inside a doc-style block.
    doc_depth = 0  # depth at which the current doc block opened, 0 = not in one
    doc_flag_chars = []

    def emit(ch, isdoc):
        out.append(ch)
        doc_flag_chars.append(isdoc)

    while i < n:
        ch = text[i]
        nxt = text[i + 1] if i + 1 < n else ""
        nxt2 = text[i + 2] if i + 2 < n else ""

        if depth == 0 and not in_str and ch == '"':
            in_str = True
            emit(" ", False)
            i += 1
            continue
        if in_str:
            if ch == "\\" and nxt:
                emit(" ", False)
                emit(" ", False)
                i += 2
                continue
            if ch == '"':
                in_str = False
            emit(" " if ch != "\n" else "\n", False)
            i += 1
            continue

        if ch == "/" and nxt == "-":
            depth += 1
            if depth == 1 and nxt2 in ("-", "!"):
                doc_depth = 1
            emit(" ", False)
            emit(" ", False)
            i += 2
            continue
        if ch == "-" and nxt == "/" and depth > 0:
            depth -= 1
            emit(" ", False)
            emit(" ", False)
            i += 2
            if depth == 0:
                doc_depth = 0
            continue
        if depth == 0 and ch == "-" and nxt == "-":
            # `--` line comment: keep its text, stop at newline.
            while i < n and text[i] != "\n":
                emit(text[i], False)
                i += 1
            continue

        if depth > 0:
            emit(ch, doc_depth > 0)
        else:
            emit(" " if ch != "\n" else "\n", False)
        i += 1

    masked = "".join(out)
    # Reduce per-character doc flags to per-line: a line is "doc" if any kept
    # character on it belongs to a doc block.
    doc_lines = []
    cur = False
    for ch, isdoc in zip(out, doc_flag_chars):
        if ch == "\n":
            doc_lines.append(cur)
            cur = False
        else:
            cur = cur or isdoc
    doc_lines.append(cur)
    return masked, doc_lines


def spans(line):
    """Yield each backtick span's content that is exactly a Lean identifier."""
    for m in SPAN.finditer(line):
        tok = m.group(1).strip()
        if not IDENT.match(tok):
            continue
        if FILE_EXT.search(tok):
            continue
        yield tok


def scan_lean(path):
    with open(path, encoding="utf-8", errors="replace") as fh:
        raw = fh.read()
    masked, doc_lines = comment_mask(raw)
    lines = masked.split("\n")
    for idx, line in enumerate(lines):
        if "`" not in line:
            continue
        isdoc = doc_lines[idx] if idx < len(doc_lines) else False
        # A `--` line comment is never a docstring; comment_mask flags only
        # block-doc text, so this is already correct.
        kind = "lean-doc" if isdoc else "lean-comment"
        window = " ".join(lines[max(0, idx - 1):idx + 2])
        for tok in spans(line):
            yield idx + 1, kind, tok, line, window


def scan_prose(path):
    fence = False
    with open(path, encoding="utf-8", errors="replace") as fh:
        lines = fh.read().split("\n")
    for idx, line in enumerate(lines):
        stripped = line.lstrip()
        if stripped.startswith("```") or stripped.startswith("~~~"):
            fence = not fence
            continue
        if fence:
            continue
        if "`" not in line:
            continue
        window = " ".join(lines[max(0, idx - 1):idx + 2])
        for tok in spans(line):
            yield idx + 1, "prose", tok, line, window


def main():
    if len(sys.argv) < 2:
        raise SystemExit(__doc__)
    for path in sys.argv[1:]:
        gen = scan_lean if path.endswith(".lean") else scan_prose
        try:
            for ln, kind, tok, ctx, window in gen(path):
                # Two context fields travel with each citation: the containing
                # LINE, for quoting as evidence, and a three-line WINDOW, for
                # testing whether the sentence asserts the name is absent. The
                # window is needed because these docstrings wrap a sentence
                # across lines — "were retired" and "returned zero hits" both
                # landed on the line after their citation, and a line-only test
                # scored them as defects.
                print("%s\t%d\t%s\t%s\t%s\t%s"
                      % (path, ln, kind, tok,
                         ctx.replace("\t", " ").strip(),
                         window.replace("\t", " ").strip()))
        except (OSError, UnicodeError) as exc:
            print("a7-cite-scan: %s: %s" % (path, exc), file=sys.stderr)


if __name__ == "__main__":
    main()
