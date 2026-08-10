#!/usr/bin/env python3
"""a8-doc-claims.py — r0044 Class 4 (reading half), agent8.

Pairs every declaration docstring (`/-- … -/`) in the package with the
signature of the declaration it documents, so the CLAIM in the prose can be
compared against the TYPE the kernel elaborated.  A docstring that promises a
conjunct, a uniqueness clause, a hypothesis-free statement or a biconditional
that the signature does not carry is the defect this round is looking for; the
known instance is `smyth_natBot_orderIso`, whose docstring promises "carries
every directed supremum" and whose statement is a bare `≃o` plus a pointwise
equation.

This is a *discovery aid only*.  Every hit it reports is confirmed by reading
the file and by `#check @d` against the built `.olean`, never from this output.

Usage:
    scripts/a8-doc-claims.py <regex> [outfile]

The regex is matched case-insensitively against the docstring text.  Output is
one record per hit:

    <path>:<docstring-start-line>
    DOC  <docstring text>
    SIG  <declaration signature, up to := / where / by>
"""
import os
import re
import sys

ROOT = "/home/milnes/projects/ScottLean4-agent8/ScottDomains"
DECL = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+|scoped\s+)*"
    r"(theorem|lemma|def|abbrev|instance|structure|class|inductive)\b")


def records(path):
    """Yield (line_no, doc_text, signature) for each /-- … -/ in `path`."""
    with open(path, encoding="utf-8") as fh:
        lines = fh.readlines()
    i, n = 0, len(lines)
    while i < n:
        s = lines[i]
        if s.lstrip().startswith("/--"):
            start = i
            buf = []
            while i < n:
                buf.append(lines[i].rstrip("\n"))
                if "-/" in lines[i] and not (i == start and lines[i].lstrip() == "/--"):
                    break
                i += 1
            doc = "\n".join(buf)
            doc = re.sub(r"^\s*/--", "", doc)
            doc = re.sub(r"-/\s*$", "", doc.rstrip())
            # signature: from the next declaration line to := / where / by
            j = i + 1
            sig = []
            while j < n and j < i + 40:
                t = lines[j].rstrip("\n")
                if not sig and not t.strip():
                    j += 1
                    continue
                if not sig and not DECL.match(t):
                    break
                sig.append(t)
                if re.search(r":=|\bwhere\b|\bby\b$", t):
                    break
                j += 1
            yield start + 1, doc.strip(), "\n".join(sig)
        i += 1


def main():
    if len(sys.argv) < 2:
        sys.exit(__doc__)
    pat = re.compile(sys.argv[1], re.IGNORECASE | re.DOTALL)
    out = open(sys.argv[2], "w", encoding="utf-8") if len(sys.argv) > 2 else sys.stdout
    hits = 0
    for dirpath, _, names in os.walk(os.path.join(ROOT, "ScottDomains")):
        if ".lake" in dirpath:
            continue
        for name in sorted(names):
            if not name.endswith(".lean"):
                continue
            path = os.path.join(dirpath, name)
            for ln, doc, sig in records(path):
                if not sig:
                    continue
                if pat.search(doc):
                    hits += 1
                    print(f"\n=== {path}:{ln}", file=out)
                    print("DOC  " + doc.replace("\n", "\n     "), file=out)
                    print("SIG  " + sig.replace("\n", "\n     "), file=out)
    print(f"\n# hits: {hits}", file=out)
    if out is not sys.stdout:
        out.close()


if __name__ == "__main__":
    main()
