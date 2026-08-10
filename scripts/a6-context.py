#!/usr/bin/env python3
"""a6-context.py — attach each `PROPDEF` row from `a6-query.lean`'s output to the
docstring and signature it was declared with, so a Prop-valued definition can be
classified as a *concept* (a predicate the development defines and then uses) or
a *claim* (a proposition standing in for a result of the paper).

The distinction cannot be drawn from the type alone. `IsBifinite α : Prop` and
`Theorem7ArrowRecursive : Prop` have the same shape; the first is a definition
every theorem quantifies over, the second is Theorem 7 written down and left
unproved. What separates them is what the author wrote above it, so this pulls
that text out mechanically instead of leaving it to be eyeballed.

Usage:
    a6-context.py <env-scan-output> <package-root> [--only-undischarged]

`<package-root>` is the directory holding `ScottDomains/` (module
`ScottDomains.A.B` maps to `<package-root>/ScottDomains/A/B.lean`).
`--only-undischarged` keeps the rows whose `uncond` column is 0 — no package
theorem concludes them without itself assuming a proof hypothesis. That is the
right filter and `proofs == 0` is not: `PRep.Lemma28AtU` has three theorems
concluding it and every one of them assumes between two and five hypotheses, so
it is a reduction of Lemma 28, not a proof of it.

Output per row: a `=== file:line name binders=… refs=… proofs=… uncond=… hyps=…`
header, the docstring, and the declaration's signature lines.
"""

import os
import sys


def source_of(root, module):
    return os.path.join(root, module.replace(".", "/") + ".lean")


def docstring_before(lines, idx):
    """Lines of the `/-- … -/` block ending immediately above line `idx` (1-based),
    skipping any attribute lines in between."""
    i = idx - 2                       # 0-based index of the line above
    while i >= 0 and (lines[i].lstrip().startswith("@[") or not lines[i].strip()):
        i -= 1
    if i < 0 or not lines[i].rstrip().endswith("-/"):
        return []
    end = i
    while i >= 0 and "/--" not in lines[i]:
        i -= 1
    return lines[max(i, 0):end + 1] if i >= 0 else []


def signature_after(lines, idx):
    """The declaration's lines from `idx` (1-based) up to and including the one
    ending in `:=`, capped at 12 lines so a long proof term is not dumped."""
    out = []
    for ln in lines[idx - 1:idx + 11]:
        out.append(ln)
        if ln.rstrip().endswith(":="):
            break
    return out


def main():
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    only_undischarged = "--only-undischarged" in sys.argv
    if len(args) != 2:
        raise SystemExit(__doc__)
    scan, root = args
    n = 0
    with open(scan, encoding="utf-8") as fh:
        for row in fh:
            parts = row.rstrip("\n").split("\t")
            if not parts or parts[0] != "PROPDEF":
                continue
            # r0046 added a tenth `refuted` column to PROPDEF; unpack only the
            # nine this script reads so the extra column does not break it.
            _, module, line, name, binders, refs, proofs, uncond, hyps = parts[:9]
            if only_undischarged and uncond != "0":
                continue
            path = source_of(root, module)
            with open(path, encoding="utf-8") as src:
                lines = src.readlines()
            idx = int(line)
            n += 1
            print("=== %s:%s %s binders=%s refs=%s proofs=%s uncond=%s hyps=%s"
                  % (path, line, name, binders, refs, proofs, uncond, hyps))
            for ln in docstring_before(lines, idx):
                print("    " + ln.rstrip())
            for ln in signature_after(lines, idx):
                print("  > " + ln.rstrip())
            print()
    print("rows: %d" % n)


if __name__ == "__main__":
    main()
