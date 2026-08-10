#!/usr/bin/env python3
"""a1-r52-undischarged.py — list the Prop-valued `def`s that no package theorem
concludes unconditionally, i.e. the population round r0052's claim census must
adjudicate.

Usage: a1-r52-undischarged.py <a6-env-scan output>

`a6-summarize.py` prints only the *count* (72) unless a `--claims` file already
exists; the census has to be built before that file can be written, so this
script dumps the population itself: one TSV row per undischarged def with the
raw counters (`binders refs proofs uncond hyps refuted`) and any REFUTEDBY
theorem, so the adjudication reads from data rather than from a grep.
"""

import sys

FIELDS = ("module", "line", "name", "binders", "refs", "proofs",
          "uncond", "hyps", "refuted")


def main():
    path = sys.argv[1]
    pd, refby = [], {}
    with open(path, encoding="utf-8") as fh:
        for line in fh:
            p = line.rstrip("\n").split("\t")
            if p[0] == "PROPDEF":
                d = dict(zip(FIELDS, p[1:]))
                d.setdefault("refuted", "0")
                pd.append(d)
            elif p[0] == "REFUTEDBY":
                refby.setdefault(p[1], []).append(p[2])
    undis = [d for d in pd if d["uncond"] == "0"]
    print("# %d Prop-valued defs total, %d undischarged" % (len(pd), len(undis)))
    print("\t".join(("module", "line", "name", "binders", "refs", "proofs",
                     "hyps", "refuted", "refutedBy")))
    for d in sorted(undis, key=lambda d: (d["module"], int(d["line"]))):
        print("\t".join((d["module"], d["line"], d["name"], d["binders"],
                         d["refs"], d["proofs"], d["hyps"], d["refuted"],
                         ",".join(sorted(refby.get(d["name"], []))) or "-")))


if __name__ == "__main__":
    main()
