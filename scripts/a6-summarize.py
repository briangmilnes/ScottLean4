#!/usr/bin/env python3
"""a6-summarize.py — turn `a6-query.lean`'s raw records into the tallies round
r0044's Class-3 stream reports, so every number in the report is reproduced by
one command rather than read off a grep.

Usage:
    a6-summarize.py <env-scan-output> [--claims <file>]

`--claims` names a file of fully-qualified declaration names, one per line
(blank lines and `#` comments ignored): the Prop-valued definitions judged to be
*claims* — a result of the paper written down — rather than *concepts* — a
predicate the development defines in order to quantify over it. That judgement
is made by reading the docstring (`a6-context.py` prints them) and is recorded
as data, not buried in prose.

Sections printed:
    1  axiom census
    2  sorryAx census
    3  Prop-valued defs: total, undischarged, claims split into open vs refuted
    4  Prop-valued defs with no consumer at all
    5  structures never instantiated
    6  simp lemmas no proof term names

Section 3's split is r0046's correction (agent1). The undischarged test is
`uncond == 0` — "no package theorem concludes this with no proof hypothesis" —
and a *refutation* concludes `¬ D`, whose head is `Not`, so it never increments
`uncond`. Under the old reading a claim stayed on the open list forever once
somebody proved it false, which is the opposite of the truth. `a6-query.lean`
now emits REFUTEDBY records for closed refutations (its docstring states the
criterion and why it is sound), and this script reports

    claims: N named, R refuted (resolved), N-R open

with the refuting theorem named for each. **Goal A is the open count**, not the
named count.
"""

import sys


def load(path):
    rows = {"PROPDEF": [], "AXIOM": [], "SORRYUSER": [], "STRUCT": [],
            "SIMP": [], "PROVEDBY": [], "REFUTEDBY": [], "TOTALS": []}
    with open(path, encoding="utf-8") as fh:
        for line in fh:
            parts = line.rstrip("\n").split("\t")
            if parts and parts[0] in rows:
                rows[parts[0]].append(parts[1:])
    return rows


def main():
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    claims = set()
    if "--claims" in sys.argv:
        with open(sys.argv[sys.argv.index("--claims") + 1], encoding="utf-8") as fh:
            for line in fh:
                s = line.split("#")[0].strip()
                if s:
                    claims.add(s)
    r = load(args[0])

    print("1  axiom declarations in package modules: %d" % len(r["AXIOM"]))
    for a in r["AXIOM"]:
        print("     %s:%s %s" % (a[0], a[1], a[2]))
    print("2  package constants naming sorryAx:      %d" % len(r["SORRYUSER"]))

    pd = [dict(zip(("module", "line", "name", "binders", "refs", "proofs",
                    "uncond", "hyps", "refuted"), p)) for p in r["PROPDEF"]]
    for d in pd:
        d.setdefault("refuted", "0")
    refby = {}
    for c, t in r["REFUTEDBY"]:
        refby.setdefault(c, []).append(t)
    undis = [d for d in pd if d["uncond"] == "0"]
    print("3  Prop-valued defs: %d total, %d with no unconditional proof"
          % (len(pd), len(undis)))
    if claims:
        cl = [d for d in undis if d["name"] in claims]
        co = [d for d in undis if d["name"] not in claims]
        ref = [d for d in cl if d["refuted"] != "0"]
        opn = [d for d in cl if d["refuted"] == "0"]
        print("     claims:   %d named, %d refuted (resolved), %d OPEN  <- Goal A"
              % (len(cl), len(ref), len(opn)))
        print("     concepts: %d" % len(co))
        stray = claims - {d["name"] for d in undis}
        if stray:
            print("     !! named as claims but NOT undischarged: %s" % sorted(stray))
        for d in sorted(opn, key=lambda d: (d["module"], int(d["line"]))):
            print("     open     %s:%s\t%s\tbinders=%s refs=%s proofs=%s hyps=%s"
                  % (d["module"], d["line"], d["name"], d["binders"], d["refs"],
                     d["proofs"], d["hyps"]))
        for d in sorted(ref, key=lambda d: (d["module"], int(d["line"]))):
            print("     refuted  %s:%s\t%s\tby %s"
                  % (d["module"], d["line"], d["name"],
                     ", ".join(sorted(refby.get(d["name"], [])))))
        # The count above can also be too LOW. `uncond` scores any zero-
        # proof-hypothesis theorem headed by the claim as a discharge, including
        # one that fills a parameter slot with a particular value or with
        # another binder — r0044's dominant defect mode. PROVEDBY's `generic`
        # field measures it; a claim counted resolved whose every unconditional
        # proof is non-generic is discharged AT an instance, not discharged.
        undis_names = {d["name"] for d in undis}
        atinst = []
        for name in sorted(claims - undis_names):
            rows = [p for p in r["PROVEDBY"] if p[0] == name]
            unc = [p for p in rows if len(p) > 2 and p[2] == "0"]
            if unc and all(len(p) > 3 and p[3] == "false" for p in unc):
                atinst.append((name, [p[1] for p in unc]))
        print("     !! counted resolved but every unconditional proof is at a "
              "parameter instance: %d" % len(atinst))
        for name, ts in atinst:
            print("        %s\tby %s" % (name, ", ".join(sorted(ts))))

    noref = [d for d in pd if d["refs"] == "0"]
    nouse = [d for d in pd if d["proofs"] == "0" and d["hyps"] == "0"]
    print("4  Prop-valued defs never mentioned by any other constant: %d" % len(noref))
    for d in sorted(noref, key=lambda d: d["name"]):
        print("     %s:%s\t%s" % (d["module"], d["line"], d["name"]))
    print("   Prop-valued defs never concluded and never a hypothesis: %d" % len(nouse))
    for d in sorted(nouse, key=lambda d: (d["module"], int(d["line"]))):
        print("     %s:%s\t%s\trefs=%s" % (d["module"], d["line"], d["name"], d["refs"]))

    st = [dict(zip(("module", "line", "name", "ctorRefs", "fields", "propFields"), p))
          for p in r["STRUCT"]]
    dead = [s for s in st if s["ctorRefs"] == "0"]
    print("5  structures/classes: %d total, %d never instantiated" % (len(st), len(dead)))
    for s in dead:
        print("     %s:%s\t%s\tfields=%s propFields=%s"
              % (s["module"], s["line"], s["name"], s["fields"], s["propFields"]))

    sp = [dict(zip(("module", "line", "name", "refs", "rfl"), p)) for p in r["SIMP"]]
    z = [s for s in sp if s["refs"] == "0"]
    zn = [s for s in z if s["rfl"] == "false"]
    zr = [s for s in z if s["rfl"] == "true"]
    print("6  simp-tagged declarations: %d total, %d named by no proof term"
          % (len(sp), len(z)))
    print("     of those, %d are not rfl-theorems — they cannot have fired" % len(zn))
    print("     of those, %d are rfl-theorems — inconclusive (dsimp leaves no term)"
          % len(zr))
    for s in sorted(zn, key=lambda s: (s["module"], int(s["line"]))):
        print("     %s:%s\t%s" % (s["module"], s["line"], s["name"]))
    for t in r["TOTALS"]:
        print("   TOTALS constants=%s source=%s defs=%s theorems=%s propDefs=%s simp=%s"
              % tuple(t))


if __name__ == "__main__":
    main()
