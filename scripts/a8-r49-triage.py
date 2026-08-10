#!/usr/bin/env python3
"""a8-r49-triage.py — r0049 / agent8, Goal B: partition the necessity /
impossibility / absence / uniqueness sweep residue by WHAT WOULD DECIDE EACH
SITE, so the round's adjudication effort goes where an instrument exists.

--------------------------------------------------------------------------------
Why a triage and not another sweep
--------------------------------------------------------------------------------
r0046's `a5-r46-sweep.sh` produced 228 candidate sites and adjudicated 24,
leaving 183 undecided plus Class U. Re-running the sweep (measured here: 264
candidates, the corpus having grown by r0047 and r0048 prose) does not move that
number, because the sweep is a *recall* instrument: it emits every sentence
matching an English cue, and a large fraction of those sentences are not
standing claims about the environment at all. The binding constraint is not
finding more candidates; it is knowing which candidate is decidable by which
probe.

Four disjoint tiers, assigned by a test on the sentence, not on its meaning:

  ADJ    already carries a verdict in r0046's ledger. Subtracted, never
         recounted — r0046 measured that correcting a false claim leaves the
         site still matching the grep, because the correction protocol requires
         quoting the sentence being corrected (230 candidates before four
         corrections, 231 after). Raw candidate count is not a progress metric.

  QUOTE  the sentence is the PAPER's, reproduced behind a `>` blockquote marker.
         Gunter & Scott wrote it; it is not a claim this development makes, and
         convicting it is the error the round's evidence rules name ("check the
         paper before convicting it" — three suspicions already traced to our
         own transcription).

  CITE   the sentence's subject is a backticked name. Decidable with no human
         judgement at all: the name either is a constant in the elaborated
         environment or is not. This is the tier `a8-r49-cites.sh` decides, and
         the join is done here.

  SCOPE  Class U — "the only place `X` is spent", "nothing else uses `Y`". The
         subject resolves; the QUANTIFIER is what is unchecked, and its domain
         is a file or a proof that the sentence does not name. r0046's agent5
         refused to convict `JungBicomplete.lean:506` on exactly these grounds
         after measuring 11 users against a claimed 1. No instrument decides
         these; `docs/ScopedClaims.md` is the deliverable instead.

  NARR   no backticked subject anywhere in the line: a statement about the proof
         script as written ("no case split on directedness is needed here").
         The elaboration of the file IS the check — the proof compiles without
         the case split — so the sentence is self-verifying and carries no
         standing obligation. Reported, not adjudicated.

Precision is not claimed for the tiers. Each is a lexical test whose predicate
is stated above; the report gives the counts and the hand-check sample.

--------------------------------------------------------------------------------
Usage
--------------------------------------------------------------------------------
    a8-r49-triage.py <sweep.txt> <r46-ledger.tsv> <unresolved.tsv> <out.tsv>

Work: O(|sites| * |citation rows|) with the citation rows indexed by site;
span: one pass.
"""

import re
import sys
from collections import defaultdict

# A backticked span holding something identifier-shaped. Deliberately looser
# than a7-resolve.py's `plausible()`: here the question is only "does this
# sentence HAVE a name-shaped subject", not "is that name a declaration".
BACKTICK = re.compile(r"`([^`]+)`")
NAMEISH = re.compile(r"^[A-Za-z_][A-Za-z0-9_.'!?₀-₉]*$")


def has_name_subject(text):
    for span in BACKTICK.findall(text):
        s = span.strip()
        if NAMEISH.match(s) and (len(s) >= 4 or "." in s or "_" in s):
            return True
    return False


def is_quote(text):
    return text.lstrip().startswith(">")


def main():
    if len(sys.argv) != 5:
        raise SystemExit(__doc__)
    sweep_path, ledger_path, unres_path, out_path = sys.argv[1:5]

    # r0046's verdicts, keyed by "path:line".
    adjudicated = {}
    with open(ledger_path, encoding="utf-8") as fh:
        for line in fh:
            if line.startswith("#") or not line.strip():
                continue
            cols = line.rstrip("\n").split("\t")
            if len(cols) >= 2:
                adjudicated[cols[0]] = cols[1]

    # Citation verdicts, keyed by "path:line" with the worktree prefix stripped
    # so both files use the repo-relative form the sweep emits.
    cite = defaultdict(list)
    with open(unres_path, encoding="utf-8") as fh:
        for line in fh:
            cols = line.rstrip("\n").split("\t")
            if len(cols) < 5:
                continue
            path, lineno, _kind, name, tier = cols[:5]
            idx = path.find("/ScottDomains/ScottDomains/")
            if idx >= 0:
                path = path[idx + 1:]
            cite["%s:%s" % (path, lineno)].append((name, tier))

    rows = []
    with open(sweep_path, encoding="utf-8") as fh:
        for line in fh:
            cols = line.rstrip("\n").split("\t")
            if len(cols) < 3:
                continue
            cls, site, text = cols[0], cols[1], "\t".join(cols[2:])
            if site in adjudicated:
                rows.append((cls, site, "ADJ", adjudicated[site], text))
            elif is_quote(text):
                rows.append((cls, site, "QUOTE", "", text))
            elif site in cite:
                names = ";".join("%s=%s" % (n, t) for n, t in cite[site])
                rows.append((cls, site, "CITE", names, text))
            elif cls == "U":
                rows.append((cls, site, "SCOPE", "", text))
            elif has_name_subject(text):
                rows.append((cls, site, "CITE-OK", "", text))
            else:
                rows.append((cls, site, "NARR", "", text))

    with open(out_path, "w", encoding="utf-8") as out:
        out.write("# a8-r49-triage.py — r0049/agent8. class, site, tier, note, text\n")
        for r in rows:
            out.write("\t".join(r) + "\n")

    tally = defaultdict(int)
    for cls, _site, tier, _note, _text in rows:
        tally[tier] += 1
        tally["%s/%s" % (cls, tier)] += 1
    print("sites: %d" % len(rows))
    for tier in ("ADJ", "QUOTE", "CITE", "CITE-OK", "SCOPE", "NARR"):
        print("  %-8s %4d" % (tier, tally[tier]))
    print("by class:")
    for cls in ("N", "I", "A", "U"):
        parts = " ".join(
            "%s=%d" % (t, tally["%s/%s" % (cls, t)])
            for t in ("ADJ", "QUOTE", "CITE", "CITE-OK", "SCOPE", "NARR")
            if tally["%s/%s" % (cls, t)])
        print("  %s: %s" % (cls, parts))
    print("wrote %s" % out_path)


if __name__ == "__main__":
    main()
