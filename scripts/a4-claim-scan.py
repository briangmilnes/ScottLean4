#!/usr/bin/env python3
"""a4-claim-scan.py — r0046 Goal B (agent4): the sweep for PROSE THAT CLAIMS A
PROOF EXISTS, checked against the elaborated environment.

The `sorry` count has been 0 for three rounds, so the binding constraint on this
development is no longer the kernel's proof obligations — it is the sentences
around them, which nothing checks. Four such sentences were confirmed false
before this instrument existed, and every one was found by accident.

--------------------------------------------------------------------------------
What is checked
--------------------------------------------------------------------------------
A sentence in a `.lean` comment is a CLAIM UNIT. Its polarity comes from a cue
list; its SUBJECT is the backticked names in it. Four detectors, each of which
is a question about the environment and not about any source line:

  P1  proved-but-nothing-concludes
      The sentence asserts a proof exists ("is proved", "we prove", "follows
      from", "is immediate", "is established", "is checked", "is carried out
      below", "done in") and names a Prop-valued package `def` S, but NO package
      theorem's type, after stripping every binder, is headed by S.
      This is Goal A's discharge test read backwards: the `def` is undischarged,
      and the prose says otherwise.

  P2  open-but-something-concludes
      The sentence asserts the opposite — S "is open", "is unproved", "nothing
      proves" it, it "is refutable" — while the environment DOES contain a
      hypothesis-free theorem concluding S (or, for a refutability claim, does
      NOT contain one concluding `Not S`).

  P3  absent-but-the-same-module-declares-it
      The sentence asserts a name or a class instance does not exist ("does not
      exist", "there is no", "no `X`", "returned zero hits", "is not among
      them"), and the SAME MODULE declares something matching it.
      Restricted to the declaring module on purpose: the plan's four confirmed
      true positives are four-for-four intra-file, and a tree-wide test turns
      every true statement about Mathlib's contents into a false hit.

  P4  count-claim
      The sentence quantifies proved items ("the only two", "seven of the nine",
      "both of the") while naming declarations that share a conclusion head. The
      environment's count of hypothesis-free theorems with that conclusion head
      is reported next to the stated numeral, for the reader to compare. This is
      the only detector whose output is a MEASUREMENT rather than a verdict,
      because "Lemma 28's nine schemes" is a fact about the paper, not about the
      environment.

--------------------------------------------------------------------------------
Why the environment and not grep
--------------------------------------------------------------------------------
"Is S proved?" is not a lexical question. `LemThirty.Thm29Normal` is a
Prop-valued `def`; whether anything proves it is whether some theorem's
CONCLUSION is headed by that constant after binder stripping, which depends on
elaboration, on instance binders and on definitional unfolding. `a4-decl-query.lean`
produces that index; this file consumes it.

--------------------------------------------------------------------------------
Precision, not recall
--------------------------------------------------------------------------------
Every filter here is deliberately conservative and its cost is reported as a
number. A sweep whose output must itself be audited to be believed is not an
instrument. Every row this emits is hand-checked against the built `.olean`
before it appears in the round's report; the measured precision is stated there.

The comment lexer is imported from `a7-cite-scan.py` (r0044, agent7) rather than
rewritten: it already tracks nesting, string literals and doc-vs-plain comments,
and a second lexer would be a second thing to trust.

Usage:
    a4-claim-scan.py <a4-decls.tsv> <lake-root> <out.tsv>
        lake-root is .../ScottLean4-agentN/ScottDomains — the LAKE PACKAGE root,
        the directory holding both `lakefile.toml` and the module tree
        `ScottDomains/`. It has to be that one and not the module tree itself:
        the environment's module names are `ScottDomains.PRepFun`, and only a
        path relative to the lake root reproduces the leading component. Getting
        this wrong makes every module lookup miss silently, which disables the
        intra-file detector P3 without any error — measured, it took P3 from 5
        hits to 0.
"""

import importlib.util
import os
import re
import sys
from collections import defaultdict

HERE = os.path.dirname(os.path.abspath(__file__))

# --- reuse a7's comment lexer -------------------------------------------------
_spec = importlib.util.spec_from_file_location(
    "a7_cite_scan", os.path.join(HERE, "a7-cite-scan.py"))
_a7 = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_a7)
comment_mask = _a7.comment_mask
IDENT = _a7.IDENT
SPAN = _a7.SPAN

# --- cue lists ----------------------------------------------------------------
# A cue is a phrase whose truth is a fact about the environment. Phrases that
# describe INTENT ("we will prove", "should follow", "the plan is to") are
# excluded: they make no claim about the present state and flagging them was
# measured to be the largest false-positive source in the first pass.
PROVED_CUES = [
    "is proved", "are proved", "was proved", "were proved", "already proved",
    "is proven", "are proven",
    "we prove", "this proves", "which proves", "proves it",
    "is discharged", "are discharged", "discharges it",
    "is established", "are established",
    "is immediate", "are immediate",
    "follows from", "follows by", "follows immediately", "follows at once",
    "is checked", "are checked",
    "is carried out below", "is carried out above",
    "shown above", "shown below",
    "proved below", "proved above", "proved in", "done in",
    "is complete", "are complete",
    "the kernel accepts", "is formally verified",
]

# The negative polarity: the sentence says no proof exists, or that the thing
# named is absent. Split in two because P2 and P3 ask different questions.
OPEN_CUES = [
    "is open", "remains open", "is unproved", "is not proved", "is undischarged",
    "nothing proves", "no theorem proves", "is still open", "stays open",
    "is refutable", "is refuted", "has no proof", "is not discharged",
]
# Absence cues come in two grammatical shapes and the SUBJECT sits on opposite
# sides of each, so they are kept apart. Attribution by side is what makes this
# detector usable: a cue anywhere in a 300-character sentence matches some
# backticked name almost always, and the first pass returned 26 rows of which 21
# named a token that was not the cue's subject at all.
#   POST  the cue is followed by its subject:  "there is no `Foo`"
#   PRE   the cue follows its subject:         "`Foo` does not exist"
ABSENT_POST = [
    "there is no", "there are no", "has no", "have no", "had no",
    "contains no", "the package contains no", "no occurrences of",
    "we have no", "supplies no", "declares no",
]
ABSENT_PRE = [
    "does not exist", "do not exist", "doesn't exist",
    "is not among", "are not among", "returned zero hits", "returned no hits",
    "returns zero hits", "returned nothing", "is not available",
    "does not have", "do not have", "we do not have", "is nowhere declared",
]
# PAST TENSE IS NOT A CLAIM. "`r ⊗ s` did not exist … `smashMap` below is it" is
# a correct record of what the module was written to supply, and flagging it
# would be flagging the fix rather than the defect. Present tense is what asserts
# the current state, so only present-tense cues are detectors and past-tense
# forms are an explicit hedge. This is also how a corrected sentence is written,
# per the round's rule against deleting the historical record.
PAST_TENSE = [
    "did not exist", "did not have", "was absent", "were absent", "was not",
    "were not", "had no", "was no", "were no", "was missing", "used to",
    "was not present", "was also absent", "before this", "until",
]
# A claim about an EXTERNAL library cannot be refuted by a package declaration.
# `Universality.lean:85` says "Mathlib has no `OrderIso.prodCongr`"; the package
# declares its own `Universality.Iso.prodCongr`, which does not bear on the
# claim at all — and r0044 checked this exact sentence and found the Mathlib
# name genuinely absent. Without this guard it is a false positive.
EXTERNAL = ["mathlib", "core", "std", "batteries", "the standard library",
            "upstream", "lean 4 core"]
# Cues deliberately EXCLUDED, each measured to produce only false positives on
# the first pass: "is missing" (a markdown table header, "what is missing"),
# "nothing in" ("nothing in the development cites this"), "supplies only",
# "no functorial". They describe the surrounding argument, not the presence of
# the name nearest them.

# A numeral-bearing claim about how many things are proved.
COUNT_RE = re.compile(
    r"\b(?:the\s+)?(only\s+)?(one|two|three|four|five|six|seven|eight|nine|ten|"
    r"both|\d+)\s+(?:of\s+(?:the\s+)?(\w+)\s+)?", re.IGNORECASE)
NUMWORD = {"one": 1, "two": 2, "three": 3, "four": 4, "five": 5, "six": 6,
           "seven": 7, "eight": 8, "nine": 9, "ten": 10, "both": 2}

# Speculative / hypothetical framings. A sentence carrying one of these is not
# asserting the present state and is dropped before any detector runs. Each was
# added because it produced a measured false positive on the first pass.
HEDGES = [
    "would", "will ", "could", "should", "if ", "were it", "suppose",
    "plan is", "intend", "next round", "to be proved", "yet to",
    "conjectur", "we expect", "hope", "may be", "might", "once ",
]

# REPORTED SPEECH. A sentence that quotes or attributes a claim is describing
# somebody else's assertion, not making one, and correcting it would be wrong —
# it is precisely the historical record the round is told to preserve. Three of
# the first pass's 40 rows were a later round CORRECTING the very sentence the
# sweep was looking for, quoted verbatim.
REPORTED = [
    "asserts", "claims", "claimed", "listed", "recorded", "records",
    "the docstring", "docstring says", "said", "reads", "wrote", "quoted",
    "correction applies", "reported", "measured this",
]
# A round identifier anywhere in the sentence marks it as a dated record:
# "r0040 measured this sentence as N" was TRUE of r0040 and stays true however
# the tree changes afterwards.
ROUND_RE = re.compile(r"\br0\d{3}\b")
# A cue occurring inside quotation marks is quoted, not asserted.
QUOTE_RE = re.compile(r"[\"“”‘’]")


def word_cue(sent_low, cue):
    """Find `cue` on word boundaries, returning its (start, end) or None.

    Substring matching is not sound for these cues and cost measured precision:
    "has no" matched inside "has non-empty intersection", and "there is no"
    matched inside "there is none". Both produced defect rows for sentences that
    say the opposite of what the cue means.
    """
    m = re.search(r"\b" + re.escape(cue) + r"\b", sent_low)
    return m.span() if m else None


def quoted_regions(sent):
    """Character ranges lying between paired quotation marks."""
    marks = [m.start() for m in QUOTE_RE.finditer(sent)]
    return list(zip(marks[0::2], marks[1::2]))


def in_quotes(sent, pos):
    return any(a <= pos <= b for a, b in quoted_regions(sent))


def spans_with_pos(sent):
    """Every backtick span, with its character range: (start, end, content)."""
    return [(m.start(), m.end(), m.group(1).strip())
            for m in SPAN.finditer(sent)]


def subject_shaped(tok):
    """Can this span be the subject of a status claim?

    Either a Lean identifier, or a class applied to a construction whose head is
    an uppercase identifier (`Domain (D ⊗ E)`). An instance binder written in
    brackets (`[Domain E]`) is neither: it is a qualification ON the subject.
    """
    if IDENT.match(tok):
        return True
    first = re.split(r"[\s(\[]", tok, 1)[0]
    return bool(first and IDENT.match(first) and first[0].isupper())


def subject_before(sent, cue_start, limit=8):
    """The nearest preceding backtick span that can be a subject.

    `limit` counts the intervening non-space characters AFTER deleting any other
    backtick spans in between. Deleting them is load-bearing: the sentence
    "the version of `Thm29Normal` without `[Domain E]` is refutable rather than
    open" has an instance binder standing between the subject and the cue, and a
    raw-distance rule attributes the claim to `[Domain E]`, which is not a claim
    about anything. Measured, that one span cost the sweep its second confirmed
    true positive.

    8 is the measured setting, not a guess. The widest true positive is
    "`Thm29Normal` without `[Domain E]` is refutable", gap "without" = 7. The
    narrowest false positive is "…`IdealCompletion A` — the smash is not among
    them", gap "— the smash" = 11, where the cue's real subject is the unbackticked
    "the smash" and the nearest span is one of the things that DO exist. Any
    limit in [7, 10] separates them; 8 is the midpoint.
    """
    cands = [(s, e, tok) for s, e, tok in spans_with_pos(sent) if e <= cue_start]
    for s, e, tok in reversed(cands):
        gap = sent[e:cue_start]
        for s2, e2, _ in cands:
            if s2 >= e:
                gap = gap.replace(sent[s2:e2], " ")
        if len(gap.strip()) > limit:
            return None
        if QUALIFIER.search(gap.lower()):
            return None
        if subject_shaped(tok):
            return (s, e, tok)
    return None


def subject_after(sent, cue_end, limit=6):
    """The backtick span immediately following a cue, if it is adjacent."""
    for s, e, tok in spans_with_pos(sent):
        if s >= cue_end and len(sent[cue_end:s].strip()) <= limit:
            return (s, e, tok)
    return None


# A QUALIFIER standing between the named constant and the cue means the claim is
# about a MODIFIED proposition, not about the constant. "the version of
# `Thm29Normal` without `[Domain E]` is refutable" is a claim about a different
# proposition than `Thm29Normal`, and the environment cannot be asked about it by
# name at all — `R45.Agent3.Thm29NormalWithoutDomain` is the separate `def` that
# had to be written to state it.
#
# This is the plan's own "discharged versus discharged-at" rule read in the other
# direction, and it is the reason it is a guard rather than a tuning knob: a
# theorem concluding D with an added instance binder is not a discharge of D, so
# a sentence about D with a deleted binder is not a claim about D. When the
# subject is qualified, the detector has no question it can answer and must not
# return a verdict.
QUALIFIER = re.compile(
    r"\b(without|with|at|modulo|minus|plus|version|variant|form|weakened|"
    r"strengthened|restricted|instantiated|specialised|specialized)\b")

# Separators that continue an ENUMERATION of subjects rather than ending it.
LIST_SEP = re.compile(r"\A[\s,;)(\]\[]*(?:and|or)?[\s,;)(\]\[]*\Z")


def enumerated_subjects(sent, anchor):
    """`anchor` plus every span joined to it by list punctuation.

    A survey sentence names its subjects as a list — "Nine name variants
    (`fSharp`, `powerdomainMap`, `Powerdomain.map`, …, `fNatural`) returned zero
    hits" — and only the LAST of them is adjacent to the cue. Testing that one
    alone tests one ninth of the claim, and it is the eight untested variants
    that carry the defect: the module declares `PowerdomainMap.map`, which
    answers `Powerdomain.map`, the third item.
    """
    spans = spans_with_pos(sent)
    idx = next((i for i, sp in enumerate(spans) if sp[:2] == anchor[:2]), None)
    if idx is None:
        return [anchor]
    out = [anchor]
    i = idx
    while i > 0:
        prev = spans[i - 1]
        if not LIST_SEP.match(sent[prev[1]:spans[i][0]]):
            break
        out.append(prev)
        i -= 1
    return out


def sentences(path):
    """Yield (line_no, kind, sentence) for each sentence of each Lean comment.

    Comments are joined into paragraphs (blank-line separated) before splitting,
    because these docstrings wrap a single sentence across three or four lines
    and a line-at-a-time split truncates the cue away from its subject — the
    defect that made r0044's first prose pass unusable.
    """
    with open(path, encoding="utf-8", errors="replace") as fh:
        raw = fh.read()
    masked, doc_lines = comment_mask(raw)
    lines = masked.split("\n")
    para, start, isdoc = [], None, False
    out = []

    def flush():
        if not para:
            return
        text = " ".join(para)
        # Split on sentence-final punctuation followed by space + capital, and
        # on markdown list-item / header boundaries.
        pieces = re.split(r"(?<=[.!?])\s+(?=[A-Z`*\d])", text)
        for p in pieces:
            p = p.strip()
            if p:
                out.append((start, "lean-doc" if isdoc else "lean-comment", p))

    for idx, line in enumerate(lines):
        body = line.strip()
        if not body:
            flush()
            para, start = [], None
            continue
        if start is None:
            start = idx + 1
            isdoc = doc_lines[idx] if idx < len(doc_lines) else False
        para.append(body)
    flush()
    for rec in out:
        yield rec


def prose_sentences(path):
    """Yield (line_no, "prose", sentence) for a markdown document.

    Fenced code blocks are skipped, exactly as `a7-cite-scan.py` skips them and
    for the same reason: they hold Lean source, and in a plan that source is a
    PROPOSED statement naming declarations that intentionally do not exist yet.
    Scanning them reports intent as defect.

    Only P1, P2 and P4 run over this corpus. P3 asks "does the SAME MODULE
    declare it?", and a markdown file is not a module, so the question has no
    answer here — running it anyway would be the same error as matching a
    package name against a claim about Mathlib.
    """
    with open(path, encoding="utf-8", errors="replace") as fh:
        lines = fh.read().split("\n")
    fence = False
    para, start = [], None
    out = []

    def flush():
        if not para:
            return
        text = " ".join(para)
        for p in re.split(r"(?<=[.!?])\s+(?=[A-Z`*\d])", text):
            p = p.strip()
            if p:
                out.append((start, "prose", p))

    for idx, line in enumerate(lines):
        stripped = line.lstrip()
        if stripped.startswith("```") or stripped.startswith("~~~"):
            fence = not fence
            flush()
            para, start = [], None
            continue
        if fence or not stripped:
            flush()
            para, start = [], None
            continue
        if start is None:
            start = idx + 1
        para.append(stripped)
    flush()
    for rec in out:
        yield rec


def ident_spans(sent):
    """Backtick spans that are exactly a Lean identifier."""
    for m in SPAN.finditer(sent):
        tok = m.group(1).strip()
        if IDENT.match(tok):
            yield tok


def head_spans(sent):
    """Backtick spans whose FIRST token is a Lean identifier but whose span is
    not — `Domain (D ⊗ E)`, `IsBifinite (Smash α β)`. The claim is about the
    class applied to a construction, and the class is what the environment can
    be asked about."""
    for m in SPAN.finditer(sent):
        tok = m.group(1).strip()
        if IDENT.match(tok):
            continue
        first = re.split(r"[\s(\[]", tok, 1)[0]
        if first and IDENT.match(first) and first[0].isupper():
            yield first, tok


def load_env(path):
    recs = []
    with open(path, encoding="utf-8") as fh:
        for line in fh:
            f = line.rstrip("\n").split("\t")
            if len(f) != 9 or f[0] != "DECL":
                continue
            recs.append({
                "module": f[1], "line": int(f[2]), "kind": f[3], "name": f[4],
                "concl": f[5], "neg": f[6], "hyps": int(f[7]),
                "inst": f[8] == "true",
            })
    return recs


def suffixes(name):
    parts = name.split(".")
    for i in range(len(parts)):
        yield ".".join(parts[i:])


def main():
    if len(sys.argv) != 4:
        raise SystemExit(__doc__)
    env_path, pkg_root, out_path = sys.argv[1:4]
    recs = load_env(env_path)

    by_name = {r["name"]: r for r in recs}
    suffix = defaultdict(list)
    by_module = defaultdict(list)
    concl_by_head = defaultdict(list)
    neg_by_head = defaultdict(list)
    propdefs = set()
    for r in recs:
        for s in suffixes(r["name"]):
            suffix[s].append(r)
        by_module[r["module"]].append(r)
        if r["concl"] != "-":
            concl_by_head[r["concl"]].append(r)
        if r["neg"] != "-":
            neg_by_head[r["neg"]].append(r)
        if r["kind"] == "propdef":
            propdefs.add(r["name"])
    # propdef reachable by suffix, so `Thm29Normal` finds
    # `ScottDomains.LemThirty.Thm29Normal`.
    propdef_suffix = defaultdict(list)
    for n in propdefs:
        for s in suffixes(n):
            propdef_suffix[s].append(n)

    def path_of(module):
        return os.path.join(pkg_root, module.replace(".", "/") + ".lean")

    def module_of(path):
        rel = os.path.relpath(path, pkg_root)
        return rel[:-5].replace("/", ".")

    def proofs_of(name):
        """Package theorems concluding `name`, and the hypothesis-free subset."""
        all_p = [r for r in concl_by_head.get(name, []) if r["kind"] == "thm"]
        return all_p, [r for r in all_p if r["hyps"] == 0]

    rows = []
    unresolved = []
    tally = defaultdict(int)

    def p3_check(subj, path, ln, kind, sent, local, external):
        """Ask the environment whether the claimed-absent subject is present.

        Four tiers in decreasing certainty. The SAME MODULE is asked first
        because an intra-file contradiction is both the cheapest to confirm and,
        measured over the round's confirmed sites, the commonest. But the module
        is a priority, NOT a restriction: r0046's agent3 falsified a claim in
        `Effective/FunctionSpace.lean` with material two files away, so tier
        P3c asks the same question package-wide.
        """
        tok = subj[2]
        if IDENT.match(tok):
            # (a) the exact name, matched on component boundaries.
            hit = [r for r in local if tok in set(suffixes(r["name"]))]
            if hit:
                rows.append(("P3", path, ln, kind, tok,
                             "same module declares %s at line %d"
                             % (hit[0]["name"], hit[0]["line"]), sent))
                tally["P3"] += 1
                return
            # (a') the exact name, anywhere in the package.
            if not external:
                far = suffix.get(tok, [])
                if far:
                    rows.append(("P3c", path, ln, kind, tok,
                                 "package declares %s in %s at line %d"
                                 % (far[0]["name"], far[0]["module"],
                                    far[0]["line"]), sent))
                    tally["P3c"] += 1
                    return
            # (b) the same JOB under another qualifier. A survey of name variants
            # that all miss is not evidence of absence when the module itself
            # declares a constant with the searched-for LAST COMPONENT.
            # Suppressed for a claim about an external library, which a package
            # declaration cannot bear on.
            if external:
                tally["external-suppressed"] += 1
                return
            tail = tok.split(".")[-1]
            if len(tail) < 3 or "." not in tok:
                return
            alt = [r for r in local if r["name"].split(".")[-1] == tail]
            if alt:
                rows.append(("P3b", path, ln, kind, tok,
                             "same module declares %s at line %d — same final "
                             "component under a different qualifier"
                             % (alt[0]["name"], alt[0]["line"]), sent))
                tally["P3b"] += 1
            return
        # (c) a class applied to a construction: `Domain (D ⊗ E)`. Ask for a
        # package declaration in this module whose CONCLUSION is headed by that
        # class, preferring one whose name mentions the construction, so the
        # evidence line names the right declaration rather than the first found.
        first = re.split(r"[\s(\[]", tok, 1)[0]
        if not (first and IDENT.match(first) and first[0].isupper()):
            return
        cls = [r for r in local
               if r["concl"] != "-" and first in set(suffixes(r["concl"]))]
        if not cls:
            return
        arg = tok[len(first):]
        words = set(re.findall(r"[A-Za-z]{3,}", arg))
        # This development writes its type constructors as operators, so the
        # argument of the claimed-absent class is usually a symbol and carries no
        # word to match on. The map is the one the modules themselves use.
        for sym, word in (("⊗", "smash"), ("⊕", "sepsum"), ("×", "prod"),
                          ("→⊥", "strict"), ("⇸", "strict"), ("⊸", "strict"),
                          ("→", "hom"), ("♮", "plotkin"), ("♯", "smyth"),
                          ("♭", "hoare"), ("⊥", "lift")):
            if sym in arg:
                words.add(word)
                break

        def score(r):
            n = r["name"].lower()
            return sum(1 for w in words if w.lower() in n)

        cls.sort(key=lambda r: (-score(r), r["line"]))
        rows.append(("P3", path, ln, kind, tok,
                     "same module declares %s : %s at line %d"
                     % (cls[0]["name"], cls[0]["concl"], cls[0]["line"]), sent))
        tally["P3"] += 1

    def p4_check(sent, path, ln, kind, names, proofs_of):
        """Report a numeral-bearing claim about how many things are proved next
        to the environment's own count for the same conclusion head."""
        m = COUNT_RE.search(sent)
        if not m or not (m.group(1) or m.group(3)):
            return
        word = m.group(2).lower()
        stated = NUMWORD.get(word, int(word) if word.isdigit() else 0)
        fam = defaultdict(int)
        for tok in names:
            for r in suffix.get(tok, []):
                if r["concl"] != "-":
                    fam[r["concl"]] += 1
        if not fam:
            return
        head = max(fam, key=fam.get)
        allp, uncond = proofs_of(head)
        if stated and len(uncond) > stated:
            rows.append(("P4", path, ln, kind, head,
                         "claim says %d; environment has %d hypothesis-free "
                         "theorems concluding %s (%d in all)"
                         % (stated, len(uncond), head, len(allp)), sent))
            tally["P4"] += 1

    files = []
    for dirpath, _, names in os.walk(os.path.join(pkg_root, "ScottDomains")):
        if ".lake" in dirpath:
            continue
        for n in sorted(names):
            if n.endswith(".lean"):
                files.append(os.path.join(dirpath, n))
    # Goal B names "no docstring OR DOCUMENT asserting that something is proved",
    # so `docs/` is in scope. `plans/`, `reports/` and `analyses/` are not: every
    # one of them is a dated record of a round, which the round's own rules
    # forbid rewriting, and the `r00NN` hedge would suppress them anyway.
    docs = os.path.join(pkg_root, "docs")
    if os.path.isdir(docs):
        for n in sorted(os.listdir(docs)):
            if n.endswith(".md"):
                files.append(os.path.join(docs, n))

    for path in sorted(files):
        is_lean = path.endswith(".lean")
        mod = module_of(path) if is_lean else None
        local = by_module.get(mod, []) if is_lean else []
        for ln, kind, sent in (sentences(path) if is_lean
                               else prose_sentences(path)):
            tally["sentences"] += 1
            low = sent.lower()
            if "`" not in sent:
                continue
            tally["with-citation"] += 1
            hedged = (any(h in low for h in HEDGES)
                      or any(h in low for h in REPORTED)
                      or ROUND_RE.search(low) is not None)
            if hedged:
                tally["hedged"] += 1
                continue
            names = list(ident_spans(sent))

            # ---- P1 / P2: status of a Prop-valued package def -----------------
            # The SUBJECT of a status cue is the backticked name adjacent to it,
            # not any name in the sentence. Without that rule, "implied by
            # `Colimit.Thm29Second` (`thm29SecondAtDomains_of_thm29Second`) and
            # implied by `Thm29Normal` (`…_of_thm29Normal`, proved below)" scores
            # two defects, when what is "proved below" is the IMPLICATION named
            # immediately before the cue and both readings are true.
            for cue in PROVED_CUES + OPEN_CUES:
                pos = word_cue(low, cue)
                if not pos or in_quotes(sent, pos[0]):
                    continue
                subj = subject_before(sent, pos[0])
                if not subj:
                    continue
                tok = subj[2]
                if not IDENT.match(tok):
                    continue
                cands = propdef_suffix.get(tok, [])
                if len(cands) != 1:
                    continue
                pd = cands[0]
                # A (cue, subject) pair the environment can answer. The count of
                # these is the denominator that makes the defect count mean
                # something: a sweep that tests nothing reports nothing.
                tally["tested-P1P2"] += 1
                allp, uncond = proofs_of(pd)
                if cue in PROVED_CUES:
                    if not allp:
                        tally["P1"] += 1
                        rows.append(("P1", path, ln, kind, tok,
                                     "0 package theorems conclude %s" % pd, sent))
                elif cue in ("is refutable", "is refuted"):
                    if not neg_by_head.get(pd, []):
                        tally["P2"] += 1
                        rows.append(("P2", path, ln, kind, tok,
                                     "no package theorem concludes Not %s" % pd,
                                     sent))
                elif uncond:
                    tally["P2"] += 1
                    rows.append(("P2", path, ln, kind, tok,
                                 "%d hypothesis-free theorem(s) conclude %s: %s"
                                 % (len(uncond), pd,
                                    ",".join(r["name"] for r in uncond[:3])),
                                 sent))

            # ---- P3: absence claim refuted inside the same module -------------
            past = any(word_cue(low, p) for p in PAST_TENSE)
            external = any(x in low for x in EXTERNAL)
            for cue in (ABSENT_PRE + ABSENT_POST) if not past else []:
                pos = word_cue(low, cue)
                if not pos or in_quotes(sent, pos[0]):
                    continue
                anchor = (subject_before(sent, pos[0]) if cue in ABSENT_PRE
                          else subject_after(sent, pos[1]))
                if not anchor:
                    # The claim's subject is an English noun phrase, not a
                    # backticked name: "this development has no
                    # strict-step-function basis to enumerate". The environment
                    # cannot be asked about it, so no verdict is possible — but
                    # the site is still a claim, and r0046's agent3 confirmed
                    # exactly such a sentence false. Counted and listed as a
                    # manual worklist, NOT scored as a defect and NOT in the
                    # precision denominator. Its size is this sweep's recall gap,
                    # stated as a number rather than as a caveat.
                    tally["unresolvable"] += 1
                    unresolved.append((path, ln, kind, cue, sent))
                    continue
                for subj in enumerated_subjects(sent, anchor):
                    tally["tested-P3"] += 1
                    p3_check(subj, path, ln, kind, sent, local, external)

            # ---- P4: count claim about proved items ---------------------------
            if any(word_cue(low, c) for c in PROVED_CUES) and names:
                p4_check(sent, path, ln, kind, names, proofs_of)

    rows.sort(key=lambda r: (r[0], r[1], r[2]))
    with open(out_path, "w", encoding="utf-8") as out:
        for det, path, ln, kind, tok, why, sent in rows:
            out.write("%s\t%s\t%d\t%s\t%s\t%s\t%s\n"
                      % (det, path, ln, kind, tok, why,
                         re.sub(r"\s+", " ", sent)[:400]))
    with open(out_path + ".unresolvable", "w", encoding="utf-8") as out:
        for path, ln, kind, cue, sent in sorted(unresolved):
            out.write("%s\t%d\t%s\t%s\t%s\n"
                      % (path, ln, kind, cue, re.sub(r"\s+", " ", sent)[:300]))

    for k in ("sentences", "with-citation", "hedged",
              "tested-P1P2", "tested-P3", "external-suppressed", "unresolvable",
              "P1", "P2", "P3", "P3b", "P3c", "P4"):
        print("%-14s %d" % (k, tally[k]))
    print("rows           %d" % len(rows))
    print("wrote %s" % out_path)


if __name__ == "__main__":
    main()
