# Scoped claims — the writing convention for quantified prose

r0049 / agent8. Applies to every docstring, module comment and `docs/` file in
this package.

## The measurement that forces a convention

r0046's sweep classified 228 prose sites carrying a necessity, impossibility,
absence or uniqueness claim. r0049 re-ran it over the grown corpus and triaged
the 264 candidates by *what would decide each one*:

| # | Tier | Sites | Decided by |
| -- | ---- | ----: | ---------- |
| 1 | `ADJ` — already carries an r0046 verdict | 15 | — |
| 2 | `QUOTE` — reproduced behind a `>` marker | 7 | reading the source it quotes |
| 3 | `CITE` — backticked subject, resolves or does not | 43 | `scripts/a8-r49-cites.sh` |
| 4 | `SCOPE` — quantified, domain of the quantifier unstated | **114** | *nothing* |
| 5 | `NARR` — no backticked subject; about the proof as written | 85 | the file's own elaboration |

Tier 4 is the largest and it is the only one with no instrument. That is not an
instrument gap. r0046's agent5 built the reverse-dependency probe, ran it at
`JungBicomplete.lean:506` — "`JungNets.HasChainInfima`, which `Thm18` is now
known to be the only consumer of" — **measured 11 direct users, and refused to
convict.** The refusal was correct. The sentence is about the Theorem 18 route;
the probe counted the package. A global denominator cannot decide a claim whose
denominator the sentence never states, and building a better probe does not
change that.

## The same defect outside tier 4

r0049 found the failure is not confined to uniqueness claims. Of the four
absence claims corrected this round, **three were scope errors, not
falsehoods**:

| # | Site | Sentence | Package-wide truth |
| -- | ---- | -------- | ------------------ |
| 1 | `JungNets.lean:80` | "the development has no predicate for a continuous dcpo" | `JungBicomplete.IsContinuousDcpo` is one |
| 2 | `JungNets.lean:190` | "Theorem 1.2 (Iwamura's lemma), which is not available here" | `Iwamura.lean` proves it |
| 3 | `JungNets.lean:303` | "**This is not proved.**" (of `Thm137`) | `R45.Agent5.thm137` proves it at `[Domain D]` |

Each was true of the module and false of the package, and each was read
package-wide by every later round — sites 1 and 2 because `JungBicomplete.lean`
and `Iwamura.lean` **import** `JungNets.lean`, so the thing claimed absent
cannot be named at the site that claims it. The writer had a correct thought and
no vocabulary for it.

## The convention

**Every quantified claim names its scope, in the sentence, from the fixed
vocabulary below.** A claim with no scope token is read package-wide, and
`scripts/a8-claim-check.sh` treats it as such.

| # | Scope token | Means | Probe that decides it |
| -- | ----------- | ----- | --------------------- |
| 1 | *in this proof* | the tactic block or term below | the file elaborates |
| 2 | *in this declaration* | the one declaration | its elaborated type |
| 3 | *in this module* / *in this file* | this `.lean` file | `grep` this file; intra-file, cheap |
| 4 | *at this point in the import order* | the transitive imports of this module | `a4-decl-query.lean`, restricted to the import cone |
| 5 | *in this development* / *package-wide* | every `ScottDomains.*` module | `a8-r49-env.sh` + `a7-resolve.py` |
| 6 | *in Mathlib v4.32.2* | that Mathlib, named with its version | `exact?` on the **statement**, never a name grep |
| 7 | *in the paper* | Gunter & Scott 1990, with page | reading the page |

Tokens 3 and 4 differ and the difference is load-bearing. "Not available in this
module" is a fact about the file; "not available at this point in the import
order" is a fact about the DAG and is what the three defects above meant. A
result proved in a module that imports this one satisfies 4 and violates 5.

Three further rules, each answering a defect on record:

1. **A quantity carries its denominator and its round.** Not "the only
   consumer", but "1 of 11 direct users, measured r0046". The denominator is
   what makes the sentence re-checkable; the round is what makes staleness
   visible without re-deriving it. `JungBicomplete.lean:506` under this rule
   reads "the only consumer *among the Theorem 18 route's declarations*; 11
   direct users package-wide, measured r0046".

2. **"Proved" states its binders.** r0049's `Thm137` case: the `def` quantifies
   over `[CompletePartialOrder D]` and the theorem proves it for
   `[CompletePartialOrder D] [Domain D]`. "This is proved" and "this is not
   proved" are both wrong; "proved at `[Domain D]`, open for the non-algebraic
   case" is right. This is the round's *discharged* versus *discharged-at*
   distinction, written into the sentence rather than into a report.

3. **An absence claim names the locus it is absent from**, and the locus is one
   of tokens 3–7. `scripts/a8-r49-absence.py` classifies existing prose into
   exactly those loci and reports the count per locus; a sentence that the
   classifier cannot place is a sentence that does not name its scope.

## What it costs and what it buys

Cost: one prepositional phrase per claim. Nothing is deleted and no claim is
weakened — scope is what the writer already meant.

Buys: tier 4's 114 sites become decidable. Under tokens 3 and 4 the probe is a
grep of one file or of one import cone, both of which `a4-decl-query.lean`
already supports; under token 5 it is the reverse-dependency count r0046 built
and could not aim. It also removes the failure mode that produced all three
corrections above, which is not that the writer was wrong but that the reader
could not tell what was being claimed.

## Correction protocol, unchanged

When a scope error is found, **keep the original sentence and record what
changed**, per r0046. The corrections listed above each do this: the sentence is
rewritten with its scope named, and a `*Correction, rNNNN/agentN.*` paragraph
quotes what it said and names the declaration that refutes the package-wide
reading. None deletes the record.
