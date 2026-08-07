---
round: r0034
from: orchestrator
to: agent3
subject: universal-domain-theorem-27
date: 2026-0806-22:35
status: pending
related:
  - plans/r0034-plan-from-orchestrator-to-orchestrator-six-way-remaining.md
---

# r0034 agent3 — §7.3's universal domain `U`, then Theorem 27

Namespace: **`ScottDomains.Dyadic`**. New construction; **two other streams depend
on you**, so read the reporting order below before starting.

## Part 1 — build `U`

§7.3's universal domain is the **ideal completion of the dyadic half-open
intervals**. This is not a fresh development: Theorem 11 (r0028,
`IdealCompletion.thm11`) already proves that the ideal completion of a *countable
pre-order* is a domain, and `thm11_converse` that all domains so arise. What you
must supply is the pre-order — the dyadic half-open intervals with the paper's
ordering — and its countability. The `Domain` instance is then Thm 11 applied.

Characterize `K(U)` explicitly. Streams 4 and 5 both need to know what the
compacts are, and §7's later results are stated over them.

**Do not build `D∞`.** §7 constructs no inverse limit; an earlier inventory draft
claimed it did and the claim was false. If you find yourself building an inverse
limit, stop and re-read.

## Part 2 — Theorem 27

Every bounded-complete `D` is a projection of `U`.

Two proved results are on the paper's route:

- **Prop 15** (r0027, `ScottDomains.prop15`): every bounded-complete domain is
  bifinite, by the paper's own proof over `lubClosure u`.
- **Theorem 22** (r0028, `ScottDomains.thm22`): any countably-based algebraic
  lattice `L` admits a closure `r : P(ℕ) → L`, with
  `thm22_of_isCompactlyGenerated` the Mathlib-vocabulary form.

Embedding–projection pairs are `ScottHom.IsEmbeddingProjectionPair` (r0012);
`im(p)` carries a `CompletePartialOrder` via `IsProjection.rangeCompletePartialOrder`.

## Reporting order — this matters to streams 4 and 5

**Report `U`'s carrier and its interface as soon as Part 1 compiles, before
finishing Part 2.** Write it as a short note in the report file and commit, then
continue. agent4's Lemma 28 and agent5's Lemma 30 both instantiate at your `U`;
they are proving over an abstract carrier to avoid blocking on you, and they need
your interface to align it early. A late interface costs them a rewrite.

## Acceptance criteria

1. `U` defined, with a `Domain` instance and `K(U)` characterized.
2. `thm27` proved, or — if it does not land — `U` alone delivered complete, with
   the obstruction to Thm 27 stated precisely. Do not leave a `sorry`.
3. `scripts/compile.sh -r r0034` reports 0 errors and 0 warnings beyond `sorry`.
4. Interface note committed before Part 2 finishes.

## Process rules

1. **Namespace `ScottDomains.Dyadic`** for every new declaration. You are one of
   six agents this round; the collision limit binds at ~6 and the namespace rule
   is what keeps it at zero.
2. **Edit/Write only — never heredocs.** This was r0032 agent3's plan violation;
   do not repeat it.
3. **One command per Bash call. Never chain, never `cd`.**
4. Multi-step work becomes a script in `scripts/` — standing-authorized.
5. **Read the PDF, not the paraphrase.**
6. **Commit to branch `agent3` with `scripts/gitcp.sh`; do not push.**
7. Write `reports/r0034-report-from-agent3-to-orchestrator-universal-domain-theorem-27.md`
   with `started:`/`finished:` and the measured counts.
