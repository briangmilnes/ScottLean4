---
round: r0036
from: orchestrator
to: agent4
subject: lemma-28
date: 2026-0807-08:32
status: pending
related:
  - plans/r0036-plan-from-orchestrator-to-orchestrator-five-way-open-results.md
---

# r0036 stream 4 — agent4 — Lemma 28 at the right notion

Worktree `/home/milnes/projects/ScottLean4-agent4`, branch `agent4`.
Namespace **`ScottDomains.PRep`** — note this is *not* `PRepresentable`, which is
r0034's module on `main` and which you import.

## The goal

Lemma 28: the operators **`→, ×, ⊗, ⊕, +, ()⊥, ()♮, ()♯, ()♭`** — **nine**, not
the seven earlier drafts listed — are **p-representable over `Fp(U)`**, at §7.3's
dyadic-interval domain `U`.

State it and prove as many conjuncts as land. The current position is 3 of 9
**and at the wrong notion**, which is the thing this stream exists to fix.

## Why the existing three proofs are suspect, not merely incomplete

r0034's agent4 proved `CombinatorRep.rep_arrow`, `rep_prod` and `rep_lift` over
an abstract carrier needing only `Retracts U V` — the *closure* reading, using
`IsRepresentable` over `Fc(U)`. The same agent then **refuted that reading**:

> `U` the three-chain `⊥ ⊏ p ⊏ q` with `r = s` the closure `⊥ ↦ p` gives
> `im(r) ⊗ im(s)` 2 elements against `im(r ⊗ s)` 4 — `im(r)`'s bottom is
> `r⊥ ≠ ⊥`, so the target collapses a point the source does not.

A *projection* has `p⊥ = ⊥` and the obstruction vanishes — which is an independent
argument that the paper means `Fp(U)`. Two further signs the closure reading is
wrong: `()♯` and `()♭` do not even typecheck there, needing `[Domain D]` while
`im r` for a closure on a cpo is not a domain.

So the three existing proofs are **at a notion the development has since shown to
be the wrong one**. Re-examine each against `IsPRepresentable`; do not assume they
transfer. Some may — `Retracts` is a weak interface and a projection pair
satisfies it — but that is a claim to check, not to inherit.

## What exists to build on

| # | Asset | Where |
| -- | ----- | ----- |
| 1 | `PRepresentable.IsPRepresentable`, `IsPRepresentable₂` | `PRepresentable.lean:99, 106` — over `↥(Fp U)`, with `FpImage` the carrier map |
| 2 | `eq_id_of_mem_Fp_of_mem_Fc` | `PRepresentable.lean:119` — `Fp` and `Fc` meet only at `ScottHom.id`, so the distinction from Lemma 28's `IsRepresentable` is kernel-checked, not documented |
| 3 | `isProjection_repOf` | `PRepresentable.lean:147` — the projection half of the paper's conjugation recipe |
| 4 | `Dyadic.U`, `U₀`, `Domain U`, `BoundedComplete U` | `Dyadic.lean`, r0034 — **already on `main`**, so unlike r0034's stream 4 there is nothing to wait for |
| 5 | `CombinatorRep.rep_arrow`, `rep_prod`, `rep_lift` | the three to re-examine |
| 6 | `Fp(D)` as a poset | `FinitaryProjectionPoset.lean`, r0028 |

## Order of work

1. **State Lemma 28 as one theorem** — a conjunction over the paper's own
   nine-operator list, at `IsPRepresentable`/`IsPRepresentable₂` over `Fp U`. r0034
   did this for Lemmas 10 and 17 and it is why their conjunct counts are now
   kernel-checked rather than prose; two rounds were lost to prose counts drifting
   from the files. Conjuncts not yet proved are named in the statement and the
   theorem carries them as hypotheses, or the statement is built up conjunct by
   conjunct — either way the count must be readable off the file.
2. **Re-examine `→`, `×`, `()⊥`** at the projection notion. Report for each
   whether the r0034 proof transfers unchanged, transfers with a changed
   hypothesis, or fails.
3. **`+`.** The inventory measures this at 150–200 lines and it is the cheapest
   new conjunct. `+` is the separated sum, `D + E = D⊥ ⊕ E⊥` (§4.4), which is how
   `ClosureProperties.lem10_separated` got it for Lemma 10.
4. **`⊗` and `⊕`**, which the counterexample says should now *work* at the
   projection notion — proving them is the direct confirmation that the notion
   was the problem.
5. **`()♮`, `()♯`, `()♭`.** These three need `[Domain D]` of the image, so they
   are statable at the projection notion and were not at the closure notion. The
   three powerdomains have existed since r0029 as `IdealCompletion (Pf K(D))`.

## Acceptance, ranked

1. All nine conjuncts at `IsPRepresentable` over `Fp U`, as one theorem
   `PRep.lemma28`. Lemma 28 moves to `✓` in the inventory.
2. The nine-conjunct statement plus five or more proved, including `+` and at
   least one of `⊗`/`⊕` — the latter being the evidence that the notion change was
   the fix.
3. The nine-conjunct statement plus the three r0034 conjuncts re-proved at the
   projection notion, with a measured report on what transferred.
4. The statement alone, correctly at `IsPRepresentable` over `Fp U`, with the
   three re-examinations reported — this is still a real gain, because the current
   3 of 9 is at a notion known to be wrong.

**Do not leave a `sorry`.** An unproved conjunct is named in the docstring and
omitted from the conjunction, not stubbed.

## Process rules

1. Namespace `ScottDomains.PRep`. Import `PRepresentable`, `Dyadic`,
   `CombinatorRep`; do not add declarations to them.
2. `Edit`/`Write` only. Never a heredoc, never `sed -i`.
3. One command per `Bash` call. Never chain, never `cd`.
4. Multi-step work becomes a script in `scripts/` — standing-authorized.
5. Build with `/home/milnes/projects/ScottLean4-agent4/scripts/compile.sh -r r0036`.
6. **Read §7.3 of the PDF for the operator list.** The count went 7 → 9 exactly
   because an agent did this. The glyphs `♮`/`♯`/`♭` render as `\`/`]`/`[` under
   `pdftotext`, and `→` and `◦→` both extract as `!`; check against the decoded
   stream, not the raw extraction.
7. **This plan is not evidence.** The source wins; say so in the report.
8. Commit on `agent4` at every stopping point, including with build errors, using
   `/home/milnes/projects/ScottLean4-agent4/scripts/gitcp.sh "<message>" <paths>`.
   Do not push.
9. Write `reports/r0036-report-from-agent4-to-orchestrator-lemma-28.md` with
   `started:`/`finished:` and a conjunct-by-conjunct table: proved, refuted, or
   open, and at which notion.
