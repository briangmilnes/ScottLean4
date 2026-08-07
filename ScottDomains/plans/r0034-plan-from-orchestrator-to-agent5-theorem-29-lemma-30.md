---
round: r0034
from: orchestrator
to: agent5
subject: theorem-29-lemma-30
date: 2026-0806-22:35
status: pending
related:
  - plans/r0034-plan-from-orchestrator-to-orchestrator-six-way-remaining.md
  - plans/r0034-plan-from-orchestrator-to-agent3-universal-domain-theorem-27.md
---

# r0034 agent5 — Theorem 29, §7.4's `V`, and Lemma 30

Namespace: **`ScottDomains.BifiniteUniversal`**. This is the largest stream of the
six; the acceptance criteria say explicitly what a partial landing looks like, so
read them before deciding scope.

## Part 1 — Theorem 29 and `V`

`D` bifinite ⟹ `D+` bifinite, and solving `D ≅ D+`.

**Check what [Gun87] leaves deferred before proving.** The r0033 restart plan
flagged this and it is still unchecked — the paper cites it, and if the cited
source defers a step, that step is yours and you should know it on day one, not
after a failed proof attempt. This is the same discipline that made Theorem 18
expensive across three rounds.

Theorem 29 and `V` are **one piece of work, not two**: solving `D ≅ D+` is how
§7.4 constructs the bifinite universal domain. Available machinery:
`ScottDomains.IsPlotkinOrder` and `IsBifinite` (r0025), `isBifinite_iff_mubClosure`
(r0028), `Recursive.thm21` and `Recursive.IsUniversal` (r0029), and Prop 15
(r0027) for the bounded-complete case.

Note `+` is a different operator from the coalesced sum `⊕` (`CoalescedSum.lean`,
r0028), and agent2 is proving `+`'s closure conjuncts this round — coordinate
through the orchestrator at merge rather than duplicating.

## Part 2 — Lemma 30

The seven operators `→, ×, ⊗, +, ()⊥, ()♯, ()♭` are **p-representable** over `V`.

**P-representability is a distinct notion from `IsRepresentable`.** It is defined
over `Fp(U)` — the finitary *projections* — where `IsRepresentable` is over
`Fc(U)`, the finitary closures. Do not reuse the existing class, and state the
distinction in `IsPRepresentable`'s docstring; conflating them is the single most
likely way this stream produces a wrong result that still compiles.

`Fp(D)` as a poset already exists (`FinitaryProjectionPoset.lean`, r0028), so you
can define `IsPRepresentable` **without waiting on agent3's `U`**. Only the
instantiation waits.

Two facts about `Fp` from r0032 that bear on this: `Pf` is the finite *non-empty*
subsets, and Theorem 16's `Fp(D) ↪ (D → D)` embedding conjunct is **false**,
kernel-checked in `FinitaryProjectionEmbedding.lean`. Do not build on that
embedding.

## Acceptance criteria

Ranked. Deliver in this order and stop at a clean boundary rather than leaving a
`sorry`:

1. `thm29` proved, and `V` defined with its `Domain` and bifiniteness instances.
   **This alone is a complete deliverable.**
2. `IsPRepresentable` defined and distinguished from `IsRepresentable` in its
   docstring.
3. `lem30` proved for as many of the seven operators as land; name the ones that
   did not and why.
4. `scripts/compile.sh -r r0034` reports 0 errors and 0 warnings beyond `sorry`.
   No new `sorry` — an unproved operator is reported, not stubbed.

## Process rules

1. **Namespace `ScottDomains.BifiniteUniversal`** for every new declaration.
2. **Edit/Write only — never heredocs.**
3. **One command per Bash call. Never chain, never `cd`.**
4. Multi-step work becomes a script in `scripts/` — standing-authorized.
5. **Read the PDF, not the paraphrase** — and for Part 1, read [Gun87] too.
6. **Commit to branch `agent5` with `scripts/gitcp.sh`; do not push.**
7. Write `reports/r0034-report-from-agent5-to-orchestrator-theorem-29-lemma-30.md`
   with `started:`/`finished:` and the measured counts.
