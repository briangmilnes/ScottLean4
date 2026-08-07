---
round: r0037
from: orchestrator
to: agent4
subject: lemma-28-sums-and-U
date: 2026-0807-11:09
status: pending
related:
  - plans/r0037-plan-from-orchestrator-to-orchestrator-last-four.md
---

# r0037 stream 4 — agent4 — Lemma 28's sums and powerdomains, and `Lemma28AtU`

Worktree `/home/milnes/projects/ScottLean4-agent4`, branch `agent4`.
Namespace **`ScottDomains.PRepSum`**.

## The goal

Four of Lemma 28's nine conjuncts, plus the instantiation at the real `U`:

| # | Operator | Conjunct | Note |
| -- | -------- | -------- | ---- |
| 5 | `+` | `IsPRepresentable₂ U sepSumOp` | the separated sum, `D + E = D⊥ ⊕ E⊥` (§4.4) |
| 6 | `⊕` | `IsPRepresentable₂ U coalSumOp` | the coalesced sum |
| 8 | `()♯` | `IsPRepresentable U smythOp` | Smyth powerdomain |
| 9 | `()♭` | `IsPRepresentable U hoareOp` | Hoare powerdomain |
| — | — | **`PRep.Lemma28AtU`** | **see below — this is the headline** |

You wrote `PRep.lean` last round, so the machinery is yours. The operators are
already defined at `PRep.lean:147–189`; you prove representability.

## The headline: `Lemma28AtU` is unblocked, and its own docstring is stale

`PRep.lean:114–119` says:

> At §7.3's `U` the pair is what **Theorem 27** supplies, and `Dyadic.thm27` is
> still conditional on `IsNormallyRepresented`, so `Lemma28AtU` is not yet
> derivable from them — the instantiation is blocked one level below this file.

**That was true when you wrote it and is false now.** In the same round, agent3
proved `Atomless.thm27` — Theorem 27 with **no hypothesis at all**, for every
bounded complete domain, with `Atomless.isNormallyRepresented_compacts`
discharging the condition. Neither of you could see the other's work.

So `Lemma28AtU` is derivable for every conjunct already proved, **today**, and it
is the single highest-value item in this stream: it converts conditional
representability over an abstract carrier into representability over §7.3's
actual dyadic-interval domain, which is what the paper's Lemma 28 asserts. Do
this **first**, before proving any new conjunct — it is short, it is unblocking
work already done, and it retires a stale claim in a file the whole project
reads.

Correct the docstring while you are there.

## Then the four conjuncts

`isFinitaryProjection_sSup` (`PRep.lean:427`) is the keystone and discharges each
conjunct's continuity obligation; the estimate is 120–180 lines each.

- **`+` is expected cheapest.** `D + E = D⊥ ⊕ E⊥` is §4.4's own definition, and
  that is exactly how `ClosureProperties.lem10_separated` got `+` for Lemma 10.
  If `⊕` and `()⊥` are both available, `+` should follow from them rather than
  from scratch — `rep_lift` is already proved.
- **`⊕` is no longer refuted.** r0034's three-chain counterexample refuted `⊗`
  and `⊕` at the *closure* reading; a projection has `p ⊥ = ⊥`, so it does not
  apply here. Proving `⊕` is the direct confirmation that the notion was the
  problem.
- **`()♯` and `()♭` are the two you showed are definable at all.** Your own r0036
  finding: `CombinatorRep.lean` claimed they need `[Domain D]` of the type, and
  you showed the `[Domain D]` is spent only on `IdealCompletion.instDomain`, so
  `smythOp`/`hoareOp` compile on `Cpo` with `smythOp_eq`/`hoareOp_eq` agreeing by
  `rfl`. The powerdomains have existed since r0029.

## Acceptance, ranked

1. `Lemma28AtU` derived for every proved conjunct, **and** all four of your
   conjuncts proved. With stream 3 this closes Lemma 28 at 9 of 9.
2. `Lemma28AtU` derived, plus `+` and `⊕`.
3. `Lemma28AtU` derived, plus one conjunct.
4. **`Lemma28AtU` alone**, with the stale docstring corrected. This is a complete
   deliverable on its own: it is the difference between "representable over some
   carrier satisfying an interface" and "representable over the paper's `U`".

**No new `sorry`.** An unproved conjunct is named in the docstring and omitted
from the conjunction, not stubbed.

## Process rules

1. Namespace `ScottDomains.PRepSum`. You may edit `PRep.lean`'s **docstring** to
   correct the stale claim and may add `Lemma28AtU`'s derivation there if that is
   where it belongs — but new machinery goes in your own namespace, and agent3 is
   extending `PRep` from `ScottDomains.PRepFun` this round, so keep edits to
   `PRep.lean` minimal and confined to what you must change.
2. Edit/Write only. Never a heredoc, never `sed -i`.
3. One command per Bash call. Never chain, never `cd`.
4. Multi-step work becomes a script in `scripts/` — standing-authorized — but
   **check `scripts/` first and prefix any new script with your stream name**.
   Your four PDF helpers from r0036 are on `main`; reuse them. r0036 lost a merge
   because you and agent5 both wrote `scripts/pdf-section.sh`.
5. Build with `/home/milnes/projects/ScottLean4-agent4/scripts/compile.sh -r r0037`.
6. Read §7.3 of the PDF directly — you are the agent who established that the
   operator list must be read off a 600 dpi render, not `pdftotext`.
7. **This plan is not evidence.** The source wins; say so in the report.
8. Commit at every stopping point with
   `/home/milnes/projects/ScottLean4-agent4/scripts/gitcp.sh`. Do not push.
9. Report to
   `ScottDomains/reports/r0037-report-from-agent4-to-orchestrator-lemma-28-sums-and-U.md`
   with `started`/`finished`, whether `Lemma28AtU` went through as expected, and a
   conjunct-by-conjunct table.
