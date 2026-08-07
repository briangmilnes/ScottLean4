---
round: r0037
from: orchestrator
to: agent3
subject: lemma-28-function-spaces
date: 2026-0807-11:09
status: pending
related:
  - plans/r0037-plan-from-orchestrator-to-orchestrator-last-four.md
---

# r0037 stream 3 — agent3 — Lemma 28's `→`, `⇸` and `⊗`

Worktree `/home/milnes/projects/ScottLean4-agent3`, branch `agent3`.
Namespace **`ScottDomains.PRepFun`**.

## The goal

Lemma 28 is nine conjuncts, stated on `main` as `PRep.Lemma28` with
`PRep.lemma28_of` taking each as a named hypothesis, so the count is
kernel-checked. Two are proved. **Yours are conjuncts 1, 2 and 4** — the
function spaces and the smash:

| # | Operator | Conjunct | Status |
| -- | -------- | -------- | ------ |
| 1 | `→` | `IsPRepresentable₂ U funOp` | **yours** |
| 2 | `⇸` | `IsPRepresentable₂ U strictFunOp` | **yours** |
| 4 | `⊗` | `IsPRepresentable₂ U smashOp` | **yours** |

The operator definitions already exist at `PRep.lean:147–189`; you prove the
representability, you do not define the operators.

## What r0036 established, and what it means for you

**The keystone is done.** `PRep.isFinitaryProjection_sSup` (`PRep.lean:427`) —
over a domain the directed supremum of finitary projections is finitary, hence
least upper bounds in `Fp(D)` are pointwise (`isLUB_val_image_of_isLUB_fp'`).
Every conjunct's continuity obligation goes through it. That is why the estimate
for each remaining conjunct is 120–180 lines rather than a fresh development.

**`⊗` is no longer refuted.** r0034 refuted `⊗` and `⊕` at the *closure* reading
with a three-chain counterexample. A projection has `p ⊥ = ⊥`, so the obstruction
vanishes — and proving `⊗` at the projection notion is the direct confirmation
that the notion was the whole problem. Take `⊗` seriously rather than expecting
it to fail.

**Do not reuse r0034's `Combinator.rep_arrow`.** It is at the closure notion over
`Retracts U V`, and r0036 kernel-checked that this does **not** transfer:
`Retracts` gives `id ⊑ gr ∘ fn` where the projection scheme needs
`gr ∘ fn ⊑ id`, and `PRep.gr_fn_eq_of_both` proves that holding both forces
`U ≅ V`. `rep_arrow` is the closure-notion arrow and is not your conjunct 1.

## Suggested order

1. **`→` first.** It is the one with the most existing support —
   `ScottHom.lean`, `StepFunction.lean`, `FunctionSpaceDomain.lean` — and the
   pattern it establishes is what `⇸` and `⊗` follow. Model the proof on
   `PRep.rep_prod` and `PRep.rep_lift`, which are the two already at this notion;
   read them before starting, especially how each discharges the `Domain` of the
   conjugating family's image (that is `Fp`'s extra obligation, the one `Fc`
   never had).
2. **`⇸` second** — the strict function space, `StrictHom.lean` (r0024). Expect
   it to be `→`'s proof with strictness threaded through; if it is not, that
   difference is worth reporting.
3. **`⊗` third** — `Smash.lean` (r0025). Its `sSup` branches on landing in
   `NonBotPair`, which is the subtlety to respect.

## Acceptance, ranked

1. All three conjuncts proved at `IsPRepresentable₂ U`.
2. Two of the three, with the third's obstruction located precisely.
3. `→` alone — it is the conjunct the other two are modelled on, and Lemma 23
   (the closure-notion function space over `P(ℕ)`) shows the paper treats it as
   the representative case.
4. A shared scheme that reduces all three to a single obligation, even if no
   conjunct is closed by it — this is what `isFinitaryProjection_sSup` did for
   the round that produced it.

**No new `sorry`.** An unproved conjunct is named in the docstring and omitted
from the conjunction, not stubbed.

## Process rules

1. Namespace `ScottDomains.PRepFun`. Import `PRep`; **do not add declarations to
   `PRep`** — agent4 is working in the same file's neighbourhood this round and a
   shared namespace is exactly how r0028 lost a round.
2. Edit/Write only. Never a heredoc, never `sed -i`.
3. One command per Bash call. Never chain, never `cd`.
4. Multi-step work becomes a script in `scripts/` — standing-authorized — but
   **check `scripts/` first and prefix any new script with your stream name**.
5. Build with `/home/milnes/projects/ScottLean4-agent3/scripts/compile.sh -r r0037`.
6. Read §7.3 of the PDF directly. The operator list was corrected twice by agents
   doing this; `pdftotext` renders `♮`/`♯`/`♭` as `\`/`]`/`[` and both `→` and
   `⇸` as `!`, so use `scripts/pdf-render.sh` and read the page as an image.
7. **This plan is not evidence.** The source wins; say so in the report.
8. Commit at every stopping point with
   `/home/milnes/projects/ScottLean4-agent3/scripts/gitcp.sh`. Do not push.
9. Report to
   `ScottDomains/reports/r0037-report-from-agent3-to-orchestrator-lemma-28-function-spaces.md`
   with `started`/`finished` and a conjunct-by-conjunct table: proved, refuted or
   open, with the hypotheses each carries.
