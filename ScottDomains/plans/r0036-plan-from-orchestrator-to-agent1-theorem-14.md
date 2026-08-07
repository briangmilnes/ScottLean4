---
round: r0036
from: orchestrator
to: agent1
subject: theorem-14
date: 2026-0807-08:32
status: pending
related:
  - plans/r0036-plan-from-orchestrator-to-orchestrator-five-way-open-results.md
---

# r0036 stream 1 — agent1 — Theorem 14

Worktree `/home/milnes/projects/ScottLean4-agent1`, branch `agent1`.
Namespace **`ScottDomains.SFP`**.

## The goal

`ScottDomains/Skeleton/Recovered.lean:257` — one of the development's two
remaining `sorry`:

    theorem thm14 : IsBifiniteViaProjections α ↔ Domain α ∧ IsBifinite α

`IsBifiniteViaProjections α` is the paper's own §6 wording: the finitary
projections of finite image are countable, directed, and join to `ScottHom.id`.
The right-hand side is `Domain α ∧ IsPlotkinOrder (compacts α)`, which the whole
of §6 has used as the working definition. Theorem 14 is what licenses that
substitution.

This is **Plotkin's SFP characterization**. Neither direction rearranges the
other's data. r0034's plan asserted the obstacle was definitional — that
supplying `IsBifiniteViaProjections` made it `P ↔ P` no longer, and the rest was
routine. That was wrong, and r0034's agent1 measured why: four gaps, written into
`thm14`'s docstring at `Recovered.lean:223–256`. **Read that docstring first.**

## Order of work — gap 2 is the bridge

| # | Gap | What is missing | Schedule |
| -- | --- | --------------- | -------- |
| 1 | The `FpLattice` section of `FinitaryProjectionPoset.lean` sits under `variable [Domain α]` | `Domain α` is what the forward direction must *conclude*, so `toFp`, `Fp.le_iff_fpBasis_subset`, `isCompactElement_toFp_of_finite`, `isLUB_compactsBelow_fp` are all unavailable there | after 2 |
| 2 | **`Set.range ⇑(toFp hN) = N` for finite normal `N`** | `Fp(D)`'s compactness results speak of `(fpBasis q).Finite` = `range q ∩ K(D)` finite; `finiteImageProjections` asks for `(Set.range ⇑q).Finite`. The bridge says a finite normal subposet is closed under the directed suprema its own projection forms | **first** |
| 3 | `IsLUB` in `↥(Fp α)` is strictly weaker than `IsLUB … ScottHom.id` in `ScottHom α α` | an upper bound of `M` in the function space need not be a finitary projection; this is a second appeal to approximation, not a coercion | after 2 |
| 4 | Two finite-combinatorial lemmas | (a) a nonempty finite directed set contains its greatest element — this is what makes each element of a finite image compact; (b) a finite subset of a directed set has an upper bound *inside* the set — this produces the single projection whose image contains a given finite set of compacts | any time; cheap, do them early |

Gaps 1 and 3 both route through 2. Do not start on 1 or 3 before 2 is proved or
shown false.

The docstring records that the **forward** direction is routine given gap 4: each
`p ∈ M` has compact image, `{p x | p ∈ M}` is a directed set of compacts with
least upper bound `x` giving `IsAlgebraic`, `K(D) ⊆ ⋃_{p ∈ M} range p` gives
countability, and a single `p` fixing a finite set of compacts gives the Plotkin
order via `IsFinitaryProjection.isNormalIn_compacts`. **The converse is where 1–3
bite.** So the forward direction is the cheap half — land it first as a separate
named theorem if the biconditional stalls.

## What generalizing the `FpLattice` section costs

Gap 1 says the machinery is stated at `[Domain α]`. Before rewriting those
declarations, measure which of them actually *use* algebraicity or countability
of `K(α)` and which merely inherit the `variable`. The r0032 and r0034 rounds both
found results proved at strictly weaker hypotheses than declared (`thm25` at cpo
strength, `thm12` needing only `[IsAlgebraic D]`). If the four lemmas gap 1 names
survive at `[CompletePartialOrder α]`, gap 1 dissolves into a `variable` move and
costs nothing. Report the measurement either way — it is worth knowing even if the
answer is no.

## Acceptance, ranked

1. `thm14` proved, `sorry` removed. Development goes to 1 `sorry`.
2. The forward direction alone, as `SFP.thm14_forward`, plus gap 2's bridge lemma
   and gap 4's two combinatorial lemmas, with the converse left as the stated
   obstruction — `sorry` count unchanged but the gap list shortened and measured.
3. Gap 2's bridge lemma alone, `SFP.range_toFp_eq`, with a written statement of
   what it unblocks.

Land the largest of these that is complete. **Do not leave a new `sorry`** — an
unproved statement goes in the module docstring as an obstruction, in the form
r0034's `Section62.lean` used.

## Process rules

1. Namespace `ScottDomains.SFP` for every new declaration.
2. `Edit`/`Write` only. Never a heredoc, never `sed -i`.
3. One command per `Bash` call. Never chain with `&&`, `;` or `|`. Never `cd` —
   use absolute paths.
4. Multi-step work becomes a script in `scripts/` — standing-authorized, write it
   without asking.
5. Build with `/home/milnes/projects/ScottLean4-agent1/scripts/compile.sh -r r0036`.
6. Read the PDF (`ScottDomains/papers/Gunter Scott 1990.pdf`) rather than a
   paraphrase. Plotkin's Pisa notes are also in `papers/` and are the origin of
   the SFP characterization.
7. **This plan is not evidence.** If the source contradicts it, the source wins;
   say so in the report.
8. Commit on `agent1` at every stopping point, including with build errors, using
   `/home/milnes/projects/ScottLean4-agent1/scripts/gitcp.sh "<message>" <paths>`.
   Do not push — "no tracking information" is the expected outcome.
9. Write `reports/r0036-report-from-agent1-to-orchestrator-theorem-14.md` with
   `started:` and `finished:` in frontmatter, the measured `sorry` count before
   and after, and which of the four gaps closed.
