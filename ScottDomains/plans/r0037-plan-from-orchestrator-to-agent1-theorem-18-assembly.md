---
round: r0037
from: orchestrator
to: agent1
subject: theorem-18-assembly
date: 2026-0807-11:09
status: pending
related:
  - plans/r0037-plan-from-orchestrator-to-orchestrator-last-four.md
---

# r0037 stream 1 — agent1 — Theorem 18, the assembly half

Worktree `/home/milnes/projects/ScottLean4-agent1`, branch `agent1`.
Namespace **`ScottDomains.JungFinite`**.

## The goal

`thm18` at `ScottDomains/Skeleton/Section6.lean:196` is the development's **only
remaining `sorry`**. Its route is Jung 1989's five steps, mapped in
`ScottDomains/Section62.lean:142–229`. Three of the five are done:

| # | Step | Status |
| -- | ---- | ------ |
| 1 | `[D → D]` continuous ⟹ `K(D)` has property m (Thm 1.37) | **agent2's stream this round** |
| 2 | `[D → D]` algebraic ⟹ bifinite or condition (vii) (Lem 2.13, Thm 2.14) | ✓ r0036, `JungSFP.lemma213`, `JungSFP.thm214` |
| 3 | `[D → D]` ω-algebraic ⟹ property M (Lem 2.17) | ✓ r0036, `JungSFP.lemma217` |
| 4 | property M ⟹ `U^∞(A)` finite (Lem 2.2) | **yours**, partly proved |
| 5 | property m + `U^∞` finite ⟹ bifinite (Thm 1.32) | ✓ r0028, `isBifinite_iff_mubClosure` |

**Your stream is step 4 and the glue that turns five steps into `thm18`.**

## Order of work

### 1. Jung's Lemma 1.29 — property M for pairs implies it for all finite sets

agent2's report names this as the cheapest remaining piece and the one that makes
`lemma217` directly consumable. `lemma217` concludes property M for the **pair**
`{a₁, a₂}`; `isBifinite_iff_mubClosure` needs it for every finite subset of
`K(D)`. Do this first — it is the shortest path to making the existing results
compose, and until it exists steps 3 and 5 do not meet.

### 2. Step 4 — Jung's Lemma 2.2

`Section62.lean:216–229` records exactly what is present and what is missing:

> Jung's Lemma 2.2 runs: Rado's Selection Theorem extracts from an infinite
> `U^∞(A)` an infinite chain `C ⊆ U^∞(A)`; a compact `f ≪ id` fixing `A` fixes
> all of `U^∞(A)`, hence fixes `⨆C`; but Corollary 1.36 gives `f(d) ≪ d` for
> every `d`, making `⨆C` compact, which an infinite strictly ascending chain
> cannot have as its least upper bound.

Already proved and yours to reuse:

- `apply_eq_self_of_mem_mubClosure` — a deflation fixing `u` fixes `U^∞(u)`; the middle step.
- `not_isCompactElement_of_isLUB_strictMono` — the terminal contradiction.
- `exists_isCompactElement_le` (r0031) — the deflation `f` itself.

Missing: **Rado's Selection Theorem** (or König's lemma against
`Domain.countable_compacts` — the section says either serves, so take whichever
is cheaper in Mathlib; check for `König`, `Nat.rec`-based chain extraction, or
`Set.Infinite` API before building one) and **Jung's Corollary 1.36**, `f(d) ≪ d`
for a compact `f ≪ id`.

### 3. Assemble `thm18`

With steps 1–5 in hand, `thm18` is an `exact`. **Stream 2 owns step 1**, so
until it merges, assemble `thm18` conditionally: prove
`JungFinite.thm18_of_propertyM` (or whatever hypothesis shape the assembly
actually needs) taking property m as an explicit hypothesis, exactly as
`lemma217` already takes `HasCompleteMub (compacts D) {a₁, a₂}`. **Do not edit
`Skeleton/Section6.lean`'s `sorry` unless every step is in your worktree** — if
stream 2 lands, the orchestrator closes it at merge.

## Two constraints that killed earlier attempts

Both recorded in `Section62.lean`, both still binding:

1. Any proof must spend countability of `K(D → D)` somewhere. **Without
   countability Theorem 18 is false**, the algebraic L-domains being the
   counterexamples. Step 3 is where r0036 spent it, via
   `Function.cantor_surjective`.
2. r0031's (★) is **equivalent** to Theorem 18, not below it. Do not reintroduce
   it.

## Acceptance, ranked

1. `thm18` proved outright — the `sorry` removed, development at **0 `sorry`**.
   Only possible if stream 2 also lands in your worktree, which it will not; so
   in practice this means item 2 plus a note that the assembly is one `exact`.
2. Lemma 1.29 and step 4 both proved, and `thm18_of_propertyM` assembled from
   steps 1–5 with property m as the one hypothesis. **This is the target.**
3. Lemma 1.29 alone, plus whichever of Rado/König and Corollary 1.36 lands.
4. Lemma 1.29 alone — it is short, it is the missing link between two proved
   results, and it is a complete deliverable.

**No new `sorry`.**

## Process rules

1. Namespace `ScottDomains.JungFinite`. Import `JungSFP`, `Section62`,
   `MinimalUpperBounds`; add declarations to none of them.
2. Edit/Write only. Never a heredoc, never `sed -i`.
3. One command per Bash call. Never chain, never `cd`.
4. Multi-step work becomes a script in `scripts/` — standing-authorized — but
   **check `scripts/` first and prefix any new script with your stream name**;
   r0036 lost a merge to two agents writing the same filename.
5. Build with `/home/milnes/projects/ScottLean4-agent1/scripts/compile.sh -r r0037`.
6. Read Jung 1989 in `ScottDomains/papers/` directly. `scripts/pdf-render.sh`,
   `pdf-section.sh`, `pdf-crop.sh` and `pdf-find-page.sh` already exist for this.
7. **This plan is not evidence.** The source wins; say so in the report.
8. Commit at every stopping point with
   `/home/milnes/projects/ScottLean4-agent1/scripts/gitcp.sh`. Do not push.
9. Report to
   `ScottDomains/reports/r0037-report-from-agent1-to-orchestrator-theorem-18-assembly.md`
   with `started`/`finished`, which of Rado/König you chose and why, and exactly
   what remains between your work and `thm18`.
