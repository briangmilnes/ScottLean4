---
round: r0042
from: orchestrator
to: orchestrator
subject: clear-the-sorry
date: 2026-0808-13:57
status: pending
related:
  - ScottDomains/Section62.lean
  - ScottDomains/JungSFP.lean
  - ScottDomains/JungFinite.lean
  - ScottDomains/JungNets.lean
---

# r0042 — Clear the development's last `sorry`

One `sorry` remains: `thm18` at `Skeleton/Section6.lean:197` — *if `D` and
`D → D` are domains then `D` is bifinite.* It is the development's oldest open
result; five rounds have worked on it.

## Exactly what is left

Jung 1989's five-step route is mapped in `Section62.lean:142–229`. Steps 2, 3, 4
and 5 are proved. What remains is **two named propositions**, and nothing else:

| # | Proposition | Where | Status |
| -- | ----------- | ----- | ------ |
| 1 | `JungFinite.FixedPointOfCompactDeflationIsCompact` — Jung's **Corollary 1.36**, `f ≪ id` compact ⟹ `f(d) ≪ d` | `JungFinite.lean` | four lines in Jung; needs his Proposition 1.34 |
| 2 | `JungNets.Thm137` — Jung's **Theorem 1.37**, a dcpo with continuous function space is **bicomplete** | `JungNets.lean` | blocked on **Iwamura's lemma**, which Mathlib does not have |

`scripts/check-thm18-composition.sh` elaborates the composite of the two into
`IsBifinite α` on `[propext, Classical.choice, Quot.sound]`. **So the reduction is
kernel-checked, but only in a script** — r0040's agent4 found that no *library
declaration* records it. That is the one certain deliverable of this round.

## What is known and must not be re-derived

* **Theorem 1.37 says "bicomplete", not "has property m".** r0037 corrected this
  from the source (Jung p. 50, read directly). Property m is a separate inference
  inside Jung's Theorem 2.3 proof that he never proves, and `JungNets` proves it
  in full by Zorn downwards. Do not conflate them again.
* **Without countability Theorem 18 is false**, the algebraic L-domains being the
  counterexamples (Abramsky & Jung 4.3.4 vs 4.3.5). Countability is spent exactly
  once, in `JungSFP.lemma217`.
* **r0031's (★) is equivalent to Theorem 18, not below it.** Do not reintroduce
  it.
* **The restriction route to Corollary 1.36 fails**, and r0037's agent1 recorded
  precisely why in the predicate's docstring: restricting a compact deflation to
  `↓c` is cheap, but `IsCompactElement (f|↓c)` does not follow — extending a
  directed family by the identity outside `↓c` is monotone only below `id↓c`, and
  extending by the constant `c` is always monotone but then `f ⊑ ext(h)` fails
  off `↓c`. Jung needs a retraction, not a restriction. **Do not retry it.**
* **Mathlib measurements** (r0037, agent2): zero hits for `Iwamura|Markowsky`;
  `ChainCompletePartialOrder` exists in `BourbakiWitt.lean` with an instance to
  `OmegaCompletePartialOrder` and **none** to `CompletePartialOrder`; no
  ordinal-indexed nets over posets.

## The five streams

| # | Agent | Namespace | Target |
| -- | ----- | --------- | ------ |
| 1 | agent1 | `ScottDomains.JungCor136` | Jung's Corollary 1.36, and Proposition 1.34 beneath it |
| 2 | agent2 | `ScottDomains.Iwamura` | Iwamura's lemma / chain-complete ⟹ directed-complete |
| 3 | agent3 | `ScottDomains.JungBicomplete` | Theorem 1.37 **given** Corollary 1.3: the retraction onto `A ∪ αᵒᵖ`, Proposition 1.22, interpolation, the `g_β` family |
| 4 | agent4 | `ScottDomains.PropertyM` | **the bypass** — can property m at *pairs* be had without Theorem 1.37 at all? |
| 5 | agent5 | `ScottDomains.Thm18` | the assembly as a library theorem, the statement audit, and `thm18` itself if the others deliver |

**Stream 4 is the hedge and is not busy-work.** `JungSFP.lemma217` needs
`HasCompleteMub (compacts D) {a₁, a₂}` — property m at a *pair*, not at every
finite set. Theorem 1.37 delivers far more than that. If a cheaper argument
reaches the pair case, the whole Iwamura dependency drops. Abramsky & Jung §4.3,
Spreen (MSCS 15, 2005) and this development's own `MinimalUpperBounds` are the
places to look.

**Stream 5 can deliver regardless of 1–4.** Turning the script's composite into a
declaration is unconditional work, and auditing that `thm18`'s statement is the
paper's is overdue — the statement has never been checked against the PDF by
anyone.

## Dependencies

All merge-order, none launch-order. Streams 1, 2 and 4 are independent. Stream 3
assumes Corollary 1.3 as a hypothesis rather than waiting on stream 2. Stream 5
states the assembly against the two `Prop`s as they stand today and tightens at
merge.

## Expected outcome, stated honestly

| # | Case | Result |
| -- | ---- | ------ |
| 1 | Stream 5 only | the reduction becomes a library theorem; `sorry` stays 1 |
| 2 | + stream 1 | one of the two propositions discharged; `sorry` stays 1 |
| 3 | + stream 4 | property m obtained cheaply; **`sorry` → 0**, Iwamura never needed |
| 4 | + streams 2 and 3 | Theorem 1.37 proved outright; **`sorry` → 0** |

**Case 4 is the least likely.** Iwamura's lemma is a transfinite-induction result
on cardinality that Mathlib has never carried, and Theorem 1.37 then needs four
more absent ingredients. Case 3 is the one worth hoping for. Case 1 is
guaranteed. A round that ends at case 1 or 2 has still moved the development,
and **no stream may write a `sorry` to reach a better-looking number** — the
count must be 1 or 0 at the end, never 2.

## Process rules

1. Namespace per agent, as assigned.
2. `Edit`/`Write` only — no heredocs, **no `sed -i`**.
3. One command per Bash call; never chain; never `cd`.
4. New scripts in `scripts/` prefixed with the stream name.
5. Build with your worktree's `scripts/compile.sh -r r0042`; errors and
   non-`sorry` warnings to zero.
6. **Read Jung 1989 directly** — it is in `ScottDomains/papers/`. Abramsky & Jung
   1994 and Plotkin's Pisa notes are there too.
7. **The plan is not evidence.** Every round since r0034 has produced corrections
   to its own plan; r0041 produced three, including one to an argument I took
   from the paper. Contradicting this from the source is expected.
8. Commit at every stopping point; do not push.

## Orchestrator steps

1. Commit this plan; fast-forward the worktrees.
2. Launch five agents.
3. Verify each: build, `counts.sh`, `axioms.sh`, and **read the statement**.
4. Merge one at a time; composition check over every new module together.
5. If `thm18` closes: re-run `scripts/axioms.sh` on it and on every result that
   depends on it, and update `docs/PaperInventory.md` rows 2, 2d and 6 plus
   `docs/PropertiesVsTheorems.md` from measured counts.
