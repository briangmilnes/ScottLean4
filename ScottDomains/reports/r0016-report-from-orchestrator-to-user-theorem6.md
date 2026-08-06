---
round: r0016
from: orchestrator
to: user
subject: theorem6
date: 2026-0806-15:10
started: 2026-0806-15:06
finished: 2026-0806-15:10
related:
  - plans/r0016-plan-from-orchestrator-to-orchestrator-theorem6.md
  - reports/r0015-report-from-orchestrator-to-user-normal-projection.md
---

# r0016 — Theorem 6 proved

**Fourth of the 28 numbered results.** `ScottDomains/Theorem6.lean`: 193 lines,
0 `sorry`, 0 warnings. Elapsed 4 minutes.

| # | Criterion | Measurement |
| -- | --------- | ----------- |
| 1 | Builds | 0 errors, 0 warnings |
| 2 | Nothing unproved | 0 `sorry`, no `sorryAx` |
| 3 | Theorem 6 complete | both round trips and both monotonicity directions, as `ScottDomains.theorem6` |

## What the round supplied

| # | Component | Where |
| -- | --------- | ----- |
| 1 | `p_N` well defined, continuous, a projection | r0015 |
| 2 | `im(p_N) ∩ K(D) = N` | r0015 |
| 3 | both maps monotone | r0015 |
| 4 | `im(p_N)` is **algebraic** | r0016 |
| 5 | its basis is `N`, hence countable — so `p_N` is **finitary** | r0016 |
| 6 | `p_{im(p) ∩ K(D)} = p` | r0016 |
| 7 | assembled | r0016 |

The engine of 4–6 is a pair of transfer lemmas across the subtype `↥(im p)`:
r0014's `isLUB_val_image` and its converse here. With the identification
`val '' (compactsBelow y) = N ∩ ↓y` — Lemma 5 says which elements are compact,
r0015 says which elements those are — every statement about `im(p_N)` becomes a
statement about `N` inside `D`, where r0015's lemmas apply unchanged.

Theorem 6 is stated as the five facts constituting the isomorphism rather than as
a bundled `OrderIso` between subtypes, for the same reason Lemma 4.4 was: that is
the form later results cite, and it avoids subtype-order plumbing that buys
nothing.

## Elaboration failures

Three. Two were the recurring instance-overlap diagnostic — `[IsAlgebraic α]`
alongside `[Domain α]`, which implies it — fixed by moving the file's `variable`
line down into per-section declarations, so each result carries exactly the
hypotheses it uses. The third was a genuine dependent-rewrite failure: `rw` on
`N` could not build a motive because `c`'s *type*, `↥(Set.range ⇑(normalHom hN))`,
mentions `hN` which mentions `N`. Rewriting in a hypothesis about membership
instead of in the goal sidesteps it, since the set being rewritten does not occur
in any type.

## Totals

Fourteen modules, 2111 lines, 108 theorems, 0 `sorry`, 0 warnings.
Numbered results **4 of 28** — Lemmas 4 and 5, Theorems 6 and 7. Prose claims
**11**. Definitions **7 of ≈13**.

§3.1 is now fully formalized apart from effective presentations (§3.2).
