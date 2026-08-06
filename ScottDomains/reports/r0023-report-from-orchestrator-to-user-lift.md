---
round: r0023
from: orchestrator
to: user
subject: lift
date: 2026-0806-16:10
started: 2026-0806-16:04
finished: 2026-0806-16:10
related:
  - reports/r0022-report-from-orchestrator-to-user-effective-presentation.md
---

# r0023 — The lift `D⊥` as a cpo

`ScottDomains/Lift.lean`: 98 lines, 0 `sorry`, 0 warnings, built on the first
attempt. Elapsed 6 minutes.

| # | Criterion | Measurement |
| -- | --------- | ----------- |
| 1 | Builds | 0 errors, 0 warnings |
| 2 | Nothing unproved | 0 `sorry`, no `sorryAx` |
| 3 | Reuses Mathlib's order | `WithBot α` supplies the order, the coercion and `⊥`; only the cpo structure is new |

## The one step that needs an argument

For `s ⊆ D⊥`, let `t = {a : D | ↑a ∈ s}`. If `t` is empty then `s ⊆ {⊥}` and the
supremum is `⊥`; otherwise it is `↑(⨆t)`. The step with content is that **`t`
inherits directedness**: given `↑a₁, ↑a₂ ∈ s`, directedness of `s` produces some
`c ∈ s` above both, and `c` cannot be the adjoined bottom, because `↑a₁ ≤ ⊥` is
false in `WithBot`. So `c` is again a coercion and its preimage is in `t`.

That single observation — `WithBot.not_coe_le_bot` — is what makes the lift a cpo
rather than merely a pointed order, and it is the only place the adjoined element
has to be reasoned about separately.

`WithBot.recBotCoe` handles the case analysis throughout, which keeps the two
branches visible rather than buried in `Option` pattern matches.

## Where the case split lands

As with `ScottHom` and `↓a`, `SupSet` totality forces a split; here it is on
whether the base `t` is empty. The pattern is now consistent across the
development:

| # | Construction | Split on |
| -- | ------------ | -------- |
| 1 | `ScottHom α β` | continuity of the pointwise supremum |
| 2 | `↓a` | whether the supremum stays below `a` |
| 3 | `D⊥` | whether the base is empty |
| 4 | `im(p)` | none — `p` applied to the result always lands in range |
| 5 | `D × E` | none — coordinatewise suprema are always correct |

## Totals

Twenty modules, 2921 lines, 129 live theorems (+6 commented out), 0 `sorry`,
0 warnings. Numbered results **7 of 29**. Prose claims **11**. Definitions
**8 of ≈13**.

## Next

The **strict function space** `D →⊥ E`. The paper claims it is a cpo (p. 5,
"the set of strict continuous functions `D → E` is also a cpo"), which would be
prose claim 12, and Lemma 9 quantifies over it throughout. It is a subtype of
`ScottHom` and so brings its own case split, which is why it is a round rather
than an addendum to this one. After that: the smash product `D ⊗ E`, then Lemma 9.
