---
round: r0031
from: orchestrator
to: agent1
subject: computable-functions
date: 2026-0806-20:20
status: pending
---

# r0031 agent1 — The paper's *computable function*, the last missing definition

## Goal

§3.2 of Gunter & Scott defines a **computable function** on an effectively
presented domain. It is the one definition in the paper this development does not
have, and closing it completes the definition list.

## The blocker that turned out not to exist

`docs/PaperInventory.md` recorded, since r0022, that this could not be built:
"it needs recursively enumerable, and Mathlib v4.32.2 has no `RePred` or
equivalent (grep finds none)". **That grep used the wrong capitalization.**
Mathlib has:

| # | Declaration | Location |
| -- | ----------- | -------- |
| 1 | `REPred {α} [Primcodable α] (p : α → Prop)` | `Mathlib/Computability/RE.lean:157` |
| 2 | `ComputablePred` | `Mathlib/Computability/RE.lean:129` |
| 3 | `Partrec.dom_re` — the domain of a partial recursive function is r.e. | same file |
| 4 | `ComputablePred.to_re` | same file |

Read that module before anything else. Verify the claim yourself and say in your
report whether `REPred` is in fact what the paper's "recursively enumerable"
means here; if it is not, that is a finding and the definition may still be
blocked.

## Worktree and ownership

Work only in `/home/milnes/projects/ScottLean4-agent1`, branch `agent1`. Never
touch `/home/milnes/projects/ScottLean4` or a sibling worktree.

You own one new file: `ScottDomains/ScottDomains/ComputableFunction.lean`.
Everything else is read-only. If a shared module genuinely must change, stop and
report rather than change it.

**Every declaration goes in `namespace ScottDomains.Computable`.** Three sibling
agents run this round. In r0028 two agents each defined `isClosure_sSup` and
`IsClosure.apply_sSup_of_directed`; `lake build` passed at 971 jobs because no
module imported both, and the clash surfaced only when an axiom audit finally
imported the pair. r0029 used a namespace per agent and had zero collisions.

## What to read first

| # | File | Why |
| -- | ---- | --- |
| 1 | `ScottDomains/EffectivePresentation.lean` | `EffectivePresentation` (r0022) — the enumeration `d : ℕ → K(D)` with its two decidability conditions, which is what a computable function is defined relative to |
| 2 | `Mathlib/Computability/RE.lean` | `REPred`, `ComputablePred`, and their API |
| 3 | `ScottDomains/Domain.lean`, `WayBelow.lean` | `K(D)`, `IsCompactElement`, `≪` |
| 4 | `papers/Gunter Scott 1990.pdf`, §3.2 | the definition. Extract it with `pdftotext -layout` and quote it — do not work from the inventory's paraphrase. r0029 found the paraphrase of `Pf` had lost a load-bearing condition |

## Deliverables

1. The paper's definition of a computable function `f : D → E` between
   effectively presented domains, stated with the paper's wording quoted in a
   docstring, and its formalization against `REPred`.
2. Whatever the paper proves or asserts about it in §3.2 that is cheap to
   discharge — for instance that a computable function is continuous, or that the
   identity and composites are computable. State what you proved and what you did
   not attempt.
3. If the definition requires a `Primcodable` structure on `K(D)` that the
   development does not supply, build it from `EffectivePresentation`'s
   enumeration and say so.

## Rules

1. Build with `scripts/compile.sh` from the worktree root. Never prefix a build
   with the `timeout` command; raise your Bash tool's own timeout instead.
2. Errors **and** warnings to zero. No `set_option` to silence a linter.
3. Edit/Write only — never `sed -i`, heredocs, or shell redirection into a file.
4. Never weaken a statement to make it provable. If the paper's definition cannot
   be expressed against `REPred`, say precisely why and what is missing.
5. Commit with `scripts/gitcp.sh` on branch `agent1`. **Do not push, do not set an
   upstream**; the "no tracking information" failure is expected.

## Report

Write `reports/r0031-report-from-agent1-to-orchestrator-computable-functions.md`:
the definition and the paper's wording it formalizes; whether `REPred` was the
right notion; what else you proved, kernel-accepted, with `#print axioms` showing
no `sorryAx`; the exact `sorry` count; the verbatim final `lake build` line; your
commit SHAs; and any obstacle.
