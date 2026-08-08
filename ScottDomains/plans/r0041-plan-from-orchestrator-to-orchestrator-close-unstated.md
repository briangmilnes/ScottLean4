---
round: r0041
from: orchestrator
to: orchestrator
subject: close-unstated
date: 2026-0808-12:59
status: pending
related:
  - analyses/property-coverage.2026-0808-11:59.orchestrator.md
  - docs/PaperInventory.md
---

# r0041 — State and prove the paper properties the development never wrote down

r0040 measured **62 of the paper's 239 properties as having no Lean statement at
all**. This round attacks them.

## The split is by missing construction, not by paper section

r0040 was partitioned by section because it was a survey. That is the wrong
partition for *building*, because the 62 gaps do not cluster by where they are
stated — they cluster by **what single object is missing**. Four constructions
account for 33 of the 62, and each one unblocks a whole group at once:

| # | Missing construction | Unblocks | Also unblocks, beyond the 62 |
| -- | -------------------- | ---: | ---- |
| 1 | a **flat cpo** — `N⊥`, `T`, `ω⊤` are never constructed; `ℝ` occurs 0 times in the package | 16 | `(T × T)♮` not bounded complete, §6's opening motivation |
| 2 | **morphism-level algebra** — no general `f × g`, `f ⊗ g`, `f ⊕ g`, `f + g`, no multiary notation | 11 | — |
| 3 | a **functorial action on a powerdomain** — no `f♮`/`f♯`/`f♭` anywhere | 2 | **Lemma 28's `()♯` and `()♭`**, the two conjuncts keeping a *numbered* result at 7 of 9 |
| 4 | **an instantiated effective presentation** — `EffectivePresentation` is never instantiated at *any* type | 4 | **Theorem 7's second sentence**, the only numbered property with no statement |

Row 3 and row 4 each reach a numbered result, so they carry more weight than
their row counts suggest.

## Scope: 39 of 62, and the other 23 named

**This plan does not attempt all 62, and says so rather than discovering it
later.** The five streams below target **39**. The remaining 23 are deferred with
reasons:

| # | Deferred | Count | Why |
| -- | -------- | ---: | --- |
| 1 | §7.2's λ-calculus equations and the two independence claims | 5 | needs λ-term syntax with binding and substitution; `Comb` is deliberately variable-free. A development of its own |
| 2 | §7.1/§7.3 solvability and representability claims — `T ≅ T + T` by a binary tree, `X ≅ X × I⊤`, `X ≅ N⊥ + (X → X)`, the `B`-universality claim, the `i : x ↦ ↑x` properties | ~15 | each needs a carrier built first; several become cheap *after* stream 1 lands the flat cpo, so they are better attempted next round than guessed at now |
| 3 | scattered §2/§4 remarks | ~3 | low value, no shared blocker |

If a stream finishes early it should take deferred rows from group 2 in its own
section, and say which.

## The five streams

| # | Agent | Namespace | Target | Rows |
| -- | ----- | --------- | ------ | ---: |
| 1 | agent1 | `ScottDomains.Flat` | the flat cpo, then §5's `N⊥` powerdomain calculations and `(T × T)♮` | 16 |
| 2 | agent2 | `ScottDomains.Morphism` | `f × g`, `f ⊗ g`, `f ⊕ g`, `f + g`, their functor laws, multiary forms | 11 |
| 3 | agent3 | `ScottDomains.PowerdomainMap` | `f♮`, `f♯`, `f♭` and their laws | 2 (+2 Lemma 28 conjuncts) |
| 4 | agent4 | `ScottDomains.Effective` | instantiate `EffectivePresentation`; **Theorem 7's second sentence** | 4 |
| 5 | agent5 | `ScottDomains.Kleene` | bundle `kleeneFix` as a `ScottHom`; `fix` is a uniform fixed-point operator; §2.2's applications | 6 |

Namespaces are per agent, as since r0029 — zero collisions under that rule, two
before it.

## Dependencies

**Stream 1 is the keystone and everything else is independent of it.** Streams
2–5 must not wait on the flat cpo; if one of them wants a concrete witness, it
should state its result generally and leave instantiation to the merge. Stream 3
should coordinate with nothing: `Powerdomain/{Hoare,Smyth,Plotkin}.lean` have
existed since r0029 and the action is a new file over them.

## Acceptance, per stream

Ranked, and the same shape as r0034 onwards: **land the largest complete item,
never a `sorry`.**

1. Every targeted row stated **and proved**.
2. Every row **stated**, with the open ones as named `Prop`s or explicit
   hypotheses — a statement is the round's minimum unit of value, because r0040's
   whole finding is that unstated results are invisible.
3. The enabling construction alone, with its `Domain`/`CompletePartialOrder`
   instances and a non-degeneracy witness.

**Do not introduce a `sorry`.** The development has exactly one, `thm18`, and it
must still have exactly one at the end of this round. An unproved statement is a
named `Prop` or a docstring obstruction, in the form `Section62.lean` and
`Colimit.lean` already use.

## Process rules

1. **Namespace per agent**, as assigned.
2. `Edit`/`Write` only — no heredocs, **no `sed -i`**.
3. One command per Bash call; never chain; never `cd`.
4. New scripts in `scripts/` prefixed with the stream name, after checking what
   is there.
5. Build with your worktree's `scripts/compile.sh -r r0041`. Drive errors and
   non-`sorry` warnings to zero.
6. **Read the paper for the statement.** r0040's per-property tables give the
   exact sentence and printed page for every row — start from
   `reports/r0040-report-from-agentN-…`, then check the sentence against the PDF.
7. **The plan is not evidence.** r0034 had four wrong stream descriptions, r0036
   three, r0037 three, r0039 two, r0040 several conjunct counts. Contradicting
   this plan from the paper is expected behaviour.
8. Commit at every stopping point with your worktree's `scripts/gitcp.sh`; do not
   push.

## Orchestrator steps

1. Commit this plan; fast-forward the worktrees.
2. Launch five agents.
3. On each report: build, `scripts/counts.sh`, `scripts/axioms.sh` on the new
   headline declarations, and **read the statement** against the paper's sentence
   — a row claimed as stated is a claim to check.
4. Merge one branch at a time; composition check with `scripts/axioms.sh -i` over
   every new module together.
5. Update `PaperInventory.md` rows 2e and 3 and the property-coverage analysis
   from the measured result — how many of the 62 are now stated, and how many
   proved.
