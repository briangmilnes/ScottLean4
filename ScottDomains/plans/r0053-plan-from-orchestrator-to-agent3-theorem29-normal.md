---
round: r0053
from: orchestrator
to: agent3
subject: theorem29-normal
date: 2026-0810-18:40
status: pending
related: reports/r0052-report-from-agent1-to-orchestrator-unproven-claims-as-sorry.md
---

# r0053 / agent3 — root hole 3: `Theorem29Normal`, the infinite case

## 0. Setup

Work in `/home/milnes/projects/ScottLean4-agent3` on branch `agent3`. That branch
is an ancestor of `main`, so start by resetting onto it:

    git -C /home/milnes/projects/ScottLean4-agent3 reset --hard main

The worktree has four untracked log files from r0047; leave them alone or commit
them separately — do not mix them into this round's commit.

Build only through `scripts/compile.sh -r r0053`. Never call `lake build`
directly, never chain shell commands, never `cd`, never `sed -i`. Anything
needing more than one command becomes a script in `scripts/`.

## 1. The hole

`ScottDomains/ScottDomains/Lemma30.lean:535`

```lean
theorem theorem29Normal_unproven : Theorem29Normal :=
  sorry
```

with, at line 514,

```lean
def Theorem29Normal : Prop :=
  ∀ (E : Type) [CompletePartialOrder E] [Domain E], IsBifinite E →
    ∃ f : ↥(compacts E) → Ainf,
      (∀ a b, f a ≤ f b ↔ a ≤ b) ∧ Set.range f ◁ (Set.univ : Set Ainf)
```

For every bifinite domain `E`, an order-reflecting map of `K(E)` into `A∞` whose
image is normal in `A∞`.

This is the **most consequential** of the three roots: 38 of the 49 conditional
consumers hang off it. It is the root of `Theorem29SecondAtDomains` (24
consumers, via `theorem_29_secondAtDomains_of_thm29Normal`), of
`Lemma30.Lemma30AtV` (via `R49.Agent6.lemma_30_atV_of_thm29Normal`), and thence
of `Colimit.Lemma30Arrow` (via `R45.Agent3.lemma_30_arrow_of_lemma30AtV`). All
three reductions are already proved; only the root is open.

## 2. What is proved and what is missing

| # | Fact | Where |
| - | ---- | ----- |
| 1 | the **finite-basis case** — `Theorem29Normal`'s conclusion when `K(E)` is finite | `A5Thm29Finite.theorem_29_normal_finiteBasis` |
| 2 | `A∞` is countable | `Colimit.instCountableAinf` |
| 3 | order-reflection into a countable type gives countability of `K(E)` | `countable_compacts_of_reflects` |
| 4 | the three reductions out of the root | named above, all proved |
| 5 | the tower argument — extend the finite case over the tower of finite normal subposets of `K(E)`, coherently, with the union image normal in `A∞` | **missing.** This is what [Gun87] carries and §7.4 does not (`Lemma30.lean:519-523`, `:490-493`) |

Item 5 is the round's work. `[Domain E]` is load-bearing and must stay: without
the paper's word "domain" the statement is not merely unproved but **refutable**
— `R45.Agent3.not_thm29NormalWithoutDomain`. Likewise
`R45.Agent3.not_thm29Second` refutes the unqualified `Colimit.Theorem29Second`.
Read `Lemma30.lean:480-540` before starting; it records both traps.

Also read `R47.Agent1.not_hasNormalRealizations_Ainf`: `A∞` does **not** have
normal realizations in `R46.Agent2.HasNormalRealizations`'s sense, so any route
that quietly needs that property of `A∞` is dead. Establish early whether your
intended construction needs it.

## 3. Order of attack

1. **The tower.** For `E` a bifinite domain, exhibit `K(E)` as a countable
   increasing union `N₀ ⊆ N₁ ⊆ ⋯` of finite subposets, each normal in `K(E)`
   (`◁`), with `⋃ Nᵢ = K(E)`. Bifiniteness plus countability of `K(E)` (item 3
   above, via `A∞`'s countability once you have any order-reflection — or
   directly from `IsBifinite`) is the input. Look first for an existing tower in
   `JungFinite.lean`, `IdealCompletion.lean`, `Colimit.lean`, or
   `BifiniteUniversal.lean` rather than building a second one.
2. **The step.** Given a normal embedding `fᵢ : Nᵢ → A∞` with normal image and
   `Nᵢ ⊆ Nᵢ₊₁` finite normal, extend to `fᵢ₊₁ : Nᵢ₊₁ → A∞` agreeing with `fᵢ`
   on `Nᵢ` and again with normal image. This is where `A∞`'s universality is
   spent, and where the finite case (item 1) is the base. State the step as its
   own theorem with explicit hypotheses — it is the reusable content.
3. **The limit.** The `fᵢ` cohere, so they define `f : K(E) → A∞`. Prove
   order-reflection pointwise (each pair lies in some `Nᵢ`) and normality of
   `Set.range f` in `A∞` — normality of a directed union of normal subsets is
   the lemma to isolate and prove separately; if it is false in general, find
   the extra condition the tower supplies and say which.
4. **Conclude** `Theorem29Normal`.

If the round ends before step 4, steps 1–3 are the deliverable, each as a named
proved theorem with its hypotheses explicit.

## 4. Where the code goes

Write a new module `ScottDomains/ScottDomains/Theorem29NormalInfinite.lean`,
named for its content per r0051, importing `Lemma30.lean` and `A5Thm29Finite.lean`.
**Do not edit `Lemma30.lean`** — the orchestrator does the one-line rewire of
`theorem29Normal_unproven` at merge time, and `Lemma30.lean` is the file the
whole Theorem 29 / Lemma 30 cluster reads.

Name the final theorem `theorem_29_normal` per the project's numbered-result
naming rule (`theorem_<N>[_<semantic>]`, never `thm`); name the step and limit
lemmas for what they say.

## 5. Honesty conditions

Rounds r0029–r0031 all failed on this §6 line, and r0045–r0049 each carved off a
piece. A false close here corrupts 38 downstream statements at once.

- **Never** discharge by `axiom`, by weakening the `def` (dropping `[Domain E]`,
  weakening `◁` to inclusion, or replacing order-reflection by monotonicity plus
  injectivity), or by adding a hypothesis that is the claim.
  `OrderEmbedding.ofMapLEIff` is the form the rest of `Colimit.lean` consumes and
  the statement's shape is fixed for that reason (`Lemma30.lean:504-506`).
- Do not introduce a new `Prop`-valued `def` that restates the goal and prove
  something from it — r0052's census counts those, and the round would show 73
  undischarged claims instead of 72.
- If a step needs a fact about `A∞` you cannot prove, name the fact and the goal
  rather than assuming it.

## 6. Acceptance criteria

| # | Criterion |
| - | --------- |
| 1 | `scripts/compile.sh -r r0053` reports 0 errors and 0 warnings other than `sorry` |
| 2 | the `sorry` count does not rise; it falls by 1 if and only if `Theorem29Normal` is genuinely proved |
| 3 | every new theorem's `#print axioms` shows no `sorryAx` |
| 4 | `Lemma30.lean` is byte-identical to `main` |
| 5 | no new undischarged `Prop`-valued `def` is added |
| 6 | committed with `scripts/gitcp.sh` on branch `agent3`; the push step reporting "no tracking information" is expected — do not push |
| 7 | report written to `ScottDomains/reports/r0053-report-from-agent3-to-orchestrator-theorem29-normal.md` with `started:`/`finished:` frontmatter |

The report states, quantitatively: which of steps 1–3 closed, the Lean statement
and axiom footprint of each new theorem, whether an existing tower was reused or
a new one built and why, the build log path, and — if the root is still open —
the exact remaining goal and the obstruction.
