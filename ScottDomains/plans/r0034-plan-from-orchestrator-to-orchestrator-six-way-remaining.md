---
round: r0034
from: orchestrator
to: orchestrator
subject: six-way-remaining
date: 2026-0806-22:30
status: pending
related:
  - plans/r0033-plan-from-orchestrator-to-orchestrator-session-restart.md
  - docs/PaperInventory.md
  - docs/Performance.md
  - docs/StatementRecovery.md
---

# r0034 — Six-way plan for the ten outstanding numbered results

Six agents, one stream each, covering **every** result the paper states and the
development has not proved. Nothing in the paper's numbered list is left
unassigned.

## Baseline, measured

`main` at `1c9f38f`, working tree clean, all five existing worktrees
fast-forwarded to it (`scripts/worktree-sync.sh`).

| # | Quantity | Value |
| -- | -------- | ----- |
| 1 | Build | `Build completed successfully (1072 jobs).`, 0 errors, 0 diagnostics, 0 non-`sorry` warnings |
| 2 | Numbered results complete | **18 of 29** (Thm 2 excluded from the denominator: Mathlib reuse) |
| 3 | Not complete | **10** — Lem 9, Lem 10, Thm 14, Lem 17, Thm 18, Thm 26, Thm 27, Lem 28, Thm 29, Lem 30 |
| 4 | Settled but counted in neither column | **Thm 16** — one conjunct proved, one refuted |
| 5 | `sorry` | **8**, in `Skeleton/Recovered.lean` (7) and `Skeleton/Section6.lean` (1) |
| 6 | Modules / lines / theorems | 45 / 14048 / 659 |

## Why six, and what six costs

`docs/Performance.md` measures five constraints and recommends **4 to 6 agents**.
At six the binding constraint is not hardware — five agents drew about 1.2 of 20
cores, a 9% duty cycle — but two process limits:

| # | Constraint | Binds at | Mitigation in this round |
| -- | ---------- | -------- | ------------------------ |
| 1 | Declaration collisions | ~6 agents | namespace per agent, `ScottDomains.<Stream>`; zero collisions across r0029–r0032 under this rule |
| 2 | Review bandwidth | ~5 agents | streams 1, 2 and 6 retire `sorry`s and add conjuncts against existing statements — small diffs. Only streams 3–5 are new construction |
| 3 | Memory | ~5 concurrent builds | agents build rarely and not in lockstep; 2.3 GiB PSS each against a 31 GiB machine |

**Worktrees: six, all ready.** `agent6` was created for this round with
`scripts/init-worktree.sh 6` — the orchestrator running it on the user's behalf,
which GRASE rule 2.5 permits. All six are at `1c9f38f`, clean, with
`ScottDomains/.lake/packages` symlinked at the main checkout's copy (327 MiB
each, not ~7 GiB). Verified by `scripts/worktree-sync.sh`, not asserted.

## The six streams

### Stream 1 — agent1 — Lemma 9 and Theorem 14

Namespace `ScottDomains.Isomorphism`. Files: `Skeleton/Recovered.lean` (7
`sorry`), plus a new module for the proofs.

Lemma 9's six isomorphism laws over `D, E, F`, statements recovered in r0032:

| # | Conjunct | Note |
| -- | -------- | ---- |
| 1 | `D⊗E ≅ E⊗D` | certain |
| 2 | `(D⊗E)⊗F ≅ D⊗(E⊗F)` | certain |
| 3 | `(E⊕F) ◦→ D ≅ (E ◦→ D) × (F ◦→ D)` | **false as printed** |
| 4 | `D ◦→ (E ◦→ F) ≅ (D⊗E) ◦→ F` | certain |
| 5 | `D⊗(E⊕F) ≅ (D⊗E)⊕(D⊗F)` | **false as printed** |
| 6 | `D⊥ ◦→ E ≅ D → E` | certain |

Items 3 and 5 are refuted by cardinality at `D = E = Prop`, `F = Prop × Prop`;
`docs/StatementRecovery.md` carries the argument as prose. Put both under the
kernel as explicit negations, following the `lem10_smash` precedent — this closes
open decision 2 of r0033. `◦→` is the strict function space (`StrictHom.lean`,
r0024); it and `→` both extract from the PDF as `!`, so check every occurrence
against the decoded stream, not the `pdftotext` output.

Theorem 14 is the equivalence of the paper's two characterizations. The blocker
is not mathematical: `Bifinite.lean` *defines* `IsBifinite` as condition 2, which
would make the theorem `P ↔ P`. `IsBifiniteViaProjections` supplies condition 1
from the paper's own definition; `thm14` is the equivalence between them.

**Acceptance:** `Skeleton/Recovered.lean` at 0 `sorry`; development `sorry` count
8 → 1; Lem 9 and Thm 14 both complete.

### Stream 2 — agent2 — complete Lemma 10 and Lemma 17

Namespace `ScottDomains.ClosureProperties`. Six conjuncts, all against existing
statements:

- **Lemma 10's `+` conjunct.** `+` is a *different operator* from `⊕`, which is
  already proved. Expected cheap via `D + E = D⊥ ⊕ E⊥`. Takes Lem 10 to 7 of 7.
- **Lemma 17's `◦→` and `+` conjuncts**, and its **three powerdomain conjuncts**
  `D♮`, `D♯`, `D♭`. The powerdomains have existed since r0029
  (`Powerdomain/{Hoare,Smyth,Plotkin}.lean`, each `IdealCompletion (Pf K(D))`
  with compacts characterized as principal ideals); they were dropped from the
  extraction with their glyphs, not because they were unavailable. Takes Lem 17
  to 10 of 10.

`ContinuousAlgebra.lean` (r0032, 1254 lines, 0 `sorry`) supplies the free-algebra
machinery for the powerdomain conjuncts, including that each free algebra models
its own theory.

**Acceptance:** two results move partial → complete; count 18 → 20 of 29.

### Stream 3 — agent3 — §7.3's universal domain `U`, then Theorem 27

Namespace `ScottDomains.Dyadic`. New construction.

Build `U` as the ideal completion of the dyadic half-open intervals. Theorem 11
(r0028, `IdealCompletion.thm11`) already gives: the ideal completion of a
*countable pre-order* is a domain — so `U`'s `Domain` instance is Thm 11 applied
to a pre-order that must be defined and shown countable, not a fresh development.

Then **Theorem 27**: every bounded-complete `D` is a projection of `U`. Prop 15
(`BC ⟹ bifinite`, r0027) and Thm 22 (`countably-based algebraic lattice ⟹ a
closure r : P(ℕ) → L`, r0028) are the two results the paper's route uses.

**Acceptance:** `U` with a `Domain` instance and its basis characterized;
`thm27`. `U` is the prerequisite for streams 4 and 5, so this stream reports its
carrier and its interface *first*, before finishing Thm 27.

### Stream 4 — agent4 — Theorem 26 and Lemma 28

Namespace `ScottDomains.Combinator`.

**Theorem 26**: for any signature `(s₁,…,s_n)`, combinators `F₁,…,F_n` solving
the equations. Builds on Thm 21 (`Recursive.thm21`) and `IsRepresentable₂.diag`,
both r0029 — no new carrier needed.

**Lemma 28**: the seven operators `→, ×, ⊗, +, ()⊥, ()♯, ()♭` are representable
over `U`. This depends on stream 3's `U`. **Decouple it:** prove each operator
representable over an *abstract* carrier satisfying the interface Lem 24 and Thm
25 already use — both were proved at cpo strength, spending neither algebraicity
nor countability, so the interface is weak and the proofs should not need `U`'s
specific structure. Instantiate at stream 3's `U` after the merge. This makes the
dependency a merge-order dependency, not a launch-order one.

**Acceptance:** `thm26`; seven representability proofs over the abstract carrier;
instantiation at `U` deferred to the merge and named as such in the report.

### Stream 5 — agent5 — Theorem 29, §7.4's `V`, Lemma 30

Namespace `ScottDomains.BifiniteUniversal`. The largest stream.

**Theorem 29**: `D` bifinite ⟹ `D+` bifinite, and solving `D ≅ D+`. Read what
[Gun87] leaves deferred *before* proving — r0033 flagged this and it is unchecked.
Solving `D ≅ D+` is how §7.4 constructs the bifinite universal domain `V`, so
Thm 29 and `V` are one piece of work, not two.

**Lemma 30**: the same seven operators are **p-representable** over `V`.
P-representability is over `Fp(U)` and is a *distinct notion* from
`IsRepresentable` over `Fc(U)` — do not reuse the existing class. `Fp(D)` as a
poset already exists (`FinitaryProjectionPoset.lean`, r0028), so `IsPRepresentable`
can be defined without waiting on stream 3.

**Acceptance:** `thm29`; `V` with its instances; `IsPRepresentable` defined and
distinguished from `IsRepresentable` in its docstring; `lem30`. If Lem 30 does
not land, Thm 29 and `V` alone are a complete deliverable — say so rather than
leaving a `sorry`.

### Stream 6 — agent6 — Theorem 18, and Theorem 16's positive form

Namespace `ScottDomains.Section62`. Requires the agent6 worktree.

**Theorem 18** (`D` and `D → D` domains ⟹ `D` bifinite) is the development's
oldest `sorry` and has failed in three rounds. What is known:

- The paper gives no proof, citing Smyth [Smy83a].
- `isBifinite_iff_mubClosure` (r0028) reduces it to two obligations.
- `ContinuousConstruction.lean` (r0031) supplies a constructor needing neither
  bounded completeness nor algebraicity, and reduces cases (a) and (b) to one
  finiteness statement — which is **equivalent** to Thm 18, not a lemma below it.
- The perturbation route fails on one monotonicity side condition; three variants
  fail at the same point.

**The instruction is therefore different from prior rounds: read [Smy83a]
directly.** Do not generate a fourth variant of the perturbation argument. If the
case analysis is not recoverable from the source, write the obstruction precisely
— which side condition, at which step, and why the reduction is circular — and
stop. A precise obstruction is the deliverable if the proof is not.

**Theorem 16's positive form** is the complementary small task: the embedding
conjunct that r0032 refuted *does* hold when every `S_f` has a greatest normal
subposet, a condition bounded complete domains satisfy. It is currently unstated.
State and prove it, and cross-reference the refutation so the pair reads as one
result.

**Acceptance:** `thm16_positive` proved; and either `thm18` proved — taking the
development to 0 `sorry` — or a written obstruction in the module docstring and
the report.

## Expected outcome

| # | Case | Numbered results complete |
| -- | ---- | ------------------------- |
| 1 | Baseline | 18 of 29 |
| 2 | Streams 1, 2, 6 land (small diffs, no new carriers) | 21 + Thm 16 positive form |
| 3 | Streams 3, 4 also land | 24 |
| 4 | All six land including Lem 30 | **28 of 29** — everything but a still-open Thm 18 |
| 5 | All six land and Thm 18 falls | **29 of 29**, development at 0 `sorry` |

Case 4 is the realistic target. Thm 18 has resisted three rounds and its
reduction is provably not a weakening, so it is planned as research, not as
scheduled proof work.

## Sequencing

Launch all six at once. Two dependencies are merge-order, not launch-order:

1. Stream 4's instantiation of Lem 28 at `U` waits on stream 3's merge.
2. Stream 5's `Fp(U)`-based p-representability instantiates at stream 3's `U`,
   but its *definition* does not wait.

Stream 3 reports `U`'s carrier and interface before finishing Thm 27, so 4 and 5
can align their abstract interfaces early.

## Process rules for every agent plan

These are the rules that earned their place across r0028–r0032; restate them in
each per-agent plan and check the reports for compliance.

1. **Namespace per agent** — `ScottDomains.<Stream>` as assigned above. Zero
   collisions r0029–r0032 under this rule; two clashes among five agents before it.
2. **Edit/Write only, never heredocs.** r0032's agent3 edited Lean with
   `python3 - <<'PY'`, prompting the user repeatedly against its own plan.
3. **One command per Bash call. Never chain, never `cd`.** 133 prompts in one
   measured day contained `&&`/`;`/`|`/`$(…)`; 58 began with `cd`.
4. **Multi-step work becomes a script in `scripts/`** — standing-authorized.
5. **Read the PDF, not the paraphrase.** Four separate corrections came from
   agents doing this, including the Type 3 decoding that made stream 1 possible.
6. **Agents commit, only the orchestrator pushes.** "No tracking information" on
   push is the expected outcome for an agent, not an error.
7. **Composition check after every merge**: `scripts/axioms.sh -i <module> …`
   importing every new module together. `lake build` cannot catch a cross-module
   duplicate — that is how r0028's clash survived 971 green jobs.

## Orchestrator steps

1. ~~`scripts/worktree-sync.sh --ff`~~ — done; six worktrees at `1c9f38f`, clean.
2. ~~Create the agent6 worktree~~ — done, `scripts/init-worktree.sh 6`.
3. ~~Cut six per-agent plans~~ — done,
   `plans/r0034-plan-from-orchestrator-to-agentN-<subject>.md`.
4. The user attaches a session in each `~/projects/ScottLean4-agentN/` (rule 2.3)
   and points it at its plan.
5. On each report: review the diff, run `scripts/axioms.sh` on the new modules,
   merge, rebuild, then push.
6. Update `docs/PaperInventory.md` rows 2, 2a, 2b and 6 from the measured counts,
   not from the plan's expectations.
