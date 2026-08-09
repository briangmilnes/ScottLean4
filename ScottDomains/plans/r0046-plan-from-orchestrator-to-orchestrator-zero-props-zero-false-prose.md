---
round: r0046
from: orchestrator
to: orchestrator
subject: zero-props-zero-false-prose
date: 2026-0808-22:05
status: pending
related:
  - analyses/discharge-nineteen.2026-0808-21:45.orchestrator.md
  - analyses/specification-defects.2026-0808-21:05.orchestrator.md
---

# r0046 — two standing goals

The user has set two goals, and they are standing: rounds continue until both
reach zero or the residue is a named open problem.

| # | Goal | Baseline | Measured by |
| -- | --- | -------: | ----------- |
| **A** | **Zero `Prop`s naming a theorem** — no `def Foo : Prop` stating a result of the paper or of Jung that nothing proves | **10** | `scripts/a6-env-scan.sh` + `a6-summarize.py`, re-run over the built environment |
| **B** | **Zero prose claiming to be proof** — no docstring or document asserting that something is proved, required, impossible or absent when it is not | **11 false claims + 218 false-name sites** | no instrument exists; this round builds one |

Goal B is stated by the user as "zero prose claiming to be proof, **with or
without `sorry`**." The `sorry` count is 0 and has been for three rounds; that is
exactly why prose is now the binding constraint. A sentence claiming a proof
exists is as misleading as a `sorry`, and nothing checks it.

## Goal A: the ten, and what each actually needs

| # | Claim | Status | Needs |
| -- | ---- | ------ | ----- |
| 1 | `Colimit.Thm29Second` | **refuted** | bookkeeping |
| 2 | `PRep.Lemma28` | **refuted** | bookkeeping |
| 3 | `LemThirty.Lemma30` | schema, not a proposition | bookkeeping |
| 4 | `Theorem7ArrowRecursive` | reduced to 1 hypothesis | row 6 |
| 5 | `Lemma30AtV` | reduced, 2 → 5 conjuncts | row 10 + 3 missing `PRep` schemes |
| 6 | `StepFunctionsDecidable` | open **and mis-stated** | restate, then prove or refute |
| 7 | `Theorem7StrictRecursive` | open | an enumeration of `K(D ⊸ E)` |
| 8 | `Thm29SecondAtDomains` | open | row 10 |
| 9 | `Lem30Arrow` | open | row 5 |
| 10 | `Thm29Normal` | open | a universal property of `M` — **[Gun87]** |

**Three of the ten are not proof work.** Rows 1–3 inflate the count because the
detector scores "has a theorem concluding it", and a refutation produces `¬ Foo`,
not `Foo`. **Four more are downstream** of rows 6 and 10. So Goal A reduces to
four open problems, one of which is blocked on a paper we do not have.

## Streams

### agent1 — rows 1, 2, 3, 6: bookkeeping and the restatement

**Highest yield in the round: it takes Goal A from 10 to 6 and fixes a
mis-statement.**

Rows 1–3, record correctly so the claims leave the list. A refuted claim is
*resolved*, not open, and must be visible as such to the detector — decide
whether that means retiring the `def`, or marking it and teaching
`a6-summarize.py` to read the mark. **Prefer the instrument change**: deleting a
`def` loses the statement, and `LemThirty.Thm29Normal`'s docstring gives the
correct reason for keeping statements citable. Whatever you choose, the
refutation theorem must remain reachable from the claim's own docstring.

`Lemma30` is a parameterized family whose universal closure is false, and at
`W := V` it simply is `Lemma30AtV` — drop the row, keep the `def` if it is used.

**Row 6 is a specification change, and this round authorizes it — narrowly.**
`StepFunctionsDecidable`'s universal closure is false: the paper's sentence says
"using the effective presentations of `D` and `E`", our `def` quantifies over
arbitrary `d`, `e`. Restate it to the paper's printed sentence. Conditions:

* **Quote the printed sentence and its page** in the docstring, and record the
  old statement and why it was wrong. A silent weakening is the exact defect
  r0044 found nine times.
* The new statement must be **stronger or equal** at the paper's intent — you are
  correcting a transcription error, not lowering a bar.
* Then discharge it, refute it, or say precisely what blocks it.

If it discharges, row 4 falls with it; check.

### agent2 — row 10: `Thm29Normal` and what [Gun87] would supply

The deepest item and the one that unlocks rows 5, 8 and 9.

The missing input is named: **a universal property of `M` among finite posets
under normal embedding.** Nothing in `BifiniteUniversal.lean` concerns maps
between two different bases.

Your task is **not** "prove it if you can" — it is to determine whether it can be
reconstructed without [Gun87]:

1. State the universal property precisely, as a Lean `def` or `theorem`
   statement, in your namespace. Naming the missing input exactly is the round's
   deliverable even if nothing is proved.
2. Establish what it would give: does it in fact yield `Thm29Normal`? Prove the
   implication if so — a reduction to a single named, precisely stated input is a
   large advance over "open".
3. Assess reconstructibility from what we have — `Dyadic`, `BifiniteUniversal`,
   `JungFinite`, `Universality`, and the literature we do hold.

**A well-stated negative result is the expected outcome and is a success.** Do
not manufacture a proof.

### agent3 — rows 7 and 5's other blocker

Two independent pieces.

`Theorem7StrictRecursive` needs an enumeration of `K(D ⊸ E)`, the compacts of the
strict function space, which the development does not have. Its own docstring at
`Effective/FunctionSpace.lean:258` concedes the package contains no strict step
functions. Build the enumeration if it is buildable; if not, say what blocks it.

Separately, `Lemma30AtV` is short **three `PRep` schemes** (agent3's r0045
finding). Identify them precisely and build what you can. Coordinate with agent2:
if `Thm29Normal` reduces, `Lemma30AtV` needs only the schemes.

### agent4 — Goal B instrument: prose claiming a proof exists

**Build the sweep that does not exist.** Target sentences asserting that
something *is proved, follows, is immediate, is established, is checked, is
carried out below* — then check each against the built environment.

Known true positives to calibrate against, all confirmed:

* `LemThirty.lean:387` — "two of Lemma 28's nine schemes are proved"; **seven** are.
* `LemThirty.lean:506` — `Thm29Normal` without `[Domain E]` "is refutable rather
  than open"; nothing had proved it (r0045 then proved it).
* `PowerdomainMap.lean:18` — a "nine variants returned zero hits" survey,
  falsified by a declaration at `:167` **of the same file**.
* `PRepFun.lean:658` — says `Domain (D ⊗ E)` does not exist; `smashDomain` is
  proved **334 lines below in the same file**.

Note the pattern: **four of four are falsified by something in or near the same
file.** Prioritize intra-file contradiction; it is both the highest-yield and the
cheapest to check.

Report a count, a ranked list, and **a measured precision**. r0044's agent7 hand-
checked all 48 of its `.lean` sites to state 91.7%; hold that standard. A sweep
with unmeasured precision is not usable and will not be merged.

### agent5 — Goal B: necessity and impossibility claims

**Seven of these have been found across three rounds, every one incidentally,
and every one of the form "X is required" or "Y cannot be done".** It is this
development's least reliable sentence type and it has never been swept.

The instrument is known and proved to work in both directions: **the deletion
probe.** r0044's agent8 confirmed `Kleene/Uniform.lean:39`'s "indispensable" by
deleting the hypothesis and watching the reproof *fail*; r0045's agent1 and
agent4 refuted two others by deleting and watching it *succeed*.

Sweep for: "cannot do without", "indispensable", "is required", "has to go
through", "is not possible", "does not exist", "there is no", "is not in
Mathlib", "nothing proves". For each, run the probe.

Known instances to confirm and extend:
* `PowerdomainMapRep.lean:42` — "has to go through `IsProjection.isCompactElement_iff`"; false, found independently by two r0045 agents.
* `Effective/FunctionSpace.lean` — `RecursiveNormal`'s docstring says Mathlib has no `Primcodable (Finset ℕ)`; `Primcodable.ofDenumerable` supplies it.
* `Kleene/Graph.lean:36` — "which the argument cannot do without"; refuted in r0044.

Categorical claims about **Mathlib** age worst — r0044 checked eleven and found
`OrderIso.prodCongr` genuinely absent, so these are not all false and you must
check rather than assume.

## Hard rules

This round **writes `.lean` files and edits documentation**. Both limits apply.

* **Namespace per agent** (`ScottDomains.R46.AgentN`), new files prefixed `A<N>`.
  The orchestrator runs `scripts/axioms.sh -i` across all five at merge; `lake
  build` never imports two unrelated modules into one environment.
* **No `sorry`.** The package is at 0 and stays at 0.
* **Only agent1 may change a claim's `def`**, and only row 6, under the
  conditions above. Every other stream that believes a statement is wrong reports
  it and leaves it.
* **Editing prose is authorized for agents 4 and 5** — fixing a false sentence is
  the point. Two conditions: the correction must be **checked against the built
  `.olean`**, and you must not delete the historical record — if a sentence was
  true when written and a later round made it false, say so.
* Build with `scripts/compile.sh -r r0046`; zero errors, zero warnings.
* `#print axioms` every theorem added, via `scripts/axioms.sh`.
* One command per Bash call; never chain; never `cd`. `Edit`/`Write` only — no
  heredocs, no `sed -i`. Commit with your worktree's `scripts/gitcp.sh`; do not
  push.

## Evidence rules

Unchanged, because they keep working:

* **A negative result is a result.** r0045's agent5 proved the plan's central
  lead was wrong and closed its claims by another route entirely.
* **Do not inflate.** r0044's agent6 had 55 available and reported 19.
* **Discharged vs discharged-at.** A theorem concluding the claim with an
  **added instance binder** is *not* a discharge. This is r0044's dominant defect
  mode and my own criterion missed it in r0045.
* **Correct the plan, the orchestrator and each other.** Every round so far has
  produced corrections to me that were right. **The plan is not evidence.**
* **Check the paper before convicting it.** Nine printed defects are on record.
  Twice we nearly added a tenth that was our own transcription error.

## Deliverable

`reports/r0046-report-from-agentN-to-orchestrator-<subject>.md`. Agents 1–3
report per-claim status in r0045's vocabulary: discharged / discharged-at /
refuted / reduced / open. Agents 4–5 report a count, a ranked list, the
instrument, and its **measured precision**.

## Orchestrator steps

1. Fast-forward worktrees, then launch.
2. Merge; composition check across five namespaces.
3. **Re-derive both goal numbers** — Goal A by re-running the detector, Goal B by
   running whatever instrument agents 4 and 5 built. Never by subtraction.
4. Update `PaperInventory.md` rows 2h–2j and the analyses.
5. **Continue.** These goals are standing; open the next round on whatever
   residue remains, and state plainly which residue is a genuine open problem
   rather than unfinished work.
