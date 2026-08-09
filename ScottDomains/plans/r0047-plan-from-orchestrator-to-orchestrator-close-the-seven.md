---
round: r0047
from: orchestrator
to: orchestrator
subject: close-the-seven
date: 2026-0809-12:05
status: pending
related:
  - analyses/zero-props-zero-false-prose.2026-0809-11:40.orchestrator.md
  - docs/PaperInventory.md
---

# r0047 — close the seven, and the unfinished proofs behind them

Two standing goals, unchanged. This round attacks **Goal A's residue** and the
**unfinished proofs** that row 2h and 2i of `PaperInventory.md` record.

The residue is unusually tractable. After r0046 there are **7 open claims (8
strict)**, and they are not seven independent problems:

| # | Claim | Blocked on |
| -- | ---- | ---------- |
| 1 | `Thm29Normal` | **Gunter's Lemma 24 at `M(A)`** — published proof in hand |
| 2 | `Thm29SecondAtDomains` | claim 1 |
| 3 | `Lemma30AtV` | claim 1, plus conjuncts 1–2 |
| 4 | `Lem30Arrow` | claim 3 |
| 5 | `StepFunctionsDecidable` | **deciding `IsCompactElement (ofPairs Q)`** — one lemma |
| 6 | `Theorem7ArrowRecursive` | claim 5 |
| 7 | `Theorem7StrictRecursive` | claim 5 |
| 8 | `PreservesRecursivePresentation` | mis-stated; needs a `def` change |

**Two lemmas close six of the eight.** Claim 1's proof is *published* and we own
the paper; claim 5 is a single domain-theoretic fact. Neither is a research
problem. The one genuine unknown is claim 3's conjuncts 1–2.

## Streams

### agent1 — Gunter's Lemma 24 at `M(A)`, and `Thm29Normal` with it

**The highest-value item in the project.** Closing it discharges claims 1, 2, and
most of 3, and it is transcription rather than research.

The proof is in **`papers/Gunter 1987 Universal Profinite Domains.pdf` §5,
pp. 16–23** — Prop. 21, Thm. 22, Lemmas 23–24, Thm. 25, Cor. 26, with proofs.
The p. 23 remark identifies Gunter's `A⁺` with Scott's `M(A)`.
`BifiniteUniversal.lean:47` already cites that page, for the *construction* only.
A second copy is Gunter's CMU dissertation, whose file is misnamed
`Gunter 1985 …`.

r0046 built the scaffolding: `R46.Agent2.HasNormalRealizations` is the statement,
`thm29Normal_of_hasNormalRealizations` is the kernel-checked implication with
`Thm29Normal` used **exactly as stated and no added binder**, and
`hasNormalRealizations_of_stages` localizes it to a single step of the tower —
that hypothesis is `LemThirty.lean:426`'s sentence verbatim. `MPair`, `eta` and
`MSub_isNormalIn` already exist in `BifiniteUniversal.lean`.

So: prove Lemma 24 at `M(A)`, discharge `HasNormalRealizations`, and let the
implication carry it. If the published proof does not transfer, **say exactly
where** — that is a finding about the paper, and it must be checked against the
printed text before being asserted.

### agent2 — `IsCompactElement (ofPairs Q)`, and three claims with it

One domain-theoretic fact closes claims 5, 6 and 7.

r0046's agent1 established what it is: **deciding whether a finite set of step
functions named by index pairs is bounded above.** The order characterization is
half-available from `step_le_iff`; the pointwise evaluation and the
`RecursiveNormal` conjunct both reduce to the same fact; the recursion theory is
the `Finset (ℕ × ℕ)` coding, whose `Finset ℕ` analogue r0045 already proved as
`zero_mem_ofNat_finset_iff`.

**Both previously recorded blockers were measured and are not blocking.**
`Nat.bitwise`/`lor`/`testBit` co-occur with `Primrec`/`Computable` in 0 Mathlib
files — but that blocks *constructing* a recursive presentation of `P N`, which
these claims assume rather than build. `REPred` has 7 declarations and no closure
lemma — but the claims are `ComputablePred` throughout and name `REPred` nowhere.
Do not spend the round on either.

`StepFunctionsDecidable` was restated in r0046 to the paper's p. 12 sentence;
`R46.Agent1.stepFunctionsDecidable_of_unconditional` is the kernel's record that
the change did not lower the bar. Prove the restated form.

### agent3 — `PreservesRecursivePresentation`, and a sweep for its vacuity mechanism

Two pieces, and the second is worth more than the first.

`Effective.PreservesRecursivePresentation` quantifies over a `γ` unrelated to its
`α` and `β`, so `preservesRecursivePresentation_id` closes it in one line by
returning its own hypothesis, and its closure over `γ` is false by a counting
argument. **This stream is authorized to change that `def`**, under r0046's
conditions: quote the paper's sentence and page, keep the old statement verbatim
with a kernel-checked implication recording the direction of the change, and do
not lower the bar. Then discharge or refute it.

**Then sweep for the mechanism.** This is a *second and independent* vacuity
mechanism — the vacuity is in the **quantifier structure, not a field type**, so
r0044's sweeps, which looked for `Classical.dec`-inhabitable fields, would pass
it. **Exactly one instance is known and nobody has ever swept for it.** The
check is question 2 of `docs/StructuresVsTypeClassesVsPropsInLean4.md`: *is every
bound variable actually constrained by the claim, or can one be instantiated to
make the statement trivial?*

r0045's `a5-freehyp.lean` and r0044's `a3-vacuity.lean`/`a4-freeclass.lean` are
the nearest instruments; read them first. Report a count, a list, and a measured
precision. **A zero is a result** if backed by controls — r0044's agent4 backed
its 0-of-427 with four.

### agent4 — `[BoundedComplete β]` on `lem17_fun`: the one genuine unknown

`Lemma30AtV`'s conjuncts 1–2 are blocked by `R45.Agent3.not_boundedComplete_V`
against `rep_arrow`/`rep_strictArrow`'s `[BoundedComplete U]`. That reduces to
removing `[BoundedComplete β]` from `lem17_fun`, which
`ClosureProperties.lean:54` already calls **"a real open item, not a formality"**
— it is an artifact of this development's route to `Domain (D → E)` through
Theorem 7's step functions.

This is the only item in the residue that is genuinely open. Three outcomes, all
acceptable, all to be labelled precisely:

1. Remove it — a different route to `Domain (D → E)` that does not need bounded
   completeness. This closes conjuncts 1–2.
2. Prove it cannot be removed — `¬` the binder-free statement, kernel-checked.
   r0046's agent5 calls that **grade A**; "my reproof failed" is grade C and is a
   statement about the prover, not the theorem.
3. Neither, with the obstruction stated precisely.

Note `V` is universal for bifinite domains and `PRep.boundedComplete_range` says
a projection of a bounded-complete domain is bounded complete, so `Thm29Second`
and `BoundedComplete V` cannot both hold — the tension is real and located.

### agent5 — the unfinished proofs: the 16 `S+H` rows

**The other half of the user's request, and it has never been attacked
systematically.** `S+H` means the paper's property is *stated correctly* and the
proof is open — 16 of the paper's 239 properties (r0040, +1 from r0043).

These are distinct from Goal A's `Prop`-valued claims: an `S+H` row is a real
Lean statement with an open proof, not a `def` nobody attempted.

Enumerate them from `analyses/property-coverage.2026-0808-11:59.orchestrator.md`
and its r0043 successor. For each: is it open because nobody tried, because it
needs a missing construction, or because it is false as stated? **Prove what you
can; for the rest, name the missing input.** r0046 showed twice that a recorded
blocker was overstated — the strict-step-function basis was four lines away, and
`Thm29Normal`'s "unobtainable paper" was on our own disk — so **re-derive each
blocker from the current tree rather than trusting the record.**

If the real count is not 16, report the real number with its derivation. r0044's
Class 1 assignment was wrong by exactly this kind of staleness and both agents
caught it.

## Hard rules

This round **writes `.lean` files**, so the declaration-collision limit applies.

* **Namespace per agent** (`ScottDomains.R47.AgentN`), new files prefixed `A<N>`.
  The orchestrator runs `scripts/axioms.sh -i` across all five at merge.
* **No `sorry`.** The package is at 0 and stays at 0.
* **Only agent3 may change a claim's `def`**, and only
  `PreservesRecursivePresentation`. Every other stream reports and leaves it.
* **Discharged vs discharged-at.** A theorem concluding the claim with an
  **added instance binder** is not a discharge. This is the development's
  dominant defect mode and it caught this orchestrator in r0045.
* Build with `scripts/compile.sh -r r0047`; zero errors, zero warnings.
  `#print axioms` every theorem added.
* One command per Bash call; never chain; never `cd`. `Edit`/`Write` only.
  Commit with your worktree's `scripts/gitcp.sh`; do not push.

## Evidence rules

* **A negative result is a result**, and a precisely located obstruction beats a
  forced proof.
* **Do not inflate.** r0044's agent6 had 55 available and reported 19.
* **Re-derive blockers.** Three separate recorded blockers have been found
  overstated in the last two rounds.
* **Correct the plan, the orchestrator and each other. The plan is not
  evidence** — it is built from reports one round old, and r0046 showed a plan
  can be stale before it is written.
* **Check the paper before convicting it.** Nine printed defects are on record;
  twice we nearly added a tenth that was our own transcription error.

## Deliverable

`reports/r0047-report-from-agentN-to-orchestrator-<subject>.md`, per claim:
discharged / discharged-at / refuted / reduced / open, with the axiom footprint
of every theorem added.

## Orchestrator steps

1. Fast-forward worktrees, then launch.
2. Merge; composition check across five namespaces.
3. **Re-derive Goal A** by re-running `a6-env-scan.sh` + `a6-summarize.py` on the
   merged tree. Never by subtraction.
4. Update `PaperInventory.md` rows 2h–2j, 5 and 6, and regenerate the PDF.
5. Continue: the goals are standing.
