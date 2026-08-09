---
round: r0049
from: orchestrator
to: orchestrator
subject: six-at-the-unproven
date: 2026-0809-14:15
status: pending
related:
  - docs/Status.md
  - analyses/close-the-seven.2026-0809-12:35.orchestrator.md
  - plans/r0048-plan-from-orchestrator-to-orchestrator-find-two-and-fifteen.md
---

# r0049 — six agents at the unproven results

`docs/Status.md` lists eight open items, of which **six are downstream of two**.
This round attacks the two, the propositions they reduce to, and the three
categories of unfinished work that are not numbered results at all.

**Agents 1 and 2 are running r0048** (the two never-transcribed results). This
round uses **agents 3–8**, whose worktrees are free. Eight concurrent writers is
at `docs/Performance.md`'s declaration-collision limit, so **namespace per agent
is not optional this round** — r0048 writes into `ScottDomains.R48.AgentN`, this
round into `ScottDomains.R49.AgentN`.

## What is open, and who takes it

| # | Agent | Target | Closes |
| -- | ----- | ------ | ------ |
| 3 | agent3 | restate `StepFunctionsDecidable` over `consistentEnum` | up to 4 claims |
| 4 | agent4 | the recursion theory the two Theorem 7 claims still need | agent3's residue |
| 5 | agent5 | `Thm29Normal` — the §7.4 dilemma | up to 4 claims |
| 6 | agent6 | `FpImagesBifinite V` | `Lemma30AtV` conjuncts 1–2 |
| 7 | agent7 | Theorem 26's `hs`, and the added-binder `S≠` rows | 13 defects of ours |
| 8 | agent8 | Goal B's residue and a standing staleness check | 183 + 52 sites |

### agent3 — `StepFunctionsDecidable` over the consistency-guarded enumeration

**The round's highest-yield item, and it is mechanical.** r0047's agent2 proved
`IsCompactElement (ofPairs Q)` is **not** the boundedness test — closed
refutation `not_forall_isCompactElement_ofPairs_imp_bddAbove`, witness at
`α = β = N⊥` with a presentation that *is* `IsRecursive`. `sSup` on `ScottHom` is
total, so on an inconsistent `Q` the guard reads a junk value that can be compact.

The replacement is built and merged: `R47.Agent2.consistentEnum`/`scottHomC` and
`strictConsistentEnum`/`strictHomC`, with `exists_ofPairs_consistent` proving both
still exhaust the basis, and `bddAbove_stepsOf_iff` characterizing boundedness by
consistency.

**You are authorized to change `Effective.StepFunctionsDecidable`'s `def`** — the
only stream this round so authorized — under the conditions that worked in r0046
and r0047:

* Quote the printed sentence and its page; the current statement already carries
  p. 12's "using the effective presentations of `D` and `E`".
* Keep the pre-r0049 statement verbatim under your namespace and **prove the
  implication recording the direction of the change**. r0046's
  `stepFunctionsDecidable_of_unconditional` and r0047's
  `freeCarrier_of_preservesRecursivePresentation` are the pattern — note the
  latter runs the *opposite* way, and saying which direction yours runs is part
  of the deliverable.
* Then discharge it, or hand the exact residue to agent4.

If it discharges, check `Theorem7ArrowRecursive`, `Theorem7StrictRecursive` and
`PreservesRecursivePresentation` at `arrowOp` — r0047 proved the last equivalent
to the first.

### agent4 — the recursion theory

r0047 measured what remains for the two Theorem 7 recursive claims once agent3's
restatement lands, and it is **recursion theory only**:

1. `Primrec` facts for the `Finset (ℕ × ℕ)` coding. r0045 proved the `Finset ℕ`
   analogue — `R45.Agent1.zero_mem_ofNat_finset_iff`, in
   `Effective/A1FlatRecursive.lean`, which also carries
   `natBotRecursivePresentation`, the first genuine `RecursivePresentation`, built
   from `Primrec` combinators with `decide` examples confirming the procedures
   run. That is the pattern.
2. A `Nat.rfind` with a totality proof for the normal-subposet search.
   `R47.Agent2.bddAbove_iff_exists_normal` makes the search terminate:
   `isNormalIn_joinClosure` puts every finite set of compacts inside a finite
   normal one.

**Neither `Nat.bitwise` nor `REPred` appears in any of it** — both were measured
in r0046 and again in r0047 as real obstructions to something else. Do not spend
the round on either.

Coordinate with agent3: it may hand you a narrower residue than this.

### agent5 — `Thm29Normal`, and the §7.4 dilemma

**The deepest item.** r0047 established the shape and did not resolve it:

* `R47.Agent1.lemma24_MPair` proves Gunter's Lemma 24 at `M(A)` — the first proof
  anywhere; the printed Lemma 24 produces *some* `A⁺` and is not about `M(A)`.
* `not_hasNormalRealizations_Ainf` **refutes** the hypothesis r0046 reduced
  `Thm29Normal` to. The implication is sound; the target is empty.
* The dilemma, measured on both sides: the `M(f)` tower gives `V ≅ V⁺`, which
  every Lemma 30 conjunct consumes, but refutes Theorem 25's hypothesis; the `η`
  tower satisfies Lemma 24 but is **not a fixed point of `M`**.

r0047's agent1 named three ways forward and **attempted none of them**. One is
**refuting `Thm29Normal` outright**, which no stream has tried. Take whichever you
judge best and say why; a kernel-checked refutation closes the claim as
decisively as a proof, and `R45.Agent3.not_thm29NormalWithoutDomain` already
shows `[Domain E]` is necessary.

Read `A1Lemma24.lean`'s report section before starting — it lists the three
routes with the evidence for each.

### agent6 — `FpImagesBifinite V`

r0047's agent4 reduced `Lemma30AtV`'s conjuncts 1–2 to exactly one proposition:
**every finitary-projection image of `V` is bifinite** — Plotkin's closure under
projections.

It is **not a formality**, and agent4 said why: transporting a normal subposet
along `p` fails because `p a ≤ x` does not give `a ≤ x`, and the
finite-image-deflation argument needs an idempotence that `q ∘ p_i ∘ q` lacks.
No declaration in the development concludes `IsBifinite` of a projection image.

`JungSFP.lean`, `JungFinite.lean` and `FinitaryProjection.lean` are where the
existing machinery is. Prove it, refute it, or name what it needs.

### agent7 — Theorem 26's `hs`, and the added-binder rows

Two pieces of the same defect: **stating the paper's conclusion under stronger
hypotheses than the paper assumes.** r0044 measured that as this development's
dominant mode — **9 of 12 under-specified rows** — and r0047 showed one such
binder came out cleanly.

**Theorem 26.** `thm26` carries `hs : ∀ i, 0 < s i`, which the paper does not
assume. The recorded justification — that Theorem 26 is *false* at arity 0 — is
**not established**: the contradiction is derived from `fst(ψ(x)) = x`, a property
of the paper's construction and of our own conclusion, whereas the printed
statement asks only that `A` "be made isomorphic to a subalgebra", and two
one-point algebras are isomorphic to the same one-point subalgebra `{Fᵢ}`. Settle
it: **either exhibit a genuine arity-0 counterexample to the printed conclusion,
or drop `hs` and prove `thm26` without it.**

**Then the rest.** 13 of the 18 `S≠` rows are defects of ours (5 are repairs of
printed errors and must not be touched). The method is proved: r0047's agent4
removed `[BoundedComplete β]` from six declarations by finding **Gunter & Scott's
own §6.2 argument**, which does not need it, and recorded four `*_imp_old`
theorems proving the bar was not lowered. `scripts/a4-delete.lean`,
`a4-run-delete.sh` and `a1-probe45.lean` are the deletion harness.

Report which rows moved and which are genuinely necessary — a binder proved
necessary is as valuable as one removed, and r0046 established that "my reproof
failed" is **grade C**, a statement about the prover, while refuting the
binder-free statement is **grade A**.

### agent8 — Goal B's residue, and making the check standing

Three pieces.

1. **183 unadjudicated necessity sites** from r0046's sweep of 228, plus **52
   absence claims with an unbackticked subject** from r0044's — a blindness that
   stream quantified rather than caveated, 13 of which assert the package lacks
   something. The deletion probe decides necessity claims **in both directions**;
   the base rate of falsity measured 20.8%, so **report the true ones too**.
2. **Class U — 103 sites — needs a writing convention, not an instrument.**
   "The only place `X` is spent" is file- or proof-scoped, so a global
   reverse-dependency count is the wrong denominator; r0046's agent5 **refused to
   convict** `JungBicomplete.lean:506` on those grounds despite measuring 11 users
   against a claim of one. Propose the convention — sentences naming their scope
   — and write it into `~/projects/GRASE/standards/` or `docs/`.
3. **Make the check standing.** r0046 established that **seven of eight false
   proof-claims were true when written** — this is a staleness problem, and
   nothing signals it: no `sorry`, no build failure. Propose and build a check
   that runs per round, not per sweep. `scripts/a4-claim-scan.py`,
   `a5-r46-sweep.sh` and `a7-sweep.sh` are the existing instruments.

Corrections owed and not yet applied: `Colimit.lean:59` cites
`etaChain_not_wellDefined`, **which exists nowhere** — third sighting, the real
witness being `stgEmb_ne_mk_eta`.

## Hard rules

* **Namespace per agent** (`ScottDomains.R49.AgentN`), files prefixed `A<N>`.
  Eight concurrent writers is at the collision limit; the orchestrator runs
  `scripts/axioms.sh -i` across all namespaces at merge.
* **No `sorry`.** The package is at 0 and stays at 0. A `Prop`-valued `def`
  nobody attempts is worse than an honest "open" — `sorry` cannot see it.
* **Only agent3 may change a claim's `def`**, and only `StepFunctionsDecidable`.
  agent7 may change *theorem* binders in its own namespace; it may not edit an
  existing declaration in place.
* **Discharged vs discharged-at.** A theorem concluding the claim with an added
  instance binder is not a discharge.
* Build with `scripts/compile.sh -r r0049`; zero errors, zero warnings.
  `#print axioms` every theorem added.
* One command per Bash call; never chain; never `cd`. `Edit`/`Write` only.
  Commit with your worktree's `scripts/gitcp.sh`; do not push.

## Evidence rules

* **A negative result is a result**, and a precisely located obstruction beats a
  forced proof.
* **Re-derive blockers.** Five recorded blockers have been found overstated or
  simply wrong in the last three rounds, including two whose stated reasons were
  each refuted by the agent assigned to them.
* **Check the paper before convicting it.** Nine printed defects are on record;
  **three further suspicions were each traced to our own transcription error.**
* **The plan is not evidence.** It is built from reports one round old, and r0047
  showed a plan can be stale before it is written.

## Deliverable

`reports/r0049-report-from-agentN-to-orchestrator-<subject>.md`, per item:
discharged / discharged-at / refuted / reduced / open, with axiom footprints.

## Orchestrator steps

1. Merge r0048 first, then launch these six.
2. Merge; composition check across all r0048 and r0049 namespaces.
3. Re-derive Goal A with `a6-env-scan.sh` + `a6-summarize.py`; re-run
   `numbered-status.sh`; update `docs/Status.md` and regenerate its PDF.
