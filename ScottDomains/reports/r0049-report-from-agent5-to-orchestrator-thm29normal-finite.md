---
round: r0049
from: agent5
to: orchestrator
subject: thm29normal-finite
date: 2026-0809-17:05
started: 2026-0809-16:25
finished: 2026-0809-17:05
related:
  - plans/r0049-plan-from-orchestrator-to-orchestrator-six-at-the-unproven.md
  - reports/r0047-report-from-agent1-to-orchestrator-lemma24.md
  - reports/r0046-report-from-agent2-to-orchestrator-thm29normal.md
---

# r0049 agent5 — `Thm29Normal` at finite bases, and where the dilemma actually bites

**The three questions, answered first.**

| # | Question | Answer |
| -- | -------- | ------ |
| 1 | Which of r0047's three routes? | **Route 1** — prove `Thm29Normal` without passing through Theorem 25. Routes 2 and 3 are argued against below, with the evidence |
| 2 | What is now proved? | **`A∞` is universal for the finite pointed posets**: `exists_normal_embedding_Ainf`, unconditional, kernel-checked. Hence `Thm29Normal`'s conclusion for every bifinite `E` with a finite basis |
| 3 | Is `Thm29Normal` discharged? | **No — reduced.** The finite-basis case is closed; the infinite-basis case is open, and the obstruction in it is now located to one sentence |

New file `ScottDomains/ScottDomains/A5Thm29Finite.lean`, 303 lines, **6 theorems,
0 `def`s**, namespace `ScottDomains.R49.Agent5`. Package: **1366 jobs, 0 errors, 0
warnings, 0 `sorry`**. No existing file was changed; no `def` was changed.

## 1. Why route 1, and why the recorded blocker was overstated

r0047 recorded that "the route to `Thm29Normal` through Theorem 25 is now closed
at this tower". Re-derived rather than trusted, that statement is **sound but
narrower than it reads**, and the gap between what it says and what it was taken
to mean is the whole of this round's result.

| # | what is actually kernel-checked | declaration |
| -- | ------------------------------ | ----------- |
| 1 | Theorem 25's hypothesis is false at `A∞` | `R47.Agent1.not_hasNormalRealizations_Ainf` |
| 2 | its stagewise residue is false too | `R47.Agent1.not_stagewise_realizations` |
| 3 | Gunter's Lemma 24 holds at `M(A)`, against the connecting map `η` | `R47.Agent1.lemma24_MPair`, `lemma24_Step` |

Rows 1 and 2 quantify over **every** finite normal `A ◁ A∞` — including
`A = im(incl 1) = {⊥, β}`, the one the refutation uses. `Thm29Normal` quantifies
existentially: it asks that **some** normal embedding `K(E) → A∞` exist. A
construction is free to choose where its copies sit, and rows 1 and 2 say nothing
about copies the construction never builds.

Row 3 was built in r0047 and then **left unused**, because the `η`-copy of a stage
inside the next stage is not the tower's inclusion (`Colimit.stgEmb_ne_mk_eta`).
That is fatal for *extending* an embedding already fixed in `A∞`. It is not fatal
for *building* one: a finite poset is finished after finitely many steps, and only
the final stage has to be mapped into `A∞`.

So: **run Gunter's induction inside the stages along `mk ∘ η`, and apply `incl`
once, at the end.** Nothing in the argument contradicts rows 1 and 2; the
environment containing both was built and the kernel accepted it.

Why not the other two routes:

* **Route 2, refute `Thm29Normal`.** I looked for the invariant that would do it
  and found the opposite. The order on `Step α` is `⟨x,U⟩ ⊑ ⟨y,V⟩ ⟺ y ∈ ↑U`, so a
  subset `A ⊆ Step α` is normal exactly when `{⟨x,U⟩ ∈ A : z ∈ ↑U}` is non-empty
  and directed for every `z ∈ α`. That criterion is satisfiable for every finite
  pointed poset — which is what the theorem below proves. `β`'s maximality
  constrains *which* copies are normal, not *whether* one exists, exactly as
  r0047 said. Route 2 is not merely unattempted; for finite `E` it is now
  **refuted**, since `thm29Normal_finiteBasis` exhibits the embeddings.
* **Route 3, build the `η`-tower.** It discharges Theorem 29's second sentence for
  a *different carrier* and leaves Lemma 30 at `V`, where every conjunct consumes
  `Colimit.isoPlus`. It is also a second `Colimit.lean`-sized construction. Route
  1 reuses the machinery that already exists.

## 2. What is proved

| # | declaration | statement | axioms |
| -- | ----------- | --------- | ------ |
| 1 | `exists_stage_succ` | a normal copy of `S ⊆ P` in `Stg k` extends to a normal copy of `insert X S` in `Step (Stg k) = Stg (k+1)` | `[propext, Classical.choice, Quot.sound]` |
| 2 | `exists_stage_embedding` | every finite `P` with `⊥` has an order-reflecting `h : P → Stg k` with `range h ◁ Stg k` | same |
| 3 | `exists_normal_embedding_Ainf` | **`A∞` is universal for the finite pointed posets** | same |
| 4 | `thm29Normal_finiteBasis` | `LemThirty.Thm29Normal` with `Finite ↥(compacts E)` added | same |
| 5 | `thm29Normal_finiteBasis_of_thm29Normal` | `Thm29Normal` implies 4 — the added binder only weakens | same |
| 6 | `exists_normal_embedding_chain` | closed instance at `Fin 4`, so 3 is inhabited and not only quantified | same |

No `sorryAx` anywhere. `scripts/axioms.sh` was run over all six.

The argument in three steps.

**Step 1 is the only new mathematics.** Given `h '' S ◁ Stg k` and `X ∉ S` with
`insert X S ◁ P`, the pair `(P, X)` *is* a normal type over `h '' S` in exactly the
shape `lemma24_Step` consumes: the witnessing poset is `P` itself, the
order-reflecting map back is `Function.invFunOn h S`, and the two normality
hypotheses are `S ◁ P` and `insert X S ◁ P`. Lemma 24 returns a point `q` of
`Stg (k+1)` realizing that type over the `η`-image, plus the normality of the
one-point extension. This is the first use of r0047's `lemma24_Step`.

**Step 2 is Gunter's Proposition 21, already proved in r0046** as
`R46.Agent2.exists_singleton_step`: adjoining a point *maximal in `P ∖ S`* keeps
normality. Iterating it on `Set.ncard (univ ∖ S)` gives the chain
`{⊥} = S₀ ⊊ ⋯ ⊊ Sₙ = P` with singleton steps. The induction is
`R46.Agent2.hasFiniteExtensions_of_hasNormalRealizations`'s, with the appeal to
the refuted realization property replaced by step 1 — which pays for each point
by moving one stage up the tower instead.

**Step 3** carries the last stage into `A∞`: `incl k` is order-reflecting
(`Colimit.incl_le_incl`) with normal range (`Colimit.isNormalIn_range_incl`), so
`Colimit.isNormalIn_image_range` and `IsNormalIn.trans` finish.

## 3. A measurement worth recording: every finite poset is a Plotkin order

`IsNormalIn.refl` gives `Set.univ ◁ Set.univ` for free — `N ∩ ↓x` at `N = univ`
has `x` itself as greatest element — so `IsPlotkinOrder (Set.univ : Set P)` holds
for **every** poset `P`, and `IsBifinite E` is vacuous whenever `compacts E` is
finite. Consequently:

* `thm29Normal_finiteBasis` carries `IsBifinite E` only to line up with
  `Thm29Normal`'s shape and **never uses it**; `[Domain E]` is likewise unused
  here (it is load-bearing only in the infinite case, per
  `R45.Agent3.not_thm29NormalWithoutDomain`).
* the poset-level theorem `exists_normal_embedding_Ainf` is therefore the
  substantive one: it has three hypotheses, all type-class — `PartialOrder`,
  `Finite`, `OrderBot` — and no order-theoretic side condition at all.

## 4. Per-claim status

| # | Claim | Status | Evidence |
| -- | ---- | ------ | -------- |
| 1 | `A∞` universal for finite pointed posets | **discharged** | `exists_normal_embedding_Ainf`, `exists_normal_embedding_chain` |
| 2 | `LemThirty.Thm29Normal` | **reduced** — finite-basis case closed, infinite-basis case open | `thm29Normal_finiteBasis` + `thm29Normal_finiteBasis_of_thm29Normal` |
| 3 | `Thm29Normal` at `Finite ↥(compacts E)` | **discharged-at** (added binder), *not* a discharge | `thm29Normal_finiteBasis` |
| 4 | "route through Theorem 25 is closed" (r0047's recorded blocker) | **overstated** — closed for *extension*, not for *construction* | this file's route 1 |
| 5 | route 2, refuting `Thm29Normal` outright | **refuted for finite `E`**; open for infinite `E` | claim 3 exhibits the embeddings |
| 6 | `LemThirty.Thm29SecondAtDomains`, `Lemma30AtV` | **open** — unchanged | both need `Thm29Normal` at infinite bases |

Claim 3 is reported as *discharged-at* deliberately, and claim 5 of the plan's
evidence rules is why `thm29Normal_finiteBasis_of_thm29Normal` exists: it
kernel-checks that the added binder weakens rather than replaces, so the
classification is checkable and not asserted.

## 5. The residue, located to one sentence

For `K(E)` infinite the construction must produce a **nested** chain of copies
inside `A∞`, so step `i+1` has to realize a normal type over `incl kᵢ '' Aᵢ` — the
*tower's* image — whereas `lemma24_Step` realizes it over the `η`-image, and
`Colimit.stgEmb_ne_mk_eta` says those differ. That is precisely the sentence
`LemThirty.lean:479–485` defers to [Gun87], and
`R47.Agent1.not_stagewise_realizations` refutes its **unrestricted** form.

What is *not* known, and is asserted nowhere in this development: whether it holds
when the subposet is required to contain no maximal point of `A∞`. That
restriction is not arbitrary — `not_hasNormalRealizations_of_maximal` is the
**only** mechanism by which either refutation operates, and it needs a maximal
point of `A∞` inside the subposet. Every copy this file's construction builds
lies in the `η`-image of a stage, whose pairs have non-empty cover and therefore
non-empty cover at every later stage, so **no copy built here contains a maximal
point of `A∞`** — the refuting configuration is one the construction cannot
produce.

This is recorded in prose and in `A5Thm29Finite.lean`'s module docstring, **not**
as a `Prop`-valued `def`, per the round's hard rules: nothing here attempts it,
and an unattempted `def` is invisible to the `sorry` count.

## 6. One correction owed to the record

`LemThirty.lean:471` says the gap is "at getting `K(E)` into `A∞` at all". After
this round that is true only for infinite `K(E)`; for finite `K(E)` there is no
gap. `docs/Status.md` row 4 of the open-propositions table ("the `M(f)` tower
refutes Theorem 25's hypothesis; the `η` tower is not a fixed point. Three routes
named, one is refuting it outright") should record that route 1 has been taken and
carries the finite half, and that route 2 is refuted on that half. I changed no
existing file, so this is reported rather than applied.
</content>
