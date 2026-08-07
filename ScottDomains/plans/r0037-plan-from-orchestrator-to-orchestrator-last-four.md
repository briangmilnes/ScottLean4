---
round: r0037
from: orchestrator
to: orchestrator
subject: last-four
date: 2026-0807-11:09
status: pending
related:
  - plans/r0036-plan-from-orchestrator-to-orchestrator-five-way-open-results.md
  - docs/PaperInventory.md
  - docs/Performance.md
---

# r0037 — Five-way plan for the last four numbered results

Four results remain open: **Thm 18, Lem 28, Thm 29's second sentence, Lem 30.**
Five streams, because Theorem 18 is two unrelated pieces of work and Lemma 28's
seven remaining conjuncts are roughly 900 lines.

## Baseline, measured this session

`main` at `cb22b97`, working tree clean, all six worktrees at it.

| # | Quantity | Value | Measured by |
| -- | -------- | ----- | ----------- |
| 1 | Build | `Build completed successfully (1217 jobs).`, 0 errors, 0 diagnostics, 0 non-`sorry` warnings | `scripts/compile.sh -r r0036` |
| 2 | Modules / lines / theorems | 66 / 23596 / 1119 | `scripts/counts.sh` |
| 3 | `sorry` | **1** — `Skeleton/Section6.lean:197` (`thm18`) | `scripts/counts.sh` |
| 4 | Numbered results complete | 24 of 29; Thm 16 settled in all three directions, counted in neither column | `docs/PaperInventory.md` |

## Two facts r0036 established that change what is now cheap

Both are cross-stream, and neither is visible from any single r0036 report — each
agent knew only its own half. **Read these before reading your stream.**

1. **`Lemma28AtU` is unblocked.** `PRep.lean:114–119` records the instantiation
   at §7.3's `U` as "blocked one level below this file", because `Dyadic.thm27`
   was conditional on `IsNormallyRepresented`. **agent3 discharged that in the
   same round** — `Atomless.thm27` carries no hypothesis. The note is stale, and
   nobody has claimed the instantiation.
2. **Lemma 30's conjuncts are statable now.** `Colimit.lean:1008` says the
   paper's other nine operators "are not present in this development as functions
   `Cpo → Cpo` at all". That was true when agent5 wrote it and is **false on
   merged `main`**: `PRep.lean:147–189` defines all nine — `funOp`,
   `strictFunOp`, `prodOp`, `smashOp`, `sepSumOp`, `coalSumOp`, `liftOp`,
   `smythOp`, `hoareOp`. Lemma 30 differs from Lemma 28 only in the carrier
   (`V` instead of `U`) and in adding `()♮`.

## The five streams

| # | Agent | Namespace | Target |
| -- | ----- | --------- | ------ |
| 1 | agent1 | `ScottDomains.JungFinite` | Thm 18: Jung's Lemma 1.29, then step 4 (Lemma 2.2) |
| 2 | agent2 | `ScottDomains.JungNets` | Thm 18: step 1, Jung's Theorem 1.37 |
| 3 | agent3 | `ScottDomains.PRepFun` | Lem 28's `→`, `⇸`, `⊗` |
| 4 | agent4 | `ScottDomains.PRepSum` | Lem 28's `+`, `⊕`, `()♯`, `()♭`, and `Lemma28AtU` |
| 5 | agent5 | `ScottDomains.LemThirty` | Thm 29's second sentence, and Lemma 30 over `V` |

None collides with an existing namespace. Streams 3 and 4 both extend `PRep`;
they import it and add to their own namespaces, never to `PRep` itself.

## Dependencies — all merge-order, none launch-order

1. Streams 1 and 2 both feed `thm18` and touch **disjoint statements**: stream 1
   assumes property m as a hypothesis, stream 2 proves it. The assembly is an
   `exact` at merge time. Neither waits.
2. Stream 5 reuses `PRep`'s nine operators at carrier `V`. Those are already on
   `main`, so there is nothing to wait for; only the *conjunct proofs* from
   streams 3 and 4 might transfer, and that is a merge-time question.

Launch all five at once.

## Expected outcome

| # | Case | Numbered results | `sorry` |
| -- | ---- | ---------------- | ------- |
| 1 | Baseline | 24 of 29 | 1 |
| 2 | Streams 1 and 2 both land | 25 | **0 — first time** |
| 3 | Streams 3 and 4 also land | 26 | 0 |
| 4 | Stream 5 lands in full | 28 | 0 |

**Case 3 is the target; case 4 is not the forecast.** Stream 2 is the one most
likely to miss — Jung's Theorem 1.37 is the largest unbuilt prerequisite left,
needing ordinal-indexed codirected nets, interpolation, and a retraction onto
`A ∪ αᵒᵖ`, none of which the development quantifies over. If it misses, `thm18`
stays a `sorry` with its hypothesis precisely located rather than proved, which
is a real deliverable and is how `Section62.lean` already reads. Lemma 30's ten
conjuncts over a carrier built the same day is the other stretch.

Note the 29th result is Thm 16, which is settled in three directions but is not
a proof of the paper's sentence; 28 of 29 is therefore the ceiling this round can
reach.

## Process rules for every agent plan

r0028–r0036's rules all held. r0036 adds one.

1. **Namespace per agent** — as assigned. Zero collisions r0029–r0036.
2. **Script names are namespaced too.** *New this round.* r0036's agent4 and
   agent5 each wrote `scripts/pdf-section.sh` with incompatible interfaces and it
   collided at merge — the same failure the namespace rule prevents for Lean
   declarations, one directory over. Check `scripts/` before writing, and reuse
   what is there: `pdf-render.sh`, `pdf-crop.sh`, `pdf-find-page.sh` and
   `pdf-section.sh` all exist and read the source paper.
3. **Edit/Write only, never heredocs, never `sed -i`.**
4. **One command per Bash call. Never chain, never `cd`.**
5. **Multi-step work becomes a script in `scripts/`** — standing-authorized.
6. **Read the PDF, not the paraphrase.** r0036 produced three corrections this
   way, including Lemma 28's operator list and Lemma 30's tenth conjunct.
7. **The plan is not evidence.** r0034: four of six stream descriptions wrong.
   r0036: three. Contradicting this plan from the source is expected behaviour.
8. **Commit at every stopping point**, including with build errors.
9. **Agents commit, only the orchestrator pushes.**
10. **No new `sorry`.** An unproved step is a named `Prop` or a docstring
    obstruction — `Section62.lean` and `Colimit.lean` are the templates.

## Orchestrator steps

1. Cut five per-agent plans, commit to `main`, fast-forward the worktrees.
2. Launch five agents.
3. On each report: verify independently — build, `scripts/counts.sh`,
   `scripts/axioms.sh` on the headline declarations, and **read the statement**
   to confirm it was not weakened. r0036 caught nothing this way, but the check
   is what makes the reports load-bearing.
4. Merge one branch at a time; never `scripts/merge-round.sh` while agents run,
   since agents commit work in progress including with build errors.
5. Composition check with `scripts/axioms.sh -i` over every new module together.
6. Rewrite `docs/PaperInventory.md` rows 2, 2c, 2d, 5, 6 and the affected
   per-result rows from measured counts, then regenerate the PDF with
   `scripts/md2pdf.sh`.
