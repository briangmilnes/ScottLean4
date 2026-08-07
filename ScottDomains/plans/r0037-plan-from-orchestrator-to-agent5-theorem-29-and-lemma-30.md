---
round: r0037
from: orchestrator
to: agent5
subject: theorem-29-and-lemma-30
date: 2026-0807-11:09
status: pending
related:
  - plans/r0037-plan-from-orchestrator-to-orchestrator-last-four.md
---

# r0037 stream 5 — agent5 — Theorem 29's second sentence, and Lemma 30

Worktree `/home/milnes/projects/ScottLean4-agent5`, branch `agent5`.
Namespace **`ScottDomains.LemThirty`**.

## The goal

Two of the four remaining numbered results, both stated by you last round as
named `Prop`s rather than `sorry`s:

- **`Colimit.Thm29Second`** (`Colimit.lean:1012`) — Theorem 29's second sentence
  at `D = V`. The hypothesis `D ≅ D⁺` is already discharged, since you proved
  `isoPlus : V ≃o Plus V`. What remains is the universality extension step:
  extending a normal embedding of a finite normal subposet of `K(E)` into
  `Stg n` to the next one into `Stg (n+1)`.
- **`Colimit.Lem30Arrow`** (`Colimit.lean:1018`) and the rest of **Lemma 30** —
  ten conjuncts over `V`: Lemma 28's nine plus `()♮`, the convex powerdomain,
  which is the whole point of §7.4.

## Read this first: your own file's blocking note is stale

`Colimit.lean:1008` says the paper's other nine operators

> are not present in this development as functions `Cpo → Cpo` at all — so
> `Lem30Arrow` is the only [type-correct conjunct].

That was true when you wrote it and is **false on merged `main`**. agent4's
`PRep.lean:147–189` defines all nine as `Cpo → Cpo` / `Cpo → Cpo → Cpo`:
`funOp`, `strictFunOp`, `prodOp`, `smashOp`, `sepSumOp`, `coalSumOp`, `liftOp`,
`smythOp`, `hoareOp`. Neither of you could see the other's work.

**So Lemma 30 is statable in full today.** It differs from `PRep.Lemma28` in
exactly two ways: the carrier is `V` rather than `U`, and there is a tenth
conjunct `()♮` for the Plotkin (convex) powerdomain, which `Plotkin.Powerdomain`
has supplied since r0029 but which `PRep` does not define an operator for —
because it is not in Lemma 28. Define `plotkinOp` in your namespace, following
`PRep.smythOp`/`hoareOp`, and note what its `[Domain D]` is spent on.

## Order of work

1. **State Lemma 30 as one ten-fold conjunction** over `V`, with a
   `lemma30_of` taking ten named hypotheses — the shape `PRep.Lemma28` and
   `lemma28_of` use, and the shape r0034 adopted for Lemmas 10 and 17 precisely
   so conjunct counts are kernel-checked rather than prose. Two rounds were lost
   to prose counts drifting from the files, and this row of the inventory has
   already been wrong twice (nine versus ten). Do this before proving anything.
2. **Thm 29's second sentence.** It is a numbered result and Lemma 30's ten
   conjuncts are not; if the round runs short, the sentence is worth more.
3. **Whichever Lemma 30 conjuncts transfer.** Streams 3 and 4 are proving the
   same operators over `U` this round. Their proofs may transfer to `V` with the
   carrier changed — or may not, since `V`'s construction is a colimit and `U`'s
   is an ideal completion of a countable pre-order. **Check whether the proofs
   depend on anything but the `Fp` interface**; if they do not, say so, because
   that turns Lemma 30 into an instantiation rather than ten fresh proofs. That
   measurement is worth more than any single conjunct.

## What is already yours to build on

`V`, `Domain V`, `IsBifinite V`, `isoPlus : V ≃o Plus V`, the stage tower
(`Stg`, `stgEmb`, `liftStg`), and the kernel-checked correction that the
connecting map is **not** `eta` (`stgEmb_ne_mk_eta`). The stage counts 1, 2, 5,
**20** select `MPair.le` over the Smyth reading's 21; if anything you build
disagrees with those counts, stop and re-read rather than adjusting them.

## Acceptance, ranked

1. `Thm29Second` proved and Lemma 30 stated at ten conjuncts with several proved.
2. `Thm29Second` proved, Lemma 30 stated at ten — **Theorem 29 complete takes the
   numbered count to 27 of 29.** This is the target.
3. Lemma 30 stated at ten conjuncts with `plotkinOp` defined, plus the measured
   answer to whether streams 3 and 4's proofs transfer from `U` to `V`.
4. The ten-fold statement alone, correcting `Colimit.lean`'s stale note.

**No new `sorry`.** An unproved conjunct is a named `Prop` or a docstring
obstruction — `Colimit.lean` is already the template.

## Process rules

1. Namespace `ScottDomains.LemThirty`. Import `Colimit`, `PRep`,
   `BifiniteUniversal`, `Powerdomain/Plotkin`. You may correct `Colimit.lean`'s
   stale docstring note; new machinery goes in your namespace.
2. Edit/Write only. Never a heredoc, never `sed -i`.
3. One command per Bash call. Never chain, never `cd`.
4. Multi-step work becomes a script in `scripts/` — standing-authorized — but
   **check `scripts/` first and prefix any new script with your stream name**.
   r0036 lost a merge because you and agent4 both wrote `scripts/pdf-section.sh`
   with incompatible interfaces; the merged version accepts both call shapes.
5. Build with `/home/milnes/projects/ScottLean4-agent5/scripts/compile.sh -r r0037`.
6. Read §7.4 of the PDF directly. You found three printed defects in it across
   two rounds; expect more rather than fewer.
7. **This plan is not evidence.** The source wins; say so in the report.
8. Commit at every stopping point with
   `/home/milnes/projects/ScottLean4-agent5/scripts/gitcp.sh`. Do not push.
9. Report to
   `ScottDomains/reports/r0037-report-from-agent5-to-orchestrator-theorem-29-and-lemma-30.md`
   with `started`/`finished`, the transfer measurement from item 3, and a
   conjunct-by-conjunct table.
