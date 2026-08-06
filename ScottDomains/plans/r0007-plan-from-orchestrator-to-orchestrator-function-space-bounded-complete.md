---
round: r0007
from: orchestrator
to: orchestrator
subject: function-space-bounded-complete
date: 2026-0806-14:07
status: done
related:
  - plans/r0006-plan-from-orchestrator-to-orchestrator-function-space.md
  - reports/r0006-report-from-orchestrator-to-user-function-space.md
---

# r0007 — `D → E` is bounded complete whenever `E` is

Completes the first sentence of Theorem 7's proof, which r0006 delivered only
half of:

> It is not hard to see that `D → E` is a bounded complete cpo whenever `E` is.

r0006 gave the cpo. This round gives bounded completeness, and in doing so
corrects a design decision in r0006 that would otherwise make the statement
false as formalized.

## The defect r0006 left behind

r0006 defined `sSup` on `ScottHom α β` by `dite` on **directedness**: the
pointwise supremum when the set is directed, the constant-`⊥` function otherwise.
`BoundedComplete` asks that `IsLUB s (sSup s)` for every `s` that is merely
`BddAbove`. A bounded set of functions need not be directed, so for such a set
r0006's `sSup` returns the junk value and `IsLUB` fails. **`BoundedComplete (ScottHom α β)`
is not provable against r0006's `SupSet` instance.** This is not a gap in the
mathematics; it is the wrong branch condition.

The fix is to branch on the property actually needed:

```
sSup d := if h : ScottContinuous (fun x => sSup ((· x) '' d)) then ⟨_, h⟩ else const ⊥
```

Continuity of the pointwise supremum is exactly the condition under which the
pointwise supremum is the right answer. Directedness and bounded-above are then
two *sufficient* conditions for taking the true branch, each proved separately,
and neither is privileged in the definition. `SupSet` remains total; the junk
value is still unobservable, because both consumer classes only ever constrain
`sSup` where the pointwise supremum is continuous.

## The proof is r0006's, with one lemma swapped

The four-step argument of `scottContinuous_pointwiseSup` never used directedness
of `d` except through `DirectedOn.sSup_le` and `DirectedOn.le_sSup` on the
evaluation image `(· x) '' d`. In the bounded case the same two facts come from
`BoundedComplete.isLUB_sSup_of_bddAbove` applied to that image, which is bounded
because `f x ≤ g x` for the bound `g`. The steps are otherwise identical:

1. the evaluation image is bounded above (was: directed);
2. the pointwise supremum is monotone;
3. it bounds the image of any directed `s`;
4. it is the least such, via continuity of each `f ∈ d`.

Because the shared structure is real, step 3 below factors it out rather than
copying the script twice.

## Steps, each with its verification

| # | Step | Verify |
| -- | ---- | ------ |
| 1 | Rewrite the `SupSet` instance to branch on `ScottContinuous` of the pointwise supremum | elaborates |
| 2 | `coe_sSup_of_continuous` — the defining equation under the branch hypothesis | `dif_pos` |
| 3 | `scottContinuous_pointwiseSup_of_forall_isLUB` — the shared four-step argument, taking as hypothesis that each evaluation image has `sSup` as its least upper bound | the r0006 script with `DirectedOn.sSup_le`/`le_sSup` replaced by the hypothesis |
| 4 | `scottContinuous_pointwiseSup` (directed) — restated via step 3 | `DirectedOn.isLUB_sSup` supplies the hypothesis |
| 5 | `scottContinuous_pointwiseSup_of_bddAbove` — needs `[BoundedComplete β]` | `isLUB_sSup_of_bddAbove` supplies the hypothesis; the image is bounded by the bound on `d` |
| 6 | `coe_sSup_of_directed` — unchanged statement, re-proved through steps 2 and 4 | downstream uses in r0006 keep working |
| 7 | `coe_sSup_of_bddAbove` | as step 6, through step 5 |
| 8 | `instance : BoundedComplete (ScottHom α β)` given `[BoundedComplete β]` | upper bound and least, pointwise, exactly as `lubOfDirected` |
| 9 | The r0006 `CompletePartialOrder` instance still builds unchanged | no edit to it beyond what step 6 makes automatic |
| 10 | `lake build`; `#print axioms`; the two no-diamond `rfl` examples still typecheck | 0 errors, 0 warnings, 0 `sorry` |
| 11 | `docs/PaperInventory.md` progress table; `INDEX.md`; regenerate the PDF | Theorem 7's first sentence recorded as done |

Steps 1→2, 3→{4,5}, {4,6}, {5,7}, 7→8 are the dependencies. Span is 4 sequential
elaborations.

## Acceptance criteria

| # | Criterion | Measurement |
| -- | --------- | ----------- |
| 1 | Builds | `lake build` exits 0, 0 errors, 0 warnings |
| 2 | Nothing unproved | `grep -c sorry` = 0; no `sorryAx` |
| 3 | The paper's sentence holds in full | `BoundedComplete (ScottHom α β)` is an instance, given `[BoundedComplete β]`, alongside r0006's `CompletePartialOrder` |
| 4 | The r0006 API survives | `coe_sSup_of_directed` keeps its statement; the two no-diamond examples still typecheck |
| 5 | The shared argument is shared | steps 4 and 5 are each ≤ 3 lines, both delegating to step 3 — the four-step script appears once |

## Out of scope

Step functions, algebraicity of the function space, and Theorem 7 itself. After
this round the remaining half of Theorem 7 is exactly the paper's second
sentence: exhibiting the basis.
