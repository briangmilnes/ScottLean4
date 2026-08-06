---
round: r0007
from: orchestrator
to: user
subject: function-space-bounded-complete
date: 2026-0806-14:12
started: 2026-0806-14:07
finished: 2026-0806-14:12
related:
  - plans/r0007-plan-from-orchestrator-to-orchestrator-function-space-bounded-complete.md
  - reports/r0006-report-from-orchestrator-to-user-function-space.md
---

# r0007 — `D → E` bounded complete: result

`ScottDomains/ScottHom.lean` grows from 200 to 269 lines. Theorem 7's first
sentence now holds in full: `D → E` is a bounded complete cpo whenever `E` is.
0 `sorry`, 0 warnings, built first try after the edit. Elapsed 5 minutes.

| # | Criterion | Measurement |
| -- | --------- | ----------- |
| 1 | Builds | `lake build` exits 0, 0 errors, 0 warnings, 0.7 s |
| 2 | Nothing unproved | `grep -c sorry` = 0; no `sorryAx` |
| 3 | The paper's sentence holds in full | `instance [BoundedComplete β] : BoundedComplete (ScottHom α β)`, alongside r0006's `CompletePartialOrder`. Both resolve for the concrete `ScottHom (Set ℕ) (Set ℕ)` |
| 4 | The r0006 API survives | `coe_sSup_of_directed` keeps its exact statement; both no-diamond `rfl` examples still typecheck |
| 5 | The shared argument is shared | the four-step script appears once; the directed and bounded cases are one line each |

## A defect in r0006, found by trying to state the next theorem

r0006 defined `sSup` on `ScottHom α β` by a case split on **directedness**.
`BoundedComplete` requires `IsLUB s (sSup s)` for every `s` that is merely
`BddAbove`, and a bounded set of functions need not be directed — so on such a
set r0006's `sSup` returns the constant-`⊥` junk value and `IsLUB` is false.
**`BoundedComplete (ScottHom α β)` was not provable against r0006's instance.**

The mathematics was never wrong; the branch condition was. r0006 chose
directedness because that was the only sufficient condition it needed at the
time. The correct condition is the one that actually makes the pointwise
supremum the right answer:

```
sSup d := if h : ScottContinuous (fun x => sSup ((· x) '' d)) then ⟨_, h⟩ else const ⊥
```

Directedness and boundedness are now two *sufficient* conditions for taking the
true branch, proved separately, neither privileged in the definition. This is
worth recording as a general lesson: a `dite` guard should name the property the
true branch needs, not the property the first caller happens to have.

## The proof was already shared, once it was asked to be

The four-step argument of `scottContinuous_pointwiseSup` never used directedness
of `d` directly — only `DirectedOn.sSup_le` and `DirectedOn.le_sSup` on the
evaluation image. Abstracting that to the hypothesis

```
∀ x, IsLUB ((· x) '' d) (sSup ((· x) '' d))
```

gives `scottContinuous_pointwiseSup_of_forall_isLUB`, and both cases are then one
line:

| # | Case | Supplies the hypothesis |
| -- | ---- | ----------------------- |
| 1 | directed | `DirectedOn.isLUB_sSup` |
| 2 | bounded above, `E` bounded complete | `isLUB_sSup_of_bddAbove` on `bddAbove_eval_image` |

The generalized lemma is *simpler* than the special case it replaced: it names
what the argument uses instead of what the caller has.

## Axioms

`scottContinuous_pointwiseSup_of_forall_isLUB`, and both of its instantiations,
depend on `propext` and `Quot.sound` only — no `Classical.choice`. Choice still
enters exactly where `SupSet`'s totality forces the case split
(`coe_sSup_of_*` and the instances). The classical dependency did not spread when
the condition changed.

## Where Theorem 7 now stands

The paper's sketch reads: "It is not hard to see that `D → E` is a bounded
complete cpo whenever `E` is. To prove that `D → E` is a domain we must
demonstrate its basis." The first sentence is done. The second is the whole of
the remaining work: given finite `N ⊆ K(D)` and monotone `s : N → K(E)`, the step
function `step(s)` is compact in `ScottHom`, and the step functions form a basis.

Counts are unchanged — **9 definitions and 28 results remaining** — because
Theorem 7 is not yet complete. `docs/PaperInventory.md` and `INDEX.md` record the
half that is.
