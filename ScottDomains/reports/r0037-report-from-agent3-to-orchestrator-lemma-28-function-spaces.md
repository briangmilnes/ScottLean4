---
round: r0037
from: agent3
to: orchestrator
subject: lemma-28-function-spaces
date: 2026-0807-11:52
started: 2026-0807-11:14
finished: 2026-0807-11:52
related:
  - plans/r0037-plan-from-orchestrator-to-agent3-lemma-28-function-spaces.md
  - plans/r0037-plan-from-orchestrator-to-orchestrator-last-four.md
---

# r0037 stream 3 — Lemma 28's `→`, `⇸` and `⊗`, all three proved

Branch `agent3`, worktree `/home/milnes/projects/ScottLean4-agent3`.
One new module: `ScottDomains/ScottDomains/PRepFun.lean`, namespace
`ScottDomains.PRepFun`, 1267 lines, 67 declarations. No declaration was added to
`PRep`; no file outside `PRepFun.lean` and `ScottDomains/logs/` was touched.

## 1. Result

| # | Conjunct | Statement | Outcome | Hypotheses it carries |
| - | -------- | --------- | ------- | --------------------- |
| 1 | `→` | `IsPRepresentable₂ U funOp` | **proved** — `PRepFun.rep_arrow` | `[CompletePartialOrder U] [Domain U] [BoundedComplete U]`; the pair `fn : U → (U → U)`, `gr : (U → U) → U` with `fn ∘ gr = id` and `gr ∘ fn ⊑ id` |
| 2 | `⇸` | `IsPRepresentable₂ U strictFunOp` | **proved** — `PRepFun.rep_strictArrow` | the same, with the pair at `U ⇸ U` |
| 4 | `⊗` | `IsPRepresentable₂ U smashOp` | **proved** — `PRepFun.rep_smash` | `[CompletePartialOrder U] [Domain U]` only — **no `[BoundedComplete U]`** — and the pair at `U ⊗ U` |

The three statements are exactly the `h_arrow`, `h_strictArrow` and `h_smash`
hypotheses of `PRep.lemma28_of`, so they substitute into it without restatement.

Acceptance item 1 of the plan's ranked list is met: all three conjuncts proved at
`IsPRepresentable₂ U`.

## 2. Build and axiom measurements

| # | Quantity | Value | Measured by |
| - | -------- | ----- | ----------- |
| 1 | Build | `Build completed successfully (1218 jobs).` — 0 errors, 0 diagnostics, 0 non-`sorry` warnings | `scripts/compile.sh -r r0037`, log `compile-20260807-114916.agent3.log` |
| 2 | `sorry` | **1**, unchanged — `Skeleton/Section6.lean:197` (`thm18`), which is not this stream's | `scripts/counts.sh` |
| 3 | Modules / lines / theorems | 67 / 24863 / 1171 (baseline 66 / 23596 / 1119) | `scripts/counts.sh` |
| 4 | Axioms of `rep_arrow`, `rep_strictArrow`, `rep_smash`, `strictHomDomain`, `smashDomain`, `smashIsAlgebraic`, `isCompactElement_smash_coe_iff`, `isProjection_smashMap` | `[propext, Classical.choice, Quot.sound]` for all eight — no `sorryAx` | `scripts/axioms.sh` |

Nine build runs, seven of which reported errors; the largest error count in a
single run was six, all of them instance-resolution or coercion-level mismatches
rather than mathematical.

## 3. The source, read directly — the plan is confirmed, not corrected

Process rule 6 was followed: physical pages 41, 42 and 43 of
`ScottDomains/papers/Gunter Scott 1990.pdf` were rendered at 200 dpi with
`scripts/pdf-render.sh` and read as images, because `pdftotext` substitutes or
drops every operator glyph in the statement. Page 42 (printed folio 41) reads:

> **Lemma 28** *The following operators are representable over* `U`:
> `→`, `⇸`, `×`, `⊗`, `+`, `⊕`, `(·)⊥`, `(·)♯`, `(·)♭`.

Nine operators, the second drawn `∘→`. **`PRep.Lemma28`'s list is correct and
needs no change**, and the stream assignment (`→`, `⇸`, `⊗` as conjuncts 1, 2, 4)
matches the source's order. This is the first r0037 round item I am aware of
where reading the source produced no correction — r0034 produced four, r0036
three.

Two further sentences on the same page bear on the hypotheses:

1. **Theorem 27**: "For any bounded complete domain `D`, there is a projection
   `p : U → D`." So §7.3's `U` is universal for *bounded complete* domains, and
   the `[BoundedComplete U]` that `→` and `⇸` carry is the setting's own
   hypothesis rather than an artifact of the formalization.
2. "The proof that `→` is representable over `U` is almost identical to the proof
   we gave above that it is representable over `PN`." Measured against
   `Combinator.rep_arrow`, this is accurate about the *construction* and
   inaccurate about the *obligations* — see §5.

Page 43 confirms Lemma 30's ten operators (Lemma 28's nine plus `(·)♮`), which is
agent5's business but is recorded here since the page was read.

## 4. Two closure properties the library did not have

Both were needed because `Fp`'s second conjunct demands a `Domain` on `im(R q)`,
and both were absent from the library. This is the same gap the coordinator
relayed from agent5 mid-stream; I had measured it independently before the
message arrived, and I closed both halves rather than carrying either as a
hypothesis.

| # | Property | Was in the library? | Now |
| - | -------- | ------------------- | --- |
| 1 | `Domain (D →⊥ E)` | no — only `lem10_strict` (bounded complete) and `lem17_strictFun` (bifinite) | `PRepFun.strictHomDomain`, under `[Domain D] [Domain E] [BoundedComplete E]` |
| 2 | `IsAlgebraic (D ⊗ E)` and `Domain (D ⊗ E)` | no — only `lem10_smash` and `lem17_smash` | `PRepFun.smashIsAlgebraic`, `PRepFun.smashDomain`, under `[Domain D] [Domain E]` |

Measured: the `IsAlgebraic` instances in the whole development are `Set X`,
`ScottHom α β`, `α × β`, `WithBot α` and `IdealCompletion A`. Neither the strict
function space nor the smash was among them, and no round had recorded the
absence.

The two cost very different amounts, and the difference is structural:

- `D →⊥ E` is a **downward-closed** sub-cpo of `D → E` — anything below a strict
  function is strict (`isStrict_of_le`) — so the compact approximants of `f` in
  the subtype are literally those of `f.val` in `D → E`
  (`val_image_compactsBelow`), and both `IsAlgebraic` fields transport with no
  new argument. About 40 lines, resting on the two compactness transfers already
  in `ClosureProperties/StrictFunction.lean`.
- `D ⊗ E` has no such embedding into an algebraic space. Its algebraicity needs
  the compactness criterion `isCompactElement_smash_coe_iff` — `↑q` is compact in
  `D ⊗ E` exactly when `q.val` is compact in `D × E` — proved one direction
  through each of `ι` and `π` (§6), plus `exists_nonBot_of_isLUB`, which is the
  step that discards the compact approximants with a `⊥` coordinate and shows
  what remains is still cofinal. About 120 lines.

agent4's relayed assessment that the fix would need `isCompactElement_coe_smash_iff`
is **confirmed**: that criterion, under the name
`PRepFun.isCompactElement_smash_coe_iff`, is exactly the load-bearing lemma.

## 5. `→` measured against `Combinator.rep_arrow`

The plan asked whether r0034's closure-notion proof transfers. Seven ingredients,
of which five change:

| # | Ingredient | Closure notion (r0034) | Projection notion (here) |
| - | ---------- | ---------------------- | ------------------------ |
| 1 | conjugating family `(s, r)` | `compHom` | reused unchanged |
| 2 | monotonicity in `(r, s)` | `compHom_mono` | reused unchanged |
| 3 | the two equations | `isClosure_compHom` | `isProjection_compHom` — already existed in `Skeleton/Lemma17.lean` |
| 4 | `im((s,r)) ≅ im(r) → im(s)` | `evidentOrderIso` | **re-proved** as `evidentOrderIsoP` |
| 5 | `im(R(s,r))` a domain | not required | **new** — `domain_range_compHom` |
| 6 | the index least upper bound | `isLUB_val_image_of_isLUB` (free) | `PRep.isLUB_val_image_of_isLUB_fp'`, which costs `isFinitaryProjection_sSup` |
| 7 | the pair hypothesis | `Retracts U (U → U)`: `id ⊑ gr ∘ fn` | `gr ∘ fn ⊑ id` — incompatible; `PRep.gr_fn_eq_of_both` forces `U ≅ (U → U)` if both hold |

Row 4 is worth one line of detail. The two continuity lemmas `evidentOrderIso`
rests on both get **cheaper** at a projection: the inclusion `im(p) ↪ D` is
`IsProjection.isLUB_val_image`, already a theorem and needing neither
nonemptiness nor directedness, where the closure version builds the ambient
supremum and checks it lands back in the image; and the corestriction `x ↦ p x`
needs **no projection law at all** (`scottContinuous_corestrict` takes no
hypothesis), where the closure version spends `x ⊑ r x`.

The plan's row-7 warning was correct and load-bearing: `Combinator.rep_arrow` is
not conjunct 1 and was not reused.

## 6. `⇸` and `⊗`, briefly

**`⇸`** is `→`'s proof with strictness threaded through, as the plan predicted,
plus the `Domain (D →⊥ E)` of §4 — which is the part the plan did not predict and
which the plan said would be worth reporting if it appeared. The conjugating
family is the **same** `(q, p)` restricted, legitimate because
`ClosureProperties.isStrict_compHom` makes `(q,p) f` strict whenever `p`, `q` and
`f` are, and a projection is strict for free (`IsProjection.map_bot`). The
strictness side conditions of the range isomorphism are two equations,
`q (G ⊥) = ⊥` and `(F ⊥)ᵥ = ⊥`.

**`⊗`** turned on a decomposition. `D ⊗ E` sits against `D × E` by a
Scott-continuous pair

    ι : D ⊗ E → D × E   (adjoined bottom to `(⊥,⊥)`, a pair to itself)
    π : D × E → D ⊗ E   (a pair with a `⊥` coordinate to the adjoined bottom)

and `r ⊗ s = π ∘ (r × s) ∘ ι`, so continuity of the conjugating family is a
composite of three continuous maps rather than a case analysis over `Smash`'s
branching `sSup`. `ι` is not a retraction of `π` in either direction, so this is
a decomposition and not a conjugation. The same pair then carries the compactness
criterion of §4, one direction each.

**The plan's claim that `⊗` is "no longer refuted" is confirmed by the kernel.**
r0034's three-chain counterexample turns on `r ⊥` being allowed to sit strictly
above `⊥`. `isProjection_smashMap` is where the difference is spent: `r ⊥ = ⊥`
makes the collapse to the adjoined bottom idempotent. The change of notion was
the whole obstruction.

`⊗` also carries **one hypothesis fewer** than the two function spaces —
`[Domain U]` with no `[BoundedComplete U]` — because the function-space conjuncts
route their `Domain` obligation through `Domain (D → E)`, which the development
proves only for bounded complete `E` (Theorem 7), while `Domain (D ⊗ E)` needs
nothing beyond the two factors.

## 7. Lifting to §7.3's `U`

Per the coordinator's note: Theorem 27 supplies the retraction pair for an
operator whose *result* is a bounded complete domain, so a conjunct lifts from
the abstract `U` to `Dyadic.U` exactly when Lemma 10 and a `Domain` cover its
result type. All three of mine are covered:

| # | Conjunct | `BoundedComplete` of the result | `Domain` of the result |
| - | -------- | ------------------------------- | ---------------------- |
| 1 | `→` | `ScottHom`'s instance (Theorem 7) | `FunctionSpaceCountable.lean`'s instance |
| 2 | `⇸` | `lem10_strict` | `strictHomDomain` — **new here** |
| 4 | `⊗` | `lem10_smash` | `smashDomain` — **new here** |

Both new `Domain` halves are this stream's, so before this file no conjunct of
mine could have lifted to `U`. Whether they now do is a question about
`Dyadic.U`'s own `[Domain]` and `[BoundedComplete]` instances and about
`Atomless.thm27`'s exact statement, which is agent4's territory; I did not
attempt the instantiation, so as not to touch `Lemma28AtU` while agent4 held it.

## 8. Merge notes

1. **No collision.** Everything is under `ScottDomains.PRepFun` in one new file.
   `PRep` is imported and unmodified. No new script was written, so the r0036
   script-name collision cannot recur from this stream.
2. **agent4's constraint is respected.** Nothing here is a `Cpo`-valued `abbrev`;
   the file uses `PRep`'s existing `FpImage`, `strictFunOp` and `smashOp`, all of
   which are `def`s.
3. **Instance hygiene.** Where a statement mentions the cpo on `im(p)`, it names
   it through `(FpImage a).carrier` rather than re-synthesizing
   `IsProjection.rangeCompletePartialOrder`. Four of the seven failing builds
   were caused by mixing the two, and the `FpImage` form is the one that works.
   Anyone extending this file should follow it.
4. **Six commits**, each at a build with zero errors:
   `efdc1e6` (`→`), `76eb376` (`Domain (D →⊥ E)`), `0b4ccf3` (`⇸`),
   `707ad18` (`ι`/`π`), `3fb354e` (smash algebraicity), `9594298` (`⊗`).
   Not pushed, per the agents-commit-orchestrator-pushes rule; `gitcp.sh`
   reporting "no tracking information" on each is the expected outcome.

## 9. What this leaves open

Nothing in this stream. Lemma 28's remaining open conjuncts after this merge are
`(·)♯` and `(·)♭` (the Smyth and Hoare powerdomains), which were assigned to
nobody this round.
