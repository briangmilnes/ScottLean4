---
round: r0042
from: agent1
to: orchestrator
subject: corollary-136
date: 2026-0808-14:22
started: 2026-0808-13:58
finished: 2026-0808-14:22
related:
  - ScottDomains/plans/r0042-plan-from-orchestrator-to-orchestrator-clear-the-sorry.md
  - ScottDomains/ScottDomains/JungCor136.lean
  - ScottDomains/ScottDomains/JungFinite.lean
---

# r0042 stream 1 — Jung's Corollary 1.36, proved

## Result

Acceptance level 1. **Corollary 1.36 is proved, and it discharges
`JungFinite.FixedPointOfCompactDeflationIsCompact`.** Theorem 18 now rests on
**one** open proposition, `JungNets.Thm137`, not two.

| # | Declaration | Statement | Axioms |
| -- | ----------- | --------- | ------ |
| 1 | `JungCor136.apply_wayBelow_of_wayBelow_idHom` | Proposition 1.34: `f ≪ id_D` ⟹ `f d ≪ d` for all `d` | `propext, Classical.choice, Quot.sound` |
| 2 | `JungCor136.apply_wayBelow_apply` | Corollary 1.36: `f ≪ g` ⟹ `f d ≪ g d` for all `d` | same |
| 3 | `JungCor136.isCompactElement_apply` | a compact function has compact values | same |
| 4 | `JungCor136.fixedPointOfCompactDeflationIsCompact` | `JungFinite.FixedPointOfCompactDeflationIsCompact α` | same |

Row 4 is the deliverable agent5 composes. Row 2 is the paper's statement in full
generality, not only the `g = id` instance the development consumes; row 3 is the
`f = g` instance and is the sharpest single sentence of the file.

Hypotheses: `[CompletePartialOrder α] [IsAlgebraic (ScottHom α α)]`. **`IsAlgebraic α`
is never used.** Both `JungFinite.lemma22` and `JungFinite.thm18_of_propertyM`
already carry `IsAlgebraic (ScottHom α α)` — the second through
`Domain (ScottHom α α)` — so nothing new is asked of the caller.

## Measurements

| # | Quantity | Value |
| -- | -------- | ----- |
| 1 | full build | 1299 jobs, **0 errors, 0 non-`sorry` warnings** |
| 2 | build wall clock / peak RSS | 3.32 s · 1777 MiB single, 15519 MiB tree |
| 3 | `sorry` before / after | 1 / **1** — `Skeleton/Section6.lean:197`, unchanged |
| 4 | new module | `ScottDomains/JungCor136.lean`, 443 lines, 25 declarations |
| 5 | repository totals after | 95 modules, 34703 lines, 1676 theorems |
| 6 | composition check | `scripts/a1-check-thm18-after-cor136.sh` — exit 0 |

Row 6 elaborates, in one environment that `lake build` never forms,

```
thm18_of_jung_1_37 : JungNets.Thm137 α → IsBifinite α
```

for `[CompletePartialOrder α] [Domain α] [Domain (ScottHom α α)]`, on the three
standard axioms. That is `scripts/check-thm18-composition.sh` with its second
hypothesis deleted and `JungCor136.fixedPointOfCompactDeflationIsCompact` supplied
in its place.

## The proof is not Jung's, and is shorter

I read Jung's §1.5 from the PDF (printed pages 46–50; extracted with
`scripts/a1-jung-extract.sh`). His proof of Proposition 1.34 runs:

> Let `d` be an element of `D` and let `(e_j)_{j∈J}` be a directed family of
> elements with `⨆↑ e_j = e ≥ d`. By Proposition 1.22 the function space of `↓e`
> is also continuous. We use Proposition 1.5 in order to show that `f' = f|↓e` is
> way-below `id_{↓e}`. … The collection `(e_j)` defines a directed family of
> constant functions `(c_{e_j})` on `↓e`, the supremum of which is `c_e`. This is
> the largest function on `↓e` and hence is above `id_{↓e}`. Therefore there is
> some function `c_{e_j}` which is above `f'` and this implies `e_j = c_{e_j}(d) ≥
> f'(d) = f(d)`.

Three prerequisites (Propositions 1.22, 1.5 and the retraction), one subtype, and
one retraction pair. **The plan is not evidence, and neither is Jung.** Two
corrections to the plan's row 1, both from the source:

1. **Proposition 1.5 is a second prerequisite the plan does not name.** The plan
   says 1.36 "needs his Proposition 1.34". It needs 1.34, which in turn needs both
   Proposition 1.22 *and* Proposition 1.5(i) — "if `D` is a continuous dcpo then
   `x ≪ y` iff for all directed `A` with `⨆↑A = y` there is `a ∈ A` with `a ≥ x`."
   That is the bridge from families whose supremum *is* `id_{↓e}` (all of whose
   members are therefore deflations, which is what makes his extension by the
   identity monotone) to the constants family, whose supremum is `c_e ⊒ id_{↓e}`
   and strictly above it. Without 1.5 the two halves of Jung's proof do not meet.

2. **Jung asserts `↓e` is a retract of `D` and never says why.** Proposition 1.22
   is stated for a retract `E` of `D`; the proof of 1.34 applies it to `↓e` with no
   argument. It is true, and the witness is cheap: `x ↦ x` on `↓e` and `x ↦ e` off
   it. Monotone because `↓e` is a lower set, so the bad case (`x ⊑ e`, `y ⋣ e`,
   `x ⊑ y`) needs only `x ⊑ e`, and the reverse case cannot occur. Scott continuous
   because a directed set whose supremum escapes `↓e` already has a member outside
   `↓e`. That gap is worth recording, and closing it is what made the shorter route
   visible.

The route taken here **never forms `↓e`** and uses neither Proposition 1.22 nor
Proposition 1.5. Two explicit functions on `D` replace them:

| # | Function | Definition | Role |
| -- | -------- | ---------- | ---- |
| 1 | `cap e` | `x ↦ if x ⊑ e then x else e` | Jung's retraction onto `↓e`, kept on `D` |
| 2 | `extend e F` | `x ↦ if x ⊑ e then F x else x` | extension of `F` by the identity off `↓e` |

Given `f ≪ id_D` and directed `s` with `IsLUB s e` and `d ⊑ e`:

1. `{extend e F | F ∈ K(D → D), F ⊑ cap e}` is directed with least upper bound
   `id_D`. The least-upper-bound half is `ScottHom.isLUB_eval_image_of_isLUB`
   against `IsAlgebraic.isLUB_compactsBelow (cap e)`, evaluated at points of `↓e`;
   off `↓e` every member already *is* the identity.
2. `f ≪ id_D` applied to that family yields a **compact** `F ⊑ cap e` with
   `f ⊑ extend e F`.
3. The constants `{c_z | z ∈ s}` are directed with least upper bound `c_e`, and
   `F ⊑ cap e ⊑ c_e` because `cap e` is bounded by `e` **everywhere on `D`**.
   Compactness of `F` gives `z ∈ s` with `F ⊑ c_z`.
4. `d ⊑ e`, so `f(d) ⊑ (extend e F)(d) = F(d) ⊑ z`.

Step 3 is where Jung needs `↓e`'s top element; `c_e` supplies it on all of `D`.
Step 2 is where the restriction route died in r0037 and where it now lives: the
family is indexed below **`cap e`**, not below `idHom`, and `F ⊑ cap e` is exactly
`F x ⊑ x` on `↓e` — precisely the condition that makes extension by the identity
monotone, and precisely what r0037's docstring measured as missing. r0037 was
right that `IsCompactElement (f|↓c)` does not follow; the fix is not to prove it
but to never need it — the compactness consumed at step 3 is that of the
*approximant* `F`, not of `f`.

Corollary 1.36 then follows in Jung's own four lines: `g` is the least upper bound
of `{p ∘ g | p ⊑ id}` (algebraicity of the function space, plus
`isLUB_eval_image_of_isLUB` at `g x`), so `f ≪ g` produces a compact `p ⊑ id` with
`f ⊑ p ∘ g`, and Proposition 1.34 gives `f(d) ⊑ p(g(d)) ≪ g(d)`.

## Scope of the hypothesis, stated honestly

The file states Proposition 1.34 under `IsAlgebraic (ScottHom α α)`, where Jung
states it under *continuity* of the function space. The proof does not depend on
that choice: with `{F | F ≪ cap e}` in place of `compactsBelow (cap e)`, and
`WayBelow F (cap e)` in place of compactness at step 3, the same script runs under
mere continuity. The development carries `IsAlgebraic` and has no `IsContinuous`
class, so the algebraic form is what is stated; the docstring records the
generalization.

## Files

| # | Path | Change |
| -- | ---- | ------ |
| 1 | `ScottDomains/ScottDomains/JungCor136.lean` | new, 443 lines |
| 2 | `ScottDomains/ScottDomains/JungFinite.lean` | docstring of `FixedPointOfCompactDeflationIsCompact`: the obstruction paragraphs are now marked as the pre-r0042 record and point at the proof. No code change, no signature change — `lemma22` and `thm18_of_propertyM` are untouched, so nothing agent5 reads has moved. |
| 3 | `scripts/a1-check-thm18-after-cor136.sh` | new: elaborates `Thm137 α → IsBifinite α` |
| 4 | `scripts/a1-jung-extract.sh` | new: page-range text extraction from the Jung PDF |

Commit `ed42c96` on branch `agent1`. Not pushed, per the agent rule.

## For the orchestrator

1. `JungFinite.lemma22` and `thm18_of_propertyM` still take `hcor` as an explicit
   hypothesis. That is deliberate: `JungCor136` imports `JungFinite`, so the
   discharge cannot be inlined without moving the predicate. Agent5 should apply
   `JungCor136.fixedPointOfCompactDeflationIsCompact` at the assembly site rather
   than re-plumb the import graph.
2. `docs/PaperInventory.md` row 2d says Theorem 18 "rests on **exactly two** named
   propositions". After merge that is one, `JungNets.Thm137`.
3. `JungCor136.isCompactElement_apply` — a compact element of `[D → D]` has compact
   values — is a general fact the development did not have, and is likely to be
   worth more elsewhere than the specialization it was built for.
