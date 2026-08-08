---
round: r0042
from: agent5
to: orchestrator
subject: assembly
date: 2026-0808-14:14
started: 2026-0808-14:01
finished: 2026-0808-14:14
related:
  - ScottDomains/plans/r0042-plan-from-orchestrator-to-orchestrator-clear-the-sorry.md
  - ScottDomains/ScottDomains/Thm18.lean
  - ScottDomains/ScottDomains/Closure.lean
---

# r0042 stream 5 — the assembly, the statement audit, and the blocker the plan did not know about

Three results. Part 1 delivered: the reduction is a library theorem. Part 2
delivered: `thm18`'s Lean statement **is** Gunter & Scott's sentence, on every
reading checked. Part 3 could not be executed — the two propositions it needs are
on other branches — but executing it was **not** the one-line edit the plan
assumes, and stream 5 removed the reason why.

## Part 1 — the reduction is now a declaration

`ScottDomains/Thm18.lean`, namespace `ScottDomains.Thm18`, three theorems, all
under `[CompletePartialOrder α] [Domain α] [Domain (ScottHom α α)]`:

| # | Declaration | Statement |
| -- | ----------- | --------- |
| 1 | `thm18_of_thm137Chains_and_cor136` | `JungNets.Thm137Chains α → JungFinite.FixedPointOfCompactDeflationIsCompact α → IsBifinite α` |
| 2 | `thm18_of_thm137_and_cor136` | `JungNets.Thm137 α → JungFinite.FixedPointOfCompactDeflationIsCompact α → IsBifinite α` |
| 3 | `thm18_viaProjections_of_thm137_and_cor136` | same hypotheses `→ Recovered.IsBifiniteViaProjections α` |

`#print axioms` on all three: `[propext, Classical.choice, Quot.sound]`. No
`sorryAx`.

Row 2 is what the plan asked for and what `scripts/check-thm18-composition.sh`
elaborated in a scratch file. Row 1 is sharper and is the honest measurement of
what Theorem 18 spends: `JungNets.Thm137` concludes `IsBicomplete D` — infima of
all filtered subsets — but every consumer factors through
`JungNets.exists_minimal_upperBounds_le`, which is Zorn downwards and quantifies
over chains. So **proving `Thm137Chains` alone closes Theorem 18**; the full
Theorem 1.37 is more than the route needs. That is worth telling agents 2 and 3.

Row 3 exists because of the audit below: it states Theorem 18 with the paper's
own definition of bifinite, so the identification of the two readings is checked
by the kernel rather than asserted in a docstring.

## Part 2 — statement audit: `thm18` is the paper's sentence. No discrepancy.

Source: `ScottDomains/papers/Gunter Scott 1990.pdf`, §6.2, printed page 33 (the
page footer "Semantic Domains 33" follows it), text layer extracted with
`scripts/a5-paper-text.sh`:

> **Theorem 18** If `D` and `D → D` are domains, then `D` is bifinite.
>
> The theorem is due to Smyth and its proof may be found in [Smy83a]. It is
> carried out by analyzing each of the cases pictured in Figure 3 and showing
> that if `D → D` is not a domain, then `D` cannot be bifinite.

The Lean statement, `Skeleton/Section6.lean` (in a section with
`variable {α : Type*}` and `variable [CompletePartialOrder α]`):

```lean
theorem thm18 [Domain α] [Domain (ScottHom α α)] : IsBifinite α
```

Four things had to match. All four do.

| # | Paper | Lean | Verdict |
| -- | ----- | ---- | ------- |
| 1 | *cpo* — "every directed subset `M ⊆ D` has a least upper bound `⊔M` and there is a least element `⊥_D` in `D`" (p. 7) | `CompletePartialOrder α` (`lubOfDirected`, `bot`, `bot_le`) | exact |
| 2 | *domain* — "If `D` is algebraic and `K(D)` is countable, then we will say that `D` is a domain" (p. 8) | `class Domain extends IsAlgebraic` + `countable_compacts` (`Domain.lean:128`) | exact |
| 3 | `D → D` — the **non-strict** continuous function space, `f ⊑ g ↔ ∀x, f(x) ⊑ g(x)`, "with this ordering, the poset of continuous functions `D → E` is itself a cpo" (p. 7). The paper writes the *strict* space with a different arrow and warns about the notation explicitly | `ScottHom α α` with the pointwise `PartialOrder` and the `CompletePartialOrder` instance whose sups on directed sets are pointwise (`ScottHom.lean:239`); `ScottHom` carries no strictness field | exact — and the strict/non-strict trap is avoided |
| 4 | *bifinite* — "Let `M` be the set of finitary projections with finite image. Then `D` is said to be bifinite if `M` is countable, directed and `⊔M = id`" (p. 29) | `IsBifinite α := IsPlotkinOrder (compacts α)` (`Bifinite.lean:62`) | **not definitionally the paper's words** — see below |

Row 4 is the only place the two texts differ, and the difference is closed by a
proved theorem, not by convention. `IsBifinite` is the *second conjunct of clause
2* of the paper's Theorem 14:

> **Theorem 14** The following are equivalent for any cpo `D`.
> 1. `D` is bifinite.
> 2. `D` is a domain and `K(D)` is a Plotkin order.

and `Recovered.thm14 : IsBifiniteViaProjections α ↔ Domain α ∧ IsBifinite α` is
proved (r0036, `SFP.thm14_forward` / `SFP.thm14_converse`, axioms
`[propext, Classical.choice, Quot.sound]`). Theorem 18's own first hypothesis
supplies the `Domain α` conjunct, so under `thm18`'s hypotheses the two
conclusions are interderivable. `thm18_viaProjections_of_thm137_and_cor136` is
that derivation, kernel-checked.

**Verdict: no discrepancy. Five rounds have been spent on the right statement.**
Two further notes from the reading, neither a defect:

* The paper's own gloss of Smyth's proof is stated in the converse direction
  ("if `D → D` is not a domain, then `D` cannot be bifinite"), which is not what
  Theorem 18 asserts. `thm18`'s docstring already flagged this in an earlier
  round; the reading is confirmed against the PDF.
* Gunter & Scott's continuity is "`f` monotone and `f(⊔M) = ⊔f(M)` for every
  directed `M`"; Mathlib's `ScottContinuous`, which `ScottHom` bundles, requires
  the directed set to be **nonempty**. Over a cpo with `⊥` the empty case adds
  nothing (`f(⊥) ⊒ ⊥` always), and the development already records the choice in
  `ScottHom.lean`'s docstring. It does not touch Theorem 18.

I also updated `thm18`'s docstring, which had gone stale: it claimed "nothing
that argument quantifies over exists in this development … 0 occurrences" and
"proving `thm18` is therefore a separate development, not a proof script over
the present API". Minimal upper bounds, complete sets of them, and `U`/`U^∞` all
exist now (`MinimalUpperBounds.lean`), and the route taken is Jung's, not
Smyth's. The docstring now names the discharging declaration, per the `Skeleton/`
convention.

## Part 3 — the `sorry` could not be closed here, and the plan's closing edit was not possible

The two propositions are still open in this worktree (`JungNets.Thm137` and
`JungFinite.FixedPointOfCompactDeflationIsCompact` are `def`s appearing only as
explicit hypotheses), so the `sorry` stands. Expected: agents 1–4 work on their
own branches.

**But the plan's step — "replace the `sorry` at `Skeleton/Section6.lean:197` with
the composite" — was an import cycle and `lake` would have rejected it.**
Measured with `scripts/a5-import-cone.sh`, written for this:

```
JungFinite → Section62 → FinitaryProjectionEmbedding
           → Skeleton.Section6b → FinitaryProjectionPoset → Skeleton.Section6
```

`Skeleton.Section6` was one of the **22 modules in `ScottDomains.JungFinite`'s
import cone**. `FinitaryProjectionPoset.lean` imported the skeleton for one
reason: `IsClosure` and its API were declared there. So `Skeleton/Section6.lean`
could not import the module that proves its own Theorem 18. This would have
surfaced at merge, with four branches in flight — the worst moment to discover
it — so stream 5 removed it.

**The fix, and it changes no proof text.** `ScottDomains/Closure.lean` now owns
the eight closure declarations (`IsClosure`, `.idem`, `.le_apply`,
`.apply_of_mem_range`, `.isLUB_range`, `.rangeCompletePartialOrder`,
`.apply_sSup_of_directed`, `isClosure_sSup`) — same names, same `ScottDomains`
namespace, proofs copied verbatim. Three modules pick up imports they previously
had transitively:

| # | Module | Change |
| -- | ------ | ------ |
| 1 | `FinitaryProjectionPoset.lean` | `Skeleton.Section6` → `Closure` + `Bifinite` |
| 2 | `UniversalDomain.lean` | `Skeleton.Section6` → `Closure` |
| 3 | `Audit/Projections.lean` | added `Skeleton.Section6` (it cites `exists_upperBound_mem_of_finite`, which stays there as Proposition 15's helper) |

After the move `JungFinite`'s cone is 20 modules and excludes `Skeleton.Section6`;
`Thm18`'s cone is 36 and likewise excludes it. I then **added
`import ScottDomains.Thm18` to `Skeleton/Section6.lean` and built it** — 1300
jobs, exit 0 — to prove the closing import is acyclic in fact and not only by my
arithmetic, then reverted the import as unused.

The move also restores the `Skeleton/` convention the plan cites: the file now
holds Proposition 15, Theorem 18, Lemma 19 and Proposition 15's own proof
helpers, and owns no shared API.

**The closing edit at merge is therefore two lines**, and `thm18`'s docstring
states them:

```lean
import ScottDomains.Thm18                                  -- add
theorem thm18 [Domain α] [Domain (ScottHom α α)] : IsBifinite α :=
  Thm18.thm18_of_thm137_and_cor136 <Theorem 1.37> <Corollary 1.36>
```

with `Thm18.thm18_of_thm137Chains_and_cor136` in place of it if agents 2 and 3
land only the chain form, which is all the route spends.

## Measured build state

| # | Metric | Before (branch point) | After |
| -- | ------ | --------------------- | ----- |
| 1 | `lake` jobs | 1299 | 1300 |
| 2 | errors | 0 | 0 |
| 3 | non-`sorry` warnings | 0 | 0 |
| 4 | `sorry` | 1 (`Skeleton/Section6.lean`) | 1 (`Skeleton/Section6.lean:202`) |
| 5 | modules | 94 | 96 |
| 6 | lines | 34251 | 34460 |
| 7 | theorems | 1654 | 1657 |

Build log: `ScottDomains/logs/compile-20260808-141355.agent5.log`. Wall 2.02 s
incremental, peak 1655 MiB single / 2467 MiB tree rss.

Axioms re-checked after the move, all `[propext, Classical.choice, Quot.sound]`
or a subset, none with `sorryAx`: `prop15`, `lem19`, `Recovered.thm14`,
`IsClosure.apply_sSup_of_directed`, `isClosure_sSup`, and the three new assembly
theorems. `scripts/axioms.sh` was run with `Skeleton.Section6`, `UniversalDomain`
and `Thm18` imported into one environment, which is also a duplicate-declaration
check across the moved names; it elaborated clean.

## Commits on `agent5`

| # | Commit | Contents |
| -- | ------ | -------- |
| 1 | `a32751b` | `ScottDomains/Thm18.lean`, `scripts/a5-paper-text.sh` |
| 2 | `16f71e3` | `ScottDomains/Closure.lean`, the import move in four modules, `scripts/a5-import-cone.sh` |
| 3 | (this report) | report + `INDEX.md` rows for the two new modules |

Not pushed, per the agent rule.

## Two things for the orchestrator

1. **Merge this branch before or independently of 1–4.** It changes no proof and
   it is what makes their closings a two-line edit rather than a restructure
   under time pressure.
2. **Tell agents 2 and 3 that `Thm137Chains` suffices.** Infima of nonempty
   chains, not full bicompleteness. `JungNets.Thm137.toChains` is the only place
   the stronger form is ever used.
