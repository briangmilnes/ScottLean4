---
round: r0028
from: agent4
to: orchestrator
subject: minimal-upper-bounds
date: 2026-0806-21:30
started: 2026-0806-18:50
finished: 2026-0806-21:30
related:
  - plans/r0028-plan-from-orchestrator-to-orchestrator-five-fold-parallel.md
---

# r0028 agent4 — `MinimalUpperBounds.lean`; Theorem 18 not proved

## Measurement

| # | Quantity | Value |
| -- | -------- | ----- |
| 1 | Final build | `Build completed successfully (963 jobs).` |
| 2 | Errors | 0 |
| 3 | Warnings | 1, the declared `sorry` at `Skeleton/Section6.lean:196` (`thm18`) |
| 4 | New module | `ScottDomains/MinimalUpperBounds.lean`, 455 lines, 36 declarations (8 definitions, 28 theorems) |
| 5 | `sorry` in the development | 1, unchanged — `thm18` |
| 6 | Files edited outside the new module | 0. `Skeleton/Section6.lean` is untouched |
| 7 | Axioms | every new theorem: `[propext, Classical.choice, Quot.sound]`; no `sorryAx` |
| 8 | Commits (branch `agent4`) | `df8040a`, `bc82513` |

## What was proved

The §6.1 vocabulary the r0027 audit measured at 0 occurrences, plus **Plotkin's
criterion as an equivalence**. The paper states the criterion only as three
*necessary* conditions ("the first/second/third fact about Plotkin orders"); the
converse is proved here, which is what turns it into a usable characterization.

Definitions, relativized to a subset `A` of the ambient order because `◁` and
`IsPlotkinOrder` are conditions on the basis `K(D)`, not on `D`:

    def upperBoundsIn (A u : Set α) : Set α := A ∩ upperBounds u
    def minimalUpperBounds (A u : Set α) : Set α := {m | Minimal (· ∈ upperBoundsIn A u) m}
    def HasCompleteMub (A u : Set α) : Prop :=
      ∀ x ∈ upperBoundsIn A u, ∃ m ∈ minimalUpperBounds A u, m ≤ x
    def IsMubClosed (A N : Set α) : Prop :=
      ∀ v : Set α, v ⊆ N → v.Finite → minimalUpperBounds A v ⊆ N
    def mubStep (A N : Set α) : Set α :=            -- the paper's `U`
      N ∪ {m | ∃ v : Set α, v ⊆ N ∧ v.Finite ∧ m ∈ minimalUpperBounds A v}
    def mubIter (A u : Set α) : ℕ → Set α           -- `Uⁿ`
      | 0 => u
      | n + 1 => mubStep A (mubIter A u n)
    def mubClosure (A u : Set α) : Set α := ⋃ n, mubIter A u n   -- `U^∞`

`mubStep_eq_of_subset` proves that the adjoined `N` is redundant when `N ⊆ A`, so
`mubStep` is the paper's `U(u) = {x | x is the minimal upper bound for some v ⊆ u}`
on the nose. The `N ∪ …` form is kept so that monotonicity of the iteration needs
no hypothesis.

The headline results:

    theorem isPlotkinOrder_iff_mubClosure (A : Set α) :
        IsPlotkinOrder A ↔
          (∀ v : Set α, v.Finite → v ⊆ A → HasCompleteMub A v) ∧
            (∀ u : Set α, u.Finite → u ⊆ A → (mubClosure A u).Finite)

    theorem isBifinite_iff_mubClosure [CompletePartialOrder α] :
        IsBifinite α ↔
          (∀ v : Set α, v.Finite → v ⊆ compacts α → HasCompleteMub (compacts α) v) ∧
            (∀ u : Set α, u.Finite → u ⊆ compacts α →
              (mubClosure (compacts α) u).Finite)

    theorem exists_of_not_isPlotkinOrder {A : Set α} (h : ¬ IsPlotkinOrder A) :
        (∃ v : Set α, v.Finite ∧ v ⊆ A ∧ ¬ HasCompleteMub A v) ∨
          (∃ u : Set α, u.Finite ∧ u ⊆ A ∧ (mubClosure A u).Infinite)

`exists_of_not_isPlotkinOrder` **is** the Figure 3 case split, stated as a
theorem rather than left as prose: 3a is the left disjunct; 3b and 3c are the
right one, 3b being the sub-case where a single application of `U` is already
infinite.

Supporting results, each kernel-accepted:

* `IsNormalIn.exists_mem_le_of_finite` — the step the paper writes as "(why?)".
  For `u ⊆ N ◁ A` finite and `x` an upper bound of `u` in `A`, directedness of
  `N ∩ ↓x` collapses the finitely many members of `u` to a single `z ∈ N` with
  `u ⊑ z ⊑ x`. So `N ∩ ub(u)` is a complete set of upper bounds inside `N`.
* `minimalUpperBounds_subset_of_isNormalIn`, `minimalUpperBounds_finite_of_isNormalIn`,
  `hasCompleteMub_of_isNormalIn`, `mubClosure_subset_of_isNormalIn` — the paper's
  three facts. The one real argument is in `hasCompleteMub_of_isNormalIn`:
  minimality inside the *finite complete* set `S = {y ∈ N | y ∈ ub(u), y ⊑ x}`
  upgrades to minimality in the whole of `upperBoundsIn A u`, because any upper
  bound `y ⊑ m` puts some `z ∈ S` below `y` and minimality in `S` then gives
  `m ⊑ z ⊑ y`.
* `isNormalIn_of_isMubClosed` — the converse the paper does not state. A
  mub-closed, mub-complete `N ⊆ A` is normal in `A`. Nonemptiness of `N ∩ ↓x`
  comes from completeness at `v = ∅`, since `upperBoundsIn A ∅ = A`; directedness
  from completeness at `v = {a, b}`. Note that `⊥ ∈ N` is *derived*, not assumed:
  the theorem holds in a preorder with no least element.
* `isMubClosed_mubClosure`, `exists_mubIter_of_finite_subset`,
  `mubClosure_subset` — `U^∞(u)` is mub-closed and stays inside `A`.

## Theorem 18 — not proved, and where it stops

`thm18` still reads `sorry`; `Skeleton/Section6.lean` was not edited at all.

What the new module buys is a genuine reduction: by `isBifinite_iff_mubClosure`,
Theorem 18 is now exactly the two obligations

1. every finite `v ⊆ K(D)` has a complete set of minimal upper bounds in `K(D)`;
2. every finite `u ⊆ K(D)` has `mubClosure (compacts α) u` finite,

to be discharged from `[Domain α] [Domain (ScottHom α α)]`. **Neither obligation
was discharged. None of Smyth's three cases is complete.**

### The obstacle, stated precisely

Smyth's argument is by contraposition: for each Figure 3 configuration in `K(D)`,
exhibit a continuous `h : D → D` witnessing that `D → D` is not algebraic. Two
things were established while attempting it, and one thing blocks it.

Established, by hand rather than in Lean:

* The witness must contradict **directedness** of `compactsBelow h`, not the
  least-upper-bound conjunct. Worked example: `D = {⊥, a, b} ∪ {xᵢ}` with
  `x₀ > x₁ > …` the upper bounds of `{a, b}`, so `{a, b}` has no minimal upper
  bound. Every candidate built from `ubStep`-style or step-function-style `h`
  *does* have `⨆ compactsBelow h = h`; what fails is that `step a a` and
  `step b b`, both compact and both `⊑ id`, have no compact upper bound `⊑ id` —
  such a `g` would need `g a = a` and `g b = b`, and then an explicit increasing
  chain `qₙ` with `⨆ qₙ = g` and `g ⋢ qₙ` shows `g` is not compact.
* The entry point generalizes: from `IsAlgebraic (ScottHom α α)` and
  `exists_mem_upperBounds_of_directedOn`, any finite `u ⊆ K(D)` yields a compact
  `g ⊑ id` with `g k = k` for every `k ∈ u`.

What blocks it: **the perturbing family `qₙ` has no general construction in this
development.** In the worked example it is written down from the linear order of
the descending chain. In an arbitrary domain it must be built inside `D → D`, and
the only continuous functions constructible here are step functions and *directed*
suprema of them. The natural formulas — "`g` truncated below the `n`-th upper
bound", `qₙ z = ⨆ {g w | w ∈ K(D), w ⊑ z, w ∉ ↓sₙ}` — all take a least upper
bound of a bounded, not directed, set, which is exactly what a non-bounded-complete
`D` need not have. `CompactFunction.lean`'s decomposition of a compact function
into a finite join of step functions is unavailable for the same reason: it
carries `[BoundedComplete β]`, and Theorem 18's whole point is the case where that
hypothesis is absent.

So the missing tool is prior to the case analysis: a way to construct continuous
functions on a domain that is not bounded complete. Case (c) additionally needs
König's lemma against `Domain.countable_compacts`, but that was never reached —
case (a) blocks first.

### Recommendation

Theorem 18 should not be re-attempted as a proof script over the present API. It
needs its own round with a stated prerequisite: a constructor for continuous
functions on a general domain — plausibly "the least continuous function above a
given monotone partial assignment on `K(D)`, where it exists" — with the exact
conditions for existence proved first. Absent that, the honest state is the one
now recorded: Theorem 18 reduced to the two obligations above, with the reduction
formally verified.

## Housekeeping

`INDEX.md` at the repo root lists modules only through `Projection.lean`; it is
already missing twelve modules from earlier rounds, and `MinimalUpperBounds.lean`
is the thirteenth. It was left alone deliberately — five agents editing one root
file in the same round is a conflict for no gain. The orchestrator may want to
refresh it once in a single edit after the merges.
