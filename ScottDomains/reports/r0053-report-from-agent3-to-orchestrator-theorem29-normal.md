---
round: r0053
from: agent3
to: orchestrator
subject: theorem29-normal
date: 2026-0810-19:10
started: 2026-0810-18:45
finished: 2026-0810-19:10
related: plans/r0053-plan-from-orchestrator-to-agent3-theorem29-normal.md
---

# r0053 / agent3 — root hole 3, `Theorem29Normal`: the infinite case

`Lemma30.Theorem29Normal` is **still open**. `Lemma30.lean` is untouched; the
`sorry` count is unchanged at 3. What the round produced is one new module,
`ScottDomains/ScottDomains/Theorem29NormalInfinite.lean` (23 declarations, 0
`sorry`, no `sorryAx` in any of them), containing three measurements and one
proved infinite case.

## 1. Headline numbers

| # | measure | value |
| - | ------- | ----- |
| 1 | build | `scripts/compile.sh -r r0053`, 1373 jobs, **0 errors, 0 warnings other than `sorry`** |
| 2 | `sorry` before / after | 3 / 3 (`Lemma30.lean:535`, `Effective/A3StepDecidable.lean:200,386`) |
| 3 | new declarations | 23, all kernel-checked; axiom footprint is `{propext, Classical.choice, Quot.sound}` or empty, **no `sorryAx`** |
| 4 | tracked files changed | 1 (`INDEX.md`, one line). `Lemma30.lean` is byte-identical to `main` |
| 5 | new `Prop`-valued `def`s | 0 (the three new `def`s are `mkEmpty : α → Step α`, `bpt : (n : ℕ) → Stg n`, `maxPt : ℕ → Ainf`) |
| 6 | build log | `ScottDomains/logs/compile-20260810-190604.agent3.log` |

## 2. Plan steps 1 and 3: already proved, reused, not rebuilt

The plan asked for a tower, a step, and a limit. **Steps 1 and 3 were already in
the development**, in `A2Thm29Universal.lean` (r0046/agent2), and I built neither
a second tower nor a second limit.

| # | plan step | existing declaration | status |
| - | --------- | -------------------- | ------ |
| 1 | `K(E)` as a countable increasing union of finite normal subposets | `R46.Agent2.cover` / `coverStep`, with `cover_mono`, `cover_subset_succ`, `cover_isNormalIn_succ`, `exists_mem_cover`, `bot_mem_cover`, `cover_nonempty` | proved |
| 2 | the coherent extension step | `R46.Agent2.exists_extend`, hypothesis `HasFiniteExtensions Ainf` | **the entire gap** |
| 3 | the limit: coherence, pointwise order-reflection, normality of the union image | `R46.Agent2.limitMap`, `limitMap_eq`, `stage_stable`, `stageImage_subset`, assembled in `theorem_29_normal_of_hasFiniteExtensions` | proved |

The lemma the plan asked me to isolate — "normality of a directed union of normal
subsets" — exists as `NormalSubposet.isNormalIn_sUnion` and is applied at
`A2Thm29Universal.lean:762`; the family's `◁`-directedness comes from
`stageImage_subset`. Nothing further is needed there. The tower runs on
`IsPlotkinOrder (univ : Set ↥(compacts E))` (from `IsBifinite E`) and a surjection
`ℕ → ↥(compacts E)` (from `[Domain E]`), exactly the two halves of "bifinite
domain".

**Consequence for future rounds: `Theorem29Normal`'s residue is a single property
of `A∞`, not a construction over `K(E)`.**

## 3. New result A — the two named sufficient conditions are one, and it is false

`R46.Agent2` states `HasNormalRealizations` and `HasFiniteExtensions` and proves
`HasNormalRealizations α → HasFiniteExtensions α` (Gunter's Proposition 21).
r0047 refuted `HasNormalRealizations A∞`. That left the property actually
consumed by the reduction, `HasFiniteExtensions A∞`, formally open — and it is
step 2 above.

Proved this round:

```lean
theorem hasNormalRealizations_of_hasFiniteExtensions {α : Type} [PartialOrder α]
    (H : R46.Agent2.HasFiniteExtensions α) : R46.Agent2.HasNormalRealizations α

theorem hasFiniteExtensions_iff_hasNormalRealizations {α : Type} [PartialOrder α] :
    R46.Agent2.HasFiniteExtensions α ↔ R46.Agent2.HasNormalRealizations α

theorem not_hasFiniteExtensions_Ainf : ¬ R46.Agent2.HasFiniteExtensions Ainf
```

The new direction is cheap once seen: a normal type over `A` presented by
`(β, T, g, z)` already *is* a finite normal extension — take `T' := insert z (g '' A)`,
which is finite, nonempty, and satisfies `g '' A ◁ T'` by Lemma 4.2
(`IsNormalIn.mono_right`) — and the map `h : β → α` that `HasFiniteExtensions`
returns realizes the type at `h z`, with `h '' T' = insert (h z) A` normal by the
same call.

Axiom footprint: `{propext, Classical.choice, Quot.sound}`.

**Both named routes to `Theorem29Normal` are now closed.** A future round should
not attempt `HasFiniteExtensions A∞`.

## 4. New result B — the obstruction recurs at every stage

r0047 refutes the realization property from one point, `β = incl 1 pointB1`,
maximal in `A∞`. Read narrowly that is a defect of stage 1 and invites the repair
"start the construction later". **That repair does not exist.**

| # | statement | Lean name |
| - | --------- | --------- |
| 1 | `(x, ∅)` is maximal in `M(A)` for *every* base `x` (r0047 had `x = ⊥`) | `mkEmpty_maximal` |
| 2 | distinct bases give distinct empty-cover points | `mkEmpty_injective` |
| 3 | an empty-cover point is never `⊥` | `mkEmpty_ne_bot` |
| 4 | the tower's connecting map carries an empty cover to an empty cover | `stgEmb_mkEmpty`, `liftStg_mkEmpty` |
| 5 | hence `incl (n+1) (mkEmpty x)` is maximal in `A∞`, for every `n` and every `x : Stg n` | `incl_mkEmpty_maximal` |
| 6 | iterating from `⊥` gives an injective `maxPt : ℕ → Ainf` of maximal points | `maxPt_maximal`, `maxPt_injective`, `maxPt_le_iff` |
| 7 | **`{q : Ainf | q ≠ ⊥ ∧ ∀ w, q ≤ w → w = q}` is infinite** | `infinite_maximal_Ainf` |
| 8 | `{⊥, a} ◁ A∞` for any maximal `a`, so each of those points on its own refutes the realization property | `pair_bot_isNormalIn_of_maximal` |

Row 8 also simplifies `R47.Agent1.not_hasNormalRealizations_of_maximal`: its
second hypothesis `{⊥, a} ◁ univ` is a consequence of its third, so "a non-`⊥`
maximal point" alone kills the property.

Row 4 is the precise reason this tower behaves differently from §7.4's printed
`η`-tower: `η` destroys the maximality of `(⊥, ∅)` at the very next stage
(`R47.Agent1.exists_gt_mk_eta_pointB1`), whereas `M(f)` preserves an empty cover
forever. `Colimit.stgEmb_ne_mk_eta` is the same datum at one point.

## 5. New result C — the first *infinite* case of `Theorem29Normal`, proved

The same infinitude of maximal points that blocks the extension route is exactly
the room a flat basis needs. Distinct maximal points have no common upper bound,
so directedness is never a constraint:

```lean
theorem isNormalIn_of_bot_or_maximal {α : Type*} [PartialOrder α] [OrderBot α]
    {N : Set α} (hbot : (⊥ : α) ∈ N)
    (hmax : ∀ a ∈ N, a = ⊥ ∨ ∀ w : α, a ≤ w → w = a) :
    N ◁ (Set.univ : Set α)

theorem theorem_29_normal_flatBasis :
    ∀ (E : Type) [CompletePartialOrder E] [Domain E],
      (∀ a b : ↥(compacts E), a ≤ b → a = ⊥ ∨ a = b) → IsBifinite E →
      ∃ f : ↥(compacts E) → Ainf,
        (∀ a b, f a ≤ f b ↔ a ≤ b) ∧ Set.range f ◁ (Set.univ : Set Ainf)
```

The map is `⊥ ↦ ⊥` and, off `⊥`, an injection into `maxPt` supplied by
`[Domain E]`'s countability of `K(E)`. Order reflection matches the flat order on
the nose because two distinct maximal points of `A∞` are incomparable
(`maxPt_le_iff`). `exists_normal_antichain_Ainf` records the closed instance: a
normal copy of the countably infinite flat poset inside `A∞`.

This is `Theorem29Normal`'s conclusion for every bifinite domain with a flat
basis — the countable flat domains — and it is **the first case with an infinite
basis discharged in this development**; `R49.Agent5.theorem_29_normal_finiteBasis`
needs `Finite ↥(compacts E)`.

Honest accounting, as for the finite case: this is a *discharged-at*, not a
discharge. `theorem_29_normal_flatBasis_of_thm29Normal` checks the direction —
`Theorem29Normal` implies it, so the added hypothesis only weakens. `IsBifinite E`
is carried to line the statement up with `Theorem29Normal` and is not used.

## 6. The remaining goal, stated exactly

Open: `Theorem29Normal` for a basis that is neither finite nor flat. The smallest
open instance is a basis containing an infinite ascending chain, and for a basis
that is a *chain* the normality conjunct is free:

```lean
theorem isNormalIn_of_isChain {N : Set α} (hbot : (⊥ : α) ∈ N)
    (hchain : ∀ a ∈ N, ∀ b ∈ N, a ≤ b ∨ b ≤ a) : N ◁ (Set.univ : Set α)

theorem theorem_29_normal_of_chainBasis {E : Type} [CompletePartialOrder E]
    (hchain : ∀ a b : ↥(compacts E), a ≤ b ∨ b ≤ a) (f : ↥(compacts E) → Ainf)
    (hf : ∀ a b, f a ≤ f b ↔ a ≤ b) (hbot : f ⊥ = (⊥ : Ainf)) :
    (∀ a b, f a ≤ f b ↔ a ≤ b) ∧ Set.range f ◁ (Set.univ : Set Ainf)
```

So the `ω`-chain instance reduces to one purely order-theoretic question about
`A∞`, with no normality left in it:

> **Does `A∞` contain a strictly increasing sequence `⊥ = c₀ ⊏ c₁ ⊏ c₂ ⊏ ⋯`?**

Nothing in this development answers it, and it is decisive both ways:

* **Yes** ⟹ the `ω`-chain case of `Theorem29Normal` closes immediately by
  `theorem_29_normal_of_chainBasis`.
* **No** ⟹ `Theorem29Normal` is **refuted** at this `A∞`, because an
  order-reflecting map of an `ω`-chain basis into `A∞` is exactly such a
  sequence, and the ideal completion of an `ω`-chain is a bifinite domain with a
  countable basis.

What is known, and why the question is not obviously "yes": `A∞` contains a copy
of every stage (`incl n` is an order embedding), and the stages' heights grow —
by hand, `Stg 0 … Stg 3` have longest chains of 1, 2, 4 and 6 elements — so `A∞`
has chains of every finite length. An *infinite* chain needs more: a family of
chains `C_N ⊆ Stg N` with `stgEmb '' C_N ⊆ C_{N+1}` and `|C_N| → ∞`, and
unbounded finite chains do not supply that in a countable poset with infinite
branching. The greedy family fails: `stgEmb_mkEmpty` says the top of a chain that
reaches an empty-cover point is maximal from that stage on, and it stays maximal
in the colimit.

## 7. What I did not attempt, and why

* No route through `HasNormalRealizations` or `HasFiniteExtensions` — §3 closes
  both.
* No weakening of the `def`: `[Domain E]` is untouched (dropping it is refutable,
  `R45.Agent3.not_thm29NormalWithoutDomain`), `◁` is untouched, and
  order-reflection was not replaced by monotone-plus-injective. Both new
  `Theorem29Normal`-shaped theorems carry an *added* hypothesis and each has a
  companion `…_of_thm29Normal` proving the added hypothesis only weakens.
* No `axiom`, and no new `Prop`-valued `def` that restates the goal. The one
  hypothesis-shaped statement in the file (`theorem_29_normal_of_chainBasis`) is
  a theorem with explicit binders, following the precedent set by
  `R46.Agent2.hasNormalRealizations_of_stages`.

## 8. Files

| # | path | change |
| - | ---- | ------ |
| 1 | `ScottDomains/ScottDomains/Theorem29NormalInfinite.lean` | new, 23 declarations |
| 2 | `INDEX.md` | one line added next to `Colimit.lean` |
| 3 | `ScottDomains/logs/compile-20260810-19{0336,0533,0604}.agent3.log` | build logs (the last is the passing run) |

Committed on branch `agent3` with `scripts/gitcp.sh`; not pushed, per the
agents-commit / orchestrator-pushes rule.
