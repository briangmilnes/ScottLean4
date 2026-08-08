---
round: r0041
from: agent5
to: orchestrator
subject: kleene
date: 2026-0808-13:24
started: 2026-0808-13:02
finished: 2026-0808-13:24
related:
  - plans/r0041-plan-from-orchestrator-to-orchestrator-close-unstated.md
  - reports/r0040-report-from-agent1-to-orchestrator-property-coverage-s2-s3.md
---

# r0041, stream 5 — §2's calculus, and the missing half of Theorem 3

Namespace `ScottDomains.Kleene`, six new modules under
`ScottDomains/ScottDomains/Kleene/`. Every statement below was read off a 200 dpi
render of the physical page, not off `pdftotext`: physical pages 5–8 (printed
4–7) for §2.1–§2.3 and physical page 10 (printed 9) for `G_f`.

## 1. Headline

**Theorem 3 now has its existence half.** `UniformFixedPoint.theorem3` proved
that *every* uniform fixed point operator is `fix`; nothing proved that one
exists, and the module docstring at line 168 said so explicitly rather than
asserting the claim. `Kleene.kleeneOperator_isUniform` supplies existence, and
`Kleene.theorem3_existsUnique : ∃! F : FixedPointOperator.{u}, F.IsUniform` is
the paper's sentence — *`fix` is **the** unique uniform fixed point operator* —
in one kernel-checked statement.

**Six of six targeted rows are stated and proved.** Two further rows were taken
after they landed: the `G_f` countability row, and an upgrade of a row r0040
labelled `S≠`.

## 2. Row by row, with r0040's numbering

| # | r0040 row | Paper's sentence | § / p. | Before | After | Declaration |
| -- | --------- | ---------------- | ------ | ------ | ----- | ----------- |
| 1 | 41 (N13) | "the function `fix_D : (D → D) → D` given by `fix_D(f) = ⨆ₙ fⁿ(⊥)` is actually continuous" | 2.3 / 7 | `N` | **`S+P`** | `Kleene.scottContinuous_kleeneFix`, `Kleene.monotone_kleeneFix`, bundled as `Kleene.fixHom` (`Kleene/FixContinuous.lean:110, 66, 126`) |
| 2 | 42 (N14) | "We leave it to the reader to show that `fix` is a uniform fixed point operator" | 2.3 / 7 | `N` | **`S+P`** | `Kleene.kleeneOperator_isUniform` (`Kleene/Uniform.lean:103`); Theorem 3 in full as `Kleene.theorem3_existsUnique` (line 126) |
| 3 | 39 (N11) | factorial: "`F` is continuous (but not strict)", and "`F` has a least fixed point `fix(F)` and this solution will satisfy the equation for `fact`" | 2.2 / 5 | `N` | **`S+P`** | `Kleene.scottContinuous_factFun`, `Kleene.factFun_ne_bot`, `Kleene.isLeast_kleeneFix_factFun`, `Kleene.kleeneFix_factFun_eq` (`Kleene/Factorial.lean`) |
| 4 | 40 (N12) | grammars: the three operators "are all continuous in the variable `X`", the equations "all have least solutions", "These solutions are the languages defined by the grammars" | 2.2 / 6 | `N` | **`S+P`** | `Kleene.scottContinuous_gram1/2/3`, `Kleene.isLeast_gram1/2/3`, `Kleene.kleeneFix_gram1/2/3` (`Kleene/Grammar.lean`) |
| 5 | 36 (N9) | "The function `f*` is monotone" | 2.1 / 4 | `N` | **`S+P`** | `Kleene.monotone_extension` (`Kleene/Extension.lean:82`) |
| 6 | 37 (N9) | "`f*(⋃ᵢ Xᵢ) = ⋃ᵢ f*(Xᵢ)`. In particular, `f*` is continuous" | 2.1 / 4–5 | `N` | **`S+P`** | `Kleene.extension_iUnion`, `Kleene.scottContinuous_extension`, bundled as `Kleene.extensionHom` (`Kleene/Extension.lean:86, 103, 108`) |
| 7 | 46 (N16) | "This allows us to characterize … a continuous function `f : P N → P N` between uncountable cpo's with a countable set `G_f`" | 3 / 9 | `N` | **`S+P`** | `Kleene.countable_graphPairs`, `Kleene.not_countable_powersetNat`, `Kleene.characterization_powersetNat` (`Kleene/Graph.lean`) |
| 8 | 45 | "one may recover from `G_f` the value of `f` on `x` as `f(x) = ⨆{y₀ \| (x₀,y₀) ∈ G_f and x₀ ⊑ x}`" | 3 / 9 | **`S≠`** | **`S+P`** | `Kleene.graphPairs`, `Kleene.sSup_recoverAt` (`Kleene/Graph.lean:53, 94`) |
| 9 | 34 (part of N7) | "any monotone function `f : N⊥ → E` is continuous" | 2.1 / 4 | `N` | **`S+P`** | `Kleene.NatBot.scottContinuous_of_monotone` (`Kleene/Factorial.lean:152`) — **stream 1's row**, taken only because the factorial example cannot be stated without `N⊥` |

Rows 1–6 are the six the plan assigned. Rows 7–9 are extra.

**Row 8 is an `S≠` I changed, as the plan asks me to declare.** r0040 found
`ContinuousConstruction.coe_eq_basisExtension_self` stating the recovery formula
over `graphOn v = {(k, v k) | k ∈ K(D)}`, which restricts only the first
coordinate to compacts and pins the second to the exact value. `Kleene.graphPairs`
is the paper's `G_f` verbatim — both coordinates compact, downward closed in the
second — and `Kleene.sSup_recoverAt` is the recovery equation for *it*. The
distinction is load-bearing: row 7's countability follows only from the paper's
version, because only that one has both coordinates in a countable set. I did not
touch `ContinuousConstruction.lean`; the `S≠` row now has an `S+P` companion
rather than a replacement.

I did **not** touch the other `S≠`, "the strict step functions form a basis"
(`PRepFun.strictHomIsAlgebraic`).

## 3. Where the paper contradicted expectation

1. **The plan says "`kleeneFix` is never bundled as a `ScottHom`, so neither its
   continuity nor its uniformity in `f` is stated — two rows."** The paper makes
   these two *separate* claims one paragraph apart, and only the first is about
   varying `f`: §2.3's "`fix_D` … is actually continuous" (row 41) and "`fix` is
   a uniform fixed point operator" (row 42). Uniformity is not a property of
   `fix` as a function of `f` at all — it is a naturality condition relating
   `fix_D` and `fix_E` along a strict `h : D ⊸ E`. The two are proved
   independently here and neither uses the other.

2. **`FixedPointOperator` omits a hypothesis the paper's definition carries.**
   The printed definition asks a fixed point operator to be a class of
   *continuous* functions `F_D : (D → D) → D`. `UniformFixedPoint.lean` drops
   continuity deliberately, because `theorem3` does not use it and dropping it
   strengthens uniqueness. But that means the *existence* witness must be checked
   against the paper's definition, not the weakened one:
   `Kleene.scottContinuous_kleeneOperator_op` records that `kleeneOperator`
   satisfies it, and its proof is row 41. Without row 41, row 42 would have
   established that `fix` is uniform without establishing that `fix` is a fixed
   point operator *in the paper's sense*.

3. **The recovery equation needs a hypothesis the paper does not state.** The
   paper writes `f(x) = ⨆{y₀ | …}` with no side condition, but in a cpo `sSup` is
   pinned down only on directed sets, and the recovering set is directed only
   because two of its members are bounded by `f(x₃)` for a common compact
   `x₃ ⊑ x`, so their join exists and is compact by
   `isCompactElement_of_isLUB_pair`. `sSup_recoverAt` therefore assumes
   `[BoundedComplete β]`. `P N` is bounded complete, so the paper's own example is
   covered. `directedOn_recoverAt` uses algebraicity of `D` and bounded
   completeness of `E` but **not** algebraicity of `E`, which the `omit` clause
   records.

## 4. `N⊥` is built here, and should be replaced at merge

§2.2's factorial example cannot be stated without the flat naturals, and stream 1
owns the general flat cpo. Per the plan's instruction not to wait on stream 1,
`Kleene/Factorial.lean` defines `NatBot` — the two-constructor inductive with
`x ⊑ y ↔ x = ⊥ ∨ x = y` — with its `PartialOrder`, `SupSet` and
`CompletePartialOrder` instances, and claims nothing about flat cpos in general.

**Merge instruction:** when `ScottDomains.Flat` lands, `NatBot` should become its
instance at `ℕ`. Nothing below the instances touches the representation except
through `NatBot.le_iff` and the two constructors, so the replacement is
mechanical. The one general fact the construction buys is
`NatBot.mem_of_isLUB` — a nonempty directed set in a flat cpo **contains** its
own least upper bound — from which row 9 follows in three lines. If stream 1
proved the same fact, the two are in different namespaces and do not clash; the
composition check in §6 confirms it for the six modules of this stream.

## 5. What each module contains

| # | Module | Lines | What it proves |
| -- | ------ | ----: | -------------- |
| 1 | `Kleene/FixContinuous.lean` | 136 | `fix` monotone and Scott continuous in `f`; `fixHom : ScottHom (ScottHom α α) α` |
| 2 | `Kleene/Uniform.lean` | 129 | `h(fⁿ⊥) = gⁿ⊥`, `h '' kleeneChain f = kleeneChain g`, `kleeneOperator.IsUniform`, `theorem3_existsUnique` |
| 3 | `Kleene/Extension.lean` | 113 | `scottContinuous_set_iff` (Scott continuity on powersets, reused by module 5); `f*` monotone, union-preserving, continuous |
| 4 | `Kleene/Factorial.lean` | 322 | `NatBot` as a cpo; monotone ⟹ continuous out of it; `F` continuous but not strict; `fix(F) = fact` and `fix(F)(n) = n!` |
| 5 | `Kleene/Grammar.lean` | 269 | concatenation; three continuity combinators; the three grammars, their least solutions, and the three language identifications |
| 6 | `Kleene/Graph.lean` | 149 | the paper's `G_f`; directedness of the recovering set; the recovery equation; `G_f` countable and `P N` uncountable |

The six sum to 1118, which is the measured line delta in §6 exactly.

Two proofs are worth reading for their shape:

* **`scottContinuous_kleeneFix`.** The `⨆S ⊑ fix(F)` direction is monotonicity.
  The content is the converse, and it turns on one lemma:
  `apply_sSup_kleeneFix_image_le`, that `⨆{fix(g) | g ∈ M}` is a *pre-fixed point
  of every `f ∈ M`*. Directedness of `M` is spent exactly once there, to find a
  `k ∈ M` above both `f` and `g` so that `f(fix g) ⊑ k(fix k) = fix k`.

* **`scottContinuous_concat_diag`.** Of the three grammar operators, only
  `X ↦ X X` needs directedness: the two factors of a concatenation come from
  possibly different members of the family, and a single member above both is
  what puts the concatenation back in the image. This is a clean demonstration of
  why the Fixed Point Theorem is stated for directed families and not for chains
  or arbitrary families.

## 6. Measured build, before and after

Baseline, `scripts/compile.sh -r r0041` and `scripts/counts.sh` at
2026-0808-13:05, before any file was written:

| # | Measurement | Before | After | Δ |
| -- | ----------- | -----: | ----: | -: |
| 1 | modules | 78 | **84** | +6 |
| 2 | lines | 28617 | **29735** | +1118 |
| 3 | theorems | 1326 | **1398** | +72 |
| 4 | `sorry` | 1 | **1** | 0 |
| 5 | lake jobs | 1229 | **1235** | +6 |
| 6 | lake errors | 0 | **0** | 0 |
| 7 | non-`sorry` warnings | 0 | **0** | 0 |

The one `sorry` is `Skeleton/Section6.lean:197` (`thm18`), unchanged. No existing
`.lean` file was opened read-write; the only edit outside `Kleene/` is the
`INDEX.md` entry.

**Axiom audit**, `scripts/axioms.sh` with all six new modules imported together —
which is also the composition check for duplicate names:

    theorem3_existsUnique          propext, Classical.choice, Quot.sound
    kleeneOperator_isUniform       propext, Classical.choice, Quot.sound
    scottContinuous_kleeneFix      propext, Classical.choice, Quot.sound
    scottContinuous_extension      propext, Classical.choice, Quot.sound
    kleeneFix_gram1/2/3            propext, Classical.choice, Quot.sound
    kleeneFix_factFun_eq           propext, Classical.choice, Quot.sound
    scottContinuous_factFun        propext, Classical.choice, Quot.sound
    factFun_ne_bot                 propext, Classical.choice, Quot.sound
    sSup_recoverAt                 propext, Quot.sound
    characterization_powersetNat   propext, Classical.choice, Quot.sound

No `sorryAx` anywhere. `sSup_recoverAt` does not even use `Classical.choice`.

## 7. Commits on branch `agent5`

| # | Commit | Contents |
| -- | ------ | -------- |
| 1 | `2755e0b` | `Kleene/FixContinuous.lean`, `Kleene/Uniform.lean` — rows 41 and 42 |
| 2 | `3d845a7` | `Kleene/Extension.lean`, `Kleene/Grammar.lean` — rows 36, 37, 40 |
| 3 | `29566e1` | `Kleene/Factorial.lean` — rows 39 and 9 |
| 4 | this report | `Kleene/Graph.lean` — rows 46 and 45 — plus `INDEX.md` and this file |

Not pushed, per the agent rule.
