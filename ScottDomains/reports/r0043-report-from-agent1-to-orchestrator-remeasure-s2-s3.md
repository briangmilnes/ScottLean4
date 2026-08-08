---
round: r0043
from: agent1
to: orchestrator
subject: remeasure-s2-s3
date: 2026-0808-16:37
started: 2026-0808-16:30
finished: 2026-0808-16:37
related:
  - plans/r0043-plan-from-orchestrator-to-orchestrator-remeasure-unstated.md
  - reports/r0040-report-from-agent1-to-orchestrator-property-coverage-s2-s3.md
---

# r0043, §2 and §3 — re-measuring the 24 rows r0040 labelled `N`

Scope: exactly the 24 properties of §2 (printed pp. 3–8) and §3 (pp. 8–12) of
Gunter & Scott, *Semantic Domains*, that r0040 recorded as having no Lean
statement. The other 36 rows of r0040's 60-row table are out of scope; §5 reports
the one out-of-scope movement noticed and the regression check.

Direction: **r0040's rows → the tree as it stands after r0041 and r0042**. No
row was re-derived from the paper; the paper's sentence and printed page are
r0040's.

## 1. Headline

| # | Measurement | Value |
| -- | ----------- | ----- |
| 1 | rows re-checked (r0040's `N` rows for §2/§3) | **24** |
| 2 | now `S+P` — stated and proved, declaration named and read | **13** |
| 3 | now `S+H` — stated, proof open | **1** |
| 4 | now `S≠` | 0 |
| 5 | now `P` | 0 |
| 6 | still `N` — after three greps each | **10** |
| 7 | **now stated in some form** (rows 2+3+4+5) | **14** |

**Both of the numbered rows closed.** Theorem 7's second and third sentences
(rows 13 and 15) were the only numbered properties of §2/§3 without a Lean
statement; both are now `S+P`. With them, **every conjunct of Theorem 1, 2, 3,
Lemma 4, 5, Theorem 6 and Theorem 7 — all 15 — is stated and proved.** §2/§3 has
no unstated numbered result.

The 10 that remain are all unnumbered prose claims, and they fall into three
groups, given in §4.

Re-derived §2/§3 totals over all 60 rows, r0040's labels with these 24 replaced:

| # | Label | r0040 | r0043 |
| -- | ----- | ----: | ----: |
| 1 | `S+P` | 33 | **46** |
| 2 | `S+H` | 0 | **1** |
| 3 | `S≠` | 3 | 3 |
| 4 | `P` | 0 | 0 |
| 5 | `N` | **24** | **10** |
| — | total | 60 | 60 |

(Row 45 moved `S≠` → `S+P` as well; it is out of scope, so the table above leaves
it at `S≠`. Counting it gives 47 `S+P` and 2 `S≠`. See §5.)

## 2. The 13 rows that are now `S+P`

Every declaration below was opened and read in its file, not inferred from a
module name or a docstring. All are in the build: `lake build` via
`scripts/compile.sh -r r0043` completed 1339 jobs with 0 errors, 0 warnings and
0 `sorry`, and the lakefile globs `["ScottDomains", "ScottDomains.+"]`, so every
module under `ScottDomains/` is elaborated whether or not the root imports it.

| # | Paper's sentence | § / p. | r0040 | now | Declaration and evidence |
| -- | ---------------- | ------ | ----- | --- | ------------------------ |
| 13 | **Thm 7b**: "if `D` and `E` have effective presentations, then `D → E` has an effective presentation as well" | 3.2 / 12 | `N` | **`S+P`** | `ScottDomains.Effective.theorem7_arrow`, `Effective/FunctionSpace.lean:251`. `(d : EffectivePresentation α) (e : EffectivePresentation β) : Nonempty (EffectivePresentation (ScottHom α β))` under `[Domain α] [Domain β] [BoundedComplete β]` — the paper's hypotheses and the paper's conclusion. Proved by `Effective.scottHom` (line 233), whose `enum` is the paper's own step-function enumeration: the `n`-th `Finset (ℕ × ℕ)` read as compact pairs and joined by `ScottHom.ofPairs`, with surjectivity onto `K(D → E)` from `ScottHom.exists_ofPairs_of_isCompactElement` (line 201, `exists_scottHomEnum_eq`). `d` and `e` are genuinely used: they supply the indices and the surjectivity |
| 15 | **Thm 7d**: "Similar facts hold for `D ⊸ E`" — effective presentation | 3.2 / 12 | `N` | **`S+P`** | `ScottDomains.Effective.theorem7_strict`, `Effective/FunctionSpace.lean:270`. The statement is the paper's; the **proof is weaker** and the file says so in its own docstring — `_d` and `_e` are unused and the presentation comes from `nonempty_effectivePresentation`. The `[Domain (StrictHom α β)]` binder is not an extra hypothesis: `example : Domain (StrictHom α β) := PRepFun.strictHomDomain` at line 277 discharges it from the paper's own hypotheses. A weaker proof of the paper's statement is still a proof of it |
| 29 | "the ordinal `ω` … is not a cpo" | 2.1 / 3 | `N` | **`S+P`** | `ScottDomains.Flat.omega_not_cpo`, `FlatOmega.lean:48`. Given as the concrete failing datum rather than a negated typeclass: `Set.univ : Set ℕ` is nonempty and directed and `¬ ∃ u, IsLUB Set.univ u`, from `directedOn_univ_nat` (36) and `not_exists_isLUB_univ_nat` (42) |
| 34 | "any monotone function `f : N⊥ → E` is continuous" | 2.1 / 4 | `N` | **`S+P`** | `ScottDomains.Flat.scottContinuous_of_monotone`, `Flat.lean:255`: `{f : Flat X → E} (hf : Monotone f) : ScottContinuous f` with `[Preorder E]` — weaker in hypothesis than the paper's `E` a cpo, and for every flat cpo rather than `N⊥` alone. `N⊥` is the subject: `abbrev NatBot : Type := Flat ℕ` at line 324, with `example : Domain NatBot := inferInstance` at 339. The proof spends `mem_of_isLUB` (235): a directed subset of a flat cpo contains its own lub |
| 35 | "the function `f : ω⊤ → O` … is monotone, but it is not continuous" | 2.1 / 4 | `N` | **`S+P`** | `ScottDomains.Flat.omegaTop_monotone_not_continuous`, `FlatOmega.lean:101`: `Monotone omegaTest ∧ ¬ ScottContinuous omegaTest`. `ω⊤` is `ℕ∞` (`abbrev OmegaTop`, line 57, with `noncomputable example : CompletePartialOrder OmegaTop := inferInstance` at 59); `O` is `Prop`; `omegaTest x = (x = ⊤)` at line 82 is the paper's `f`. The failure is at one directed set, `natRange`, whose lub is `⊤` |
| 36 | "The function `f*` is monotone" | 2.1 / 4 | `N` | **`S+P`** | `ScottDomains.Kleene.monotone_extension`, `Kleene/Extension.lean:82`. `extension f X = f '' X` (line 77) is the paper's `f*(X) = {f(x) \| x ∈ X}` |
| 37 | "`f*(⋃ᵢ Xᵢ) = ⋃ᵢ f*(Xᵢ)`. In particular, `f*` is continuous" | 2.1 / 4–5 | `N` | **`S+P`** | `ScottDomains.Kleene.extension_iUnion`, `Kleene/Extension.lean:86` (the paper's indexed form) and `scottContinuous_extension`, line 103. The paper's "in particular" is reproduced as the inference: continuity is `scottContinuous_set_iff.mpr` applied to monotonicity plus `extension_sUnion` (92), with no directedness used |
| 39 | factorial: "`F` is continuous (but not strict)", and "`F` has a least fixed point `fix(F)` and this solution will satisfy the equation for `fact`" | 2.2 / 5 | `N` | **`S+P`** | Four declarations in `Kleene/Factorial.lean`: `scottContinuous_factFun` (239), `factFun_ne_bot` (265, `factFun ⊥ ≠ ⊥` — the paper's parenthesis), `isLeast_kleeneFix_factFun` (275, `theorem1` applied to `F`), and `kleeneFix_factFun_apply` (281, `(kleeneFix factFun).val (NatBot.of n) = NatBot.of n.factorial`). `kleeneFix_factFun_eq` (316) goes past the paper and identifies the solution as `factHom` |
| 40 | grammars: the three operators "are all continuous in the variable `X`", the three equations "all have least solutions", and "These solutions are the languages defined by the grammars" | 2.2 / 6 | `N` | **`S+P`** | Nine declarations in `Kleene/Grammar.lean`, three per sentence: `scottContinuous_gram1/2/3` (127, 131, 135); `isLeast_gram1/2/3` (144, 148, 152), each `theorem1` applied to the corresponding operator; `kleeneFix_gram1/2/3` (168, 196, 234), identifying the three least fixed points with `langStar a`, `langNest a b` and `langEven a` — the languages of `E ::= ε \| Ea`, `E ::= a \| bEb`, `E ::= ε \| aa \| EE` |
| 41 | "the function `fix_D : (D → D) → D` given by `fix_D(f) = ⨆ₙ fⁿ(⊥)` is actually continuous" | 2.3 / 7 | `N` | **`S+P`** | `ScottDomains.Kleene.scottContinuous_kleeneFix`, `Kleene/FixContinuous.lean:110`: `ScottContinuous fun f : ScottHom α α => kleeneFix ⇑f`. `fixHom` (126) bundles it as a `ScottHom (ScottHom α α) α`, which is the paper's `fix_D` as a member of the function space. This is exactly what r0040's N13 recorded as absent — `kleeneFix` was then a bare `(α → α) → α` with nothing said about its monotonicity or continuity in `f` |
| 42 | "We leave it to the reader to show that `fix` is a uniform fixed point operator" | 2.3 / 7 | `N` | **`S+P`** | `ScottDomains.Kleene.kleeneOperator_isUniform`, `Kleene/Uniform.lean:103`: `(kleeneOperator.{u}).IsUniform`, proved from `map_kleeneFix_of_commutes` (83). This is Theorem 3's existence half; `theorem3_existsUnique` (126) now states both halves as `∃! F : FixedPointOperator, F.IsUniform`. r0040 recorded this row as `N` rather than `P` because `UniformFixedPoint.lean`'s docstring declined to assert it; the assertion now exists and is kernel-checked |
| 46 | "This allows us to characterize … a continuous function `f : P N → P N` between uncountable cpo's with a countable set `G_f`" | 3 / 9 | `N` | **`S+P`** | `ScottDomains.Kleene.characterization_powersetNat`, `Kleene/Graph.lean:145`: for continuous `f : Set ℕ → Set ℕ`, the conjunction `(graphPairs f).Countable ∧ (∀ x, sSup (recoverAt f x) = f x) ∧ ¬ Countable (Set ℕ)` — countable graph, pointwise recovery, uncountable carrier, which is the sentence's three parts. `graphPairs f = {p \| IsCompactElement p.1 ∧ IsCompactElement p.2 ∧ p.2 ≤ f p.1}` (53) is the paper's `G_f` verbatim: both coordinates restricted to compacts, downward closed in the second. `not_countable_powersetNat` (127) is Cantor via `Function.cantor_surjective` |
| 60 | "we will discuss a great many operators like `· → ·` and `· ⊸ ·`. We will leave it to the reader to convince himself that all of these operators preserve the property of having an effective presentation" | 3.2 / 12 | `N` | **`S+P`** | `ScottDomains.Effective.operator_preserves_effectivePresentation`, `Effective/FunctionSpace.lean:288`: for any `γ` with `[Domain γ]`, given presentations of `α` and `β`, `Nonempty (EffectivePresentation γ)`. That form subsumes the paper's claim — instantiate `γ` at each operator's value — so the claim is proved. It is proved *vacuously*, and the module says so: `_d` and `_e` are unused, because `nonempty_effectivePresentation` (124) shows **every domain has an effective presentation** as the structure currently renders the definition. See the caveat below |

### The caveat attached to rows 13, 15 and 60

`Effective/FunctionSpace.lean` proves as its first theorem
(`nonempty_effectivePresentation`, line 124) that **every domain has an
`EffectivePresentation`**: `Domain` already gives a countable nonempty `K(D)`,
hence a surjection `ℕ ↠ K(D)`, and both decidability fields are dischargeable by
`Classical.dec`. So `EffectivePresentation` as rendered adds nothing to `Domain`,
and rows 13, 15 and 60 are all corollaries of `Domain` instances the development
already had.

This does not change the labels — the paper's statements are written in Lean and
the kernel accepts proofs of them — but it should be recorded next to the count.
The module records it too, and supplies the non-vacuous strengthening as four
named `Prop`s: `RecursiveNormal` (307), `IsRecursive` (316), the structure
`RecursivePresentation` (347, **deliberately uninstantiated**),
`Theorem7ArrowRecursive` (390), `Theorem7StrictRecursive` (405), and
`PreservesRecursivePresentation` (420). None is discharged. The two obstructions
are named and are recursion theory rather than domain theory: Mathlib v4.32.2
states no `Primrec`/`Computable` fact about `Nat.lor`/`Nat.bitwise`/`Nat.testBit`
(so `RecursiveLE` for `P N` is unreachable), and `REPred`'s API supplies closure
under neither `∧` nor `∃`.

Row 13's proof does not take the vacuous shortcut — `theorem7_arrow` goes through
`scottHom`, the paper's step-function enumeration. Rows 15 and 60 do.

## 3. The one row that is now `S+H`

| # | Paper's sentence | § / p. | r0040 | now | Evidence |
| -- | ---------------- | ------ | ----- | --- | -------- |
| 58 | Thm 7 proof: "The proof that the poset of step functions has decidable ordering and finite normal subposets is tedious, but not difficult, using the effective presentations of `D` and `E`" | Thm 7 proof / 12 | `N` | **`S+H`** | `ScottDomains.Effective.StepFunctionsDecidable`, `Effective/FunctionSpace.lean:374`: `def StepFunctionsDecidable (d e) : Prop := IsRecursive (scottHom d e)`. The paper's sentence is written down, against the enumeration that *is* the step-function enumeration, and it is **not proved**. `exists_isRecursive_of_stepFunctionsDecidable` (382) proves it implies Theorem 7's second sentence at recursion-theoretic strength, which is the paper's own proof structure |

The openness here is a **named unproved `Prop`, not a `sorry`** — which is why
the development is `sorry`-free and this row is still not `S+P`. If the
orchestrator prefers the label set to distinguish "hypothesis-shaped `def`, never
discharged" from "`sorry` in a proof", this row is the case that forces the
question; r0040's label set has no third option, and `S+H` ("stated, proof open")
is the closest fit.

At the weaker `DecidablePred` reading the sentence *is* discharged —
`scottHom`'s `decidableLE` and `decidableNormal` exist — but they are
`Classical.dec`, which is the degeneracy above, so reading the row that way would
label it `S+P` on no content at all.

## 4. The 10 rows that are still `N`, with their three greps

Every count is `grep -rEni --include='*.lean'` over
`ScottDomains/ScottDomains/`, docstrings included: a docstring hit is what would
make a row `P` rather than `N`. The probe script is
`scripts/a1-remeasure-greps.sh`; it is read-only and writes nothing.

| # | Property | Grep 1 | Grep 2 | Grep 3 | Verdict |
| -- | -------- | ------ | ------ | ------ | ------- |
| 30 | "`Q` [the rationals] … fail[s] to be a cpo" (row 30) | `sqrt\|square root` → **0** | `CompletePartialOrder .{0,4}(Rat\|ℚ)\|LinearOrderedField` → **0** | `rationals.{0,40}(not\|fail)\|(not\|fail).{0,40}(a cpo\|cpo)` → 22, all read: 4 are `FlatOmega`'s new `ω`-is-not-a-cpo rows, the other 18 are unrelated sentences containing "not" near "cpo" | **`N`**. `ω` was closed this round and `ℚ` was not; the paper's reason for `ℚ` is the Dedekind-cut argument (a bounded increasing sequence of rationals approximating `√2`), and nothing in the package builds it |
| 31 | "the unit interval `[0,1]` of real numbers does form a cpo" (row 31) | `unitInterval\|Set\.Icc` → **0** | `ℝ\|Real\.\|Mathlib\.Data\.Real` → 3, all prose (`PropertyM.lean:105` on `ℝᵒᵖ` as a non-well-ordered index, `LemThirty.lean:144` "the difference is real", `JungBicomplete.lean:527` on finite subsets of `ℝ`) — **the reals are still not a carrier anywhere in the package** | `unit interval` → 1, `Dyadic.lean:100`, about `ℚ ∩ [0,1)` | **`N`** |
| 33 | "In fact, this is true whenever `D` has no infinite ascending chains" (row 33) | `WellFoundedGT\|IsWellFounded\|WellFoundedLT` → 2, both read: `Iwamura.lean:135` (a monotone image of a well-ordered index is well-ordered) and `JungBicomplete.lean:533` (the well-ordering theorem) — neither is the chain condition on `D` | `ascendingChain\|noInfiniteAscending\|StrictMono.{0,24}bounded\|ACC\|ascending chain condition` → 12, every one a false positive on the substring `acc` inside "accepts"/"account"/"accurate"/"accordingly"/"accidentals"/"access" | `scottContinuous_of_monotone` → 9, in two places: `Flat.lean:255` (the flat case, row 34, closed this round) and `Kleene/Factorial.lean:152` (the same fact for that file's own flat naturals) | **`N`**. The generalization now has **two** instances proved below it — the finite case (`FinitaryProjectionEmbedding.scottContinuous_of_monotone_of_finite`, row 32) and the flat case — and neither is the chain condition. A flat cpo *has* no infinite ascending chains, so this row is a strict generalization of row 34, not an unrelated claim |
| 38 | "a function `f : [0,1] → [0,1]` … may be continuous in the cpo sense without being continuous in the usual sense" (row 38) | `TopologicalSpace\|nhds\|Metric` → 5, all false positives on the substring `metric` inside "antisymmetric"/"symmetric" | `usual sense\|topologically continuous\|Continuous \(` → 91, all `ScottContinuous (…)` in the order-theoretic sense; `usual sense` and `topologically continuous` → **0** | `ScottTopology\|scottTopology\|IsScott` → 2, both `ExistingTheories.lean:23–24`, which are `#check @Topology.IsScott` / `#check @Topology.IsScottHausdorff` — commands, not declarations | **`N`**. Unchanged from r0040: the package imports `Mathlib.Topology.Order.ScottTopology` and no declaration uses it, so there is no second notion of continuity for a claim to separate |
| 43 | "With the exception of the unit interval of real numbers, all of the cpo's we have mentioned so far are domains" (row 43) | `mentioned so far\|discussed so far\|so far are` → 1, `FlatSection6.lean:14`, a quotation of §6 about operators | `every cpo (we\|so far)\|all of the cpo` → **0** | `all of the domains\|all the domains` → **0** | **`N`**, and the underlying situation improved without closing it: of §2.1's example list (`I`, `O`, `T`, `N⊥`, `ω`, `ω⊤`, `P S`, `Q`, `[0,1]`), r0040 found only `P S` in the development; `T`, `N⊥`, `ω` and `ω⊤` now exist too (`Flat.lean:329, 324`, `FlatOmega.lean:57`). `Q` and `[0,1]` still do not, and the meta-claim quantifying over the list is not stated |
| 44 | "The compact elements of the domain `N⊥ → N⊥` are the functions with finite domain of definition" (row 44) | `finite domain of definition\|finiteSupport\|finite support\|domain of definition` → **0** | `ScottHom \(Flat\|ScottHom NatBot\|ScottHom \(NatBot` → **0** — the function space is never formed at the flat naturals | `compacts \(ScottHom\|isCompactElement.{0,30}NatBot\|NatBot.{0,30}isCompactElement` → 26, all the general `K(D → E)` machinery in `FunctionSpaceCountable`/`CompactFunction` or `Flat.compacts_eq_univ` (`K(X⊥) = X⊥`, a different statement) | **`N`**. `N⊥` now exists, so the row has a subject for the first time; but `N⊥ → N⊥` is never formed and its compacts are never characterized |
| 47 | "One can show that each of `f` and `g` uniquely determines the other" (row 47) | `uniquely determines\|unique_projection\|projection_unique\|unique_embedding` → **0** | `eq_of_isEmbeddingProjectionPair\|embedding_eq\|projection_eq\|determines_` → **0** | `determines the other\|determined by` → 10, and all ten were read: `Kleene/Graph.lean:107` (a continuous function is determined by `G_f` — new this round, and a different pair), `SFP.lean:172` (a projection is determined by its image), `ContinuousConstruction.lean:289`, `Skeleton/Lemma17.lean:363`, `FlatPowerdomain.lean:962`, `ClosureProperties/SeparatedSum.lean:198`, `Kleene/Uniform.lean:108`, `ContinuousAlgebra.lean:636`, `NormalProjection.lean:4`, `Section62.lean:360` — none is the embedding–projection pair claim | **`N`** |
| 54 | "A domain `D` is bounded complete if and only if the cpo `D⊤` which results from adding a new top element to `D` is an algebraic lattice" (row 54) | `WithTop\|adjoinTop\|addTop\|withTop` → 18, all read: 16 are `PowerdomainCompacts.lean`'s `abbrev Chain := WithTop ℕ` and its `WithTop.coe_*` lemma applications, 1 is `FlatOmega.lean:78` (`ℕ∞`), 2 are Mathlib imports. **A top is adjoined to `ℕ`, never to a domain `D`** | `algebraic lattice.{0,32}iff\|iff.{0,32}algebraic lattice\|AlgebraicLattice` → 3, all `RecursiveDomain.lean:213–226`'s `IsCountablyBasedAlgebraicLattice` and the §7 universality results about it — a predicate, not the equivalence | `boundedComplete_iff\|BoundedComplete .{0,4}↔\|↔.{0,4}BoundedComplete` → **0** | **`N`** |
| 56 | "the bounded complete domain `N⊥ ⊸ N⊥` lacks a top element and therefore fails to be an algebraic lattice" (row 56) | `lacks a top\|no top element\|OrderTop\|IsTop\|¬ *∃.{0,12}top` → 1, `Dyadic.lean:28`, about `[0,1)` in the dyadic construction | `StrictHom NatBot\|StrictHom \(Flat\|StrictHom \(NatBot` → 7, **all in `Kleene/Factorial.lean`** (193, 196, 253, 265, 267, 276, 311) and all about `factFun`/`factHom`; none says anything about a top element of the type | `fails to be an algebraic lattice\|not an algebraic lattice` → **0** | **`N`**, and this is the sharpest change of situation without a change of label: `N⊥ ⊸ N⊥` is now a type the development inhabits — the factorial functional lives in it — but nothing states that it has no top |
| 57 | "All of the domains we have discussed so far are bounded complete" (row 57) | as row 43 | as row 43 | as row 43 | **`N`**. Same meta-claim shape as row 43 and the same reason |

If the orchestrator prefers to exclude meta-claims of rows 43 and 57's shape —
r0040 offered this — the §2/§3 property total drops 60 → 58 and the remaining
`N` drops **10 → 8**.

### The 10, grouped

Three carriers the development still does not build account for six of them:
the reals (rows 31, 38) and the rationals (row 30) — three rows; and the two
meta-claims quantifying over §2.1's example list (rows 43, 57), which cannot be
stated until those carriers exist. Two more are about `N⊥`'s function spaces
(rows 44, 56), whose *carriers* now exist but whose claimed properties are not
stated. The last two are independent order-theoretic facts: the chain condition
(row 33) and the embedding–projection uniqueness (row 47), plus the `D⊤`
equivalence (row 54).

## 5. Findings outside the 24 rows

1. **No regression.** All 43 in-package declaration names that r0040 cited as
   evidence for an `S+P` or `S≠` row still have a defining occurrence.
   `scripts/a1-r0040-decls-still-present.sh` greps each for its `theorem`/
   `lemma`/`def`/`instance`/`abbrev`/`structure` line: 43 present, 0 missing.
   (The first run reported `strictFun_bot` missing; that was a defect in the
   script's regex, which did not allow an `@[simp]` prefix before the keyword.
   Fixed, and the name is at `ClosureProperties/StrictFunction.lean:65`.)

2. **Row 45 moved `S≠` → `S+P`**, in the improving direction, and is out of this
   round's scope. r0040 labelled the recovery formula `S≠` because the
   development's family was `graphOn v = {(k, v k) \| k ∈ K(D)}`, which restricts
   only the first coordinate to compacts. `Kleene/Graph.lean:53` now defines
   `graphPairs`, which is the paper's `G_f` with both coordinates compact and
   downward closed in the second, and `sSup_recoverAt` (94) is the paper's
   equation `f(x) = ⨆{y₀ \| (x₀,y₀) ∈ G_f, x₀ ⊑ x}` for it. That is what makes
   row 46 provable: only the paper's version has both coordinates in a countable
   set. The proof needs `BoundedComplete β`, which the paper does not state and
   the argument cannot do without — `recoverAt` is directed only because two of
   its members are bounded by a common `f(x₃)`; `P N` is bounded complete, so
   the paper's example is covered.

3. **The flat naturals are constructed twice.** `ScottDomains.Flat.NatBot`
   (`Flat.lean:324`, `= Flat ℕ`) and `ScottDomains.Kleene.NatBot`
   (`Kleene/Factorial.lean:55`) are two different types with the same order, each
   with its own `PartialOrder`, `CompletePartialOrder`, `mem_of_isLUB` and
   `scottContinuous_of_monotone`. `Kleene/Factorial.lean:31–35` records the
   duplication and says the local copy should be replaced by the general one.
   This is not a regression and it changes no label, but it means rows 44 and 56
   now have *two* candidate subjects and neither copy carries the claims.

## 6. Measurement invariance

No `.lean` file was opened read-write. `scripts/compile.sh -r r0043` →
`ScottDomains/logs/compile-20260808-163534.agent1.log`:

    jobs:             1339
    lean diagnostics: 0
    lake errors:      0
    sorry decls:      0
    other warnings:   0

`scripts/counts.sh`, unchanged across the round:

    modules:  100
    lines:    37300
    theorems: 1773
    sorry:    0 in 0 file(s)

Three files were written, all in `scripts/`, all read-only over the package:
`a1-remeasure-greps.sh` (the evidence for §4),
`a1-r0040-decls-still-present.sh` (the evidence for §5.1), and this report.
