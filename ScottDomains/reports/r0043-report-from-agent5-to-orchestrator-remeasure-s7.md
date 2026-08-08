---
round: r0043
from: agent5
to: orchestrator
subject: remeasure-s7
date: 2026-0808-16:36
started: 2026-0808-16:31
finished: 2026-0808-16:36
related:
  - plans/r0043-plan-from-orchestrator-to-orchestrator-remeasure-unstated.md
  - reports/r0040-report-from-agent5-to-orchestrator-property-coverage-s7.md
---

# §7 re-measurement — the 13 `N` rows against the tree after r0041 and r0042

## Headline

**Zero of the 13 moved. All 13 are still `N`.** The two `P` rows in this area are
still `P`.

This is the outcome r0041 predicted when it deferred §7.2's five λ-calculus rows
and most of §7.1/§7.3's solvability and representability rows, and the
re-measurement confirms it rather than inheriting it: every row was re-grepped
three ways over the tree as it stands, and the transcripts are reproducible by
`scripts/a5-r0043-greps.sh` and `scripts/a5-r0043-followup.sh`.

| # | Quantity | r0040 | now |
| -- | -------- | ----: | --: |
| 1 | `N` rows in §7 | 13 | **13** |
| 2 | of those, now stated | — | **0** |
| 3 | `P` rows in §7 (paper properties) | 5 | 5 |
| 4 | `P` rows, development-side refutations | 2 | 2 |

**What did change is expressibility, not statedness.** Row 23's carrier `N⊥` now
exists (`ScottDomains.Flat.NatBot`), so its sentence is writable in Lean for the
first time; nothing writes it. That distinction is the substance of this report
and is spelled out per row below.

## The 13 rows, r0040 label and label now

Every grep below is `grep -rn … ScottDomains/ScottDomains --include=*.lean`. The
three greps per row are **the same three r0040 ran**, so the two measurements are
comparable; where a fourth or fifth probe is listed it is an addition aimed at the
r0041 modules the plan named.

| # | Claim (paper's sentence) | § / p | r0040 | now | Evidence — the three greps |
| -- | ----- | ----- | ----- | --- | ---------- |
| 1 | the full simple binary tree with limit points added is a solution of `T ≅ T + T` | 7 / 33 | `N` | **`N`** | `IsSolvable\|Solves ` → 9 hits, unchanged in kind: the two definitions (`RecursiveDomain.lean:79,84`) and the same **two** solvability theorems, `Recursive.recursiveDomain_funSpace` and `PowerdomainRep.recursiveDomain_prod`. `IsSolvable.*sepSum` → 0. `binaryTree` → 0 |
| 2 | a composition of representable operators is representable | 7.1 / 34 | `N` | **`N`** | `IsRepresentable.comp` → 0. `isRepresentable_comp` → 0. `[Rr]epresentable.*compos` → 0. Added: `opComp\|compOp\|IsRepresentable₂.comp` → 0 |
| 3 | `X ≅ X × I⊤` has `(I⊤)^N` as a solution, and `(I⊤)^N ≅ P N` | 7.1 / 34 | `N` | **`N`** | `twoPoint\|TwoPoint\|Sierpinski` → 0. `Set ℕ ≃o` → 0. `ℕ → Prop` → 2, both `DecidablePred` binders in `Atomless.lean`. Added `I⊤\|Itop\|topOf\|WithTop PUnit` → 0 |
| 7 | the constant operator `X ↦ L` is representable over `P N`, for `L` an algebraic lattice | 7.1 / 36 | `N` | **`N`** | `constOp` → 0. `isRepresentable_const` → 0. `constant operator` → 1, and it is still the *other* claim (`Universality.lean:283`, row 8's biconditional). Added `[Cc]onstOp\|constFun\|const_rep\|repConst` → 0 |
| 11 | λ-equation 1: `(λx. E) = (λy. [y/x]E)` (α) | 7.2 / 37 | `N` | **`N`** | `alpha\|beta_\|eta_conv\|_beta\|_eta\b` → 15 hits, every one `mpairMap_eta` / `mem_upper_eta` / `stgEmb_ne_mk_eta`, which are §7.4's `x ↦ (x,{x})`. `LamTerm\|inductive Term` → 0. `subst` → 54, every one the `subst` tactic or the English word |
| 13 | λ-equation 3: `(λx. E(x)) = E` (η) | 7.2 / 37 | `N` | **`N`** | `lam_app` → 0. `eta_law` → 0. `_eta\b` → 14, all §7.4's `eta` as above. `Combinator.LambdaModel` still has `app_lam` and no converse field |
| 16 | λ-equation 6: `pair(fst(E))(snd(E)) = E` (surjective pairing) | 7.2 / 38 | `N` | **`N`** | `pair_fst_snd` → 0. `surjective pairing` → 0. `lam_app` → 0 |
| 17 | equations 3 and 6 are independent of the other four | 7.2 / 38 | `N` | **`N`** | `independen` → 17 hits, none about λ-equations. `pointwise pair` → 0. `LambdaModel` → 20 hits, all in `Combinator.lean`, no independence result among them |
| 18 | `pair(x)(y) = (λz. pair(x(z))(y(z)))` is independent of the six, and a model for it exists | 7.2 / 38 | `N` | **`N`** | `pointwise pair` → 0. `independen` → as row 17. `LambdaModel` → as row 17 |
| 19 | `(· + ·)⊤` is representable over `P N` | 7.3 / 40 | `N` | **`N`** | `WithTop` → 18 hits, up from 2: two Mathlib imports plus `PowerdomainCompacts.Chain := WithTop ℕ` and one line of `FlatOmega`, none about a sum operator. `sumTop\|topSum` → 0. `unmotivated\|gets in the way` → 0 |
| 20 | `B = U₀ ∪ {∅}` is a countable atomless Boolean algebra, hence the free one, hence universal for countable Boolean algebras | 7.3 / 41 | `N` | **`N`** | `[Bb]ooleanAlgebra` → 0. `IsAtomless` → 2, both prose saying Mathlib has none. `Vaught` → 2, both prose saying the route is **not** taken |
| 21 | `i : x ↦ ↑x` is a monotone injection preserving existing lubs, and `u ⊆ A` is bounded iff `⋂_{x∈u} ↑x ≠ ∅` | 7.3 / 41 | `N` | **`N`** | `upperClosure` → 0. `Ici` → 0. `principalFilter` → 0 |
| 23 | `X ≅ N⊥ + (X → X)` has a solution, represented over `U` by `p ↦ R+(R_{N⊥}(p), R→(p,p))` | 7.3 / 41 | `N` | **`N`** | see below — the carrier arrived, the sentence did not |

### Row 23 is the one row where the measurement genuinely moved, and it still lands on `N`

r0040 recorded `N⊥` → **1 hit** (an unrelated `(N⊥)♭` remark in `Powerdomain/Smyth.lean`), `WithBot ℕ` → 0, `LazyNat|natOp|NatBot` → 0. Now:

| # | grep | r0040 | now | what the hits are |
| -- | ---- | ----: | --: | ----------------- |
| 1 | `N⊥` | 1 | **48** | `Flat.lean` (§2.1's carrier), `FlatPowerdomain.lean` (§5.2–§5.3's three powerdomains of `N⊥`), `Kleene/Factorial.lean` (§3's factorial). None in §7 |
| 2 | `WithBot ℕ` | 0 | **1** | `Flat.lean:25`, a docstring explaining why `Flat X` is used instead |
| 3 | `LazyNat\|natOp\|NatBot` | 0 | **66** | every one an occurrence of `NatBot`, the abbreviation, in §2/§3/§5 files |

So `N⊥` exists: `ScottDomains.Flat.NatBot : Type := Flat ℕ` (`Flat.lean:324`), with
`Domain`, `BoundedComplete` and `Countable` instances confirmed at
`Flat.lean:339,341` and `compacts NatBot = Set.univ` at `Flat.lean:363`. **The
sentence is now expressible where in r0040 it was not.** It is still not written.
Three further probes, all zero:

* `sepSum.*funSpace\|funSpace.*sepSum` → 0 — the operator `X ↦ N⊥ + (X → X)` is nowhere formed;
* `NatBot.*[Rr]epresentable\|[Rr]epresentable.*NatBot` → 0 — `R_{N⊥}` does not exist;
* `Solves.*Flat\|IsSolvable.*Flat` → 0 — and the complete list of solvability statements in the package is still exactly two, `recursiveDomain_funSpace` and `recursiveDomain_prod`.

The label is `N` by the round's own rule: a row is `S+P` only when a declaration
is named and confirmed, and there is none.

### Row 3: r0040's second grep was directionally weak, and fixing it does not change the label

r0040 ran `Set ℕ ≃o` and got 0. The symmetric form `≃o Set ℕ` — which r0040 did
not run — now returns 2 hits, `FlatPowerdomain.hoareOrderIso : Hoare.Powerdomain
NatBot ≃o Set ℕ` and its wrapper. **That is §5.2's `(N⊥)♭ ≅ P N`, not §7.1's
`(I⊤)^N ≅ P N`** — a different left-hand side. `I⊤` itself greps to 0 under four
spellings. The row stays `N`; the correction is recorded because the r0040
transcript would otherwise be read as covering both directions of `≃o`.

### Rows 2 and 7: what the r0041 modules actually added

The plan flagged these as possibly moved by `Morphism.lean` and `PowerdomainMap`.
Measured directly rather than inferred:

* `Morphism.lean` has **44 declarations** (`scripts/lean-decls.py --list`). Every one is about a **map** — `prodMap`, `smashMap`, `smashProdMap`, `liftMap`, `copair`, `separatedSumCopair`, `strictComp`, and the multiary `multiProd`/`multiSum`/`multiPair`/`multiCopair`. None mentions `IsRepresentable`. `prodMap_comp` is functoriality of `f × g`, not composition of representable operators.
* The only structural closure lemma about `IsRepresentable` in the package is still `Recursive.IsRepresentable₂.diag` (`RecursiveDomain.lean:365`), which is **diagonalization**, not composition. Row 2 is `N`.
* For row 7, `ScottHom.const` (`ScottHom.lean:107`) and `Combinator.constHom` (`Combinator.lean:151`) exist, but both are the constant **function** `α → β`; row 7 needs the constant **operator** on `Cpo`, `IsRepresentable U (fun _ => L)`. The two `IsRepresentable U (fun X => …)` statements in the package are `fun X => prodCpo (cpoOf U) (prodCpo X X)` and `fun X => Cpo.funSpace X E` (`Universality.lean:341,362`); neither is constant in `X`. Row 7 is `N`.

## The two `P` rows: both still `P`

| # | Claim | r0040 | now | Evidence |
| -- | ----- | ----- | --- | -------- |
| 1 | Theorem 26 is **false** for a signature admitting arity `0` | `P` | **`P`** | `Combinator.lean:60–72` still carries the argument in prose and still says of itself "which is stated here and is *not* Lean-checked". `arity 0\|arity zero\|thm26_false\|thm26_arity\|nullary` → 0; `thm26.*false\|false.*thm26` → 0. No declaration |
| 2 | `Colimit.Thm29Second` is **stronger** than the printed sentence and **false** without `[Domain E]` | `P` | **`P`** | `LemThirty.lean:506–512` is unchanged prose. `countable_compacts_of_reflects` (line 513) is still the kernel-checked part; the step from it to "an uncountable flat cpo is bifinite, so no such `f` exists" is still not. `Thm29Second.*false\|thm29Second_false\|not_thm29Second\|uncountable.*flat` → 1 hit, that same docstring line |

**Row 2 of this table is now the cheapest unclosed item in my area.** The
refutation needs an uncountable flat cpo, and r0041 built the general
construction: `Flat X` is a `Domain` for any `X`, so `Flat ℝ` supplies the
witness. r0040 could not have written this; the tree now can. It was not written
this round because no `.lean` file is edited under this plan.

## Two findings not in scope, reported and not pursued

1. **`N⊥` is defined twice, under two namespaces, with the instances re-proved.**
   `ScottDomains.Flat.NatBot` is `Flat ℕ` (`Flat.lean:324`); `ScottDomains.Kleene.NatBot`
   is a separate two-constructor `inductive` (`Kleene/Factorial.lean:55`) carrying
   its own `PartialOrder`, `SupSet` and `CompletePartialOrder` instances and its
   own `scottContinuous_of_monotone`, which duplicates `Flat.scottContinuous_of_monotone`.
   `Kleene/Factorial.lean:31–35` states the intent: "when the general construction
   lands, `NatBot` should be replaced by its instance". The general construction
   landed in the same round (r0041) and the replacement did not happen. This is
   not a regression of any measured row — both objects are correct — but it is one
   concept under two terms, and either could drift.
2. **Lemma 28's `(·)♯` and `(·)♭` conjuncts were restructured, not discharged.**
   r0041 added `PowerdomainMap.Rep.repSmythAtU`, `repHoareAtU` and
   `lemma28AtU_of''`, and the file's own docstring gives the arity honestly: 9 →
   5 → 2 → **4**. The four are different in kind (facts about a functor rather
   than about `Fp(U)`'s retraction pair) but they are still open hypotheses, so
   §2 rows 20 and 21 of the r0040 report remain `S+H`. No regression; no
   improvement to the coverage label either.

## What did not change

No `.lean` file was edited. `scripts/counts.sh` measures **100 modules, 37300
lines, 1773 theorems, `sorry` 0 in 0 files** — identical to the r0042 head
commit. Every `sorry` string in the package (38 occurrences) is inside a
docstring or comment; none is a tactic. The numbered-result count is untouched.
Two scripts were added, `scripts/a5-r0043-greps.sh` and
`scripts/a5-r0043-followup.sh`, both read-only over the sources.

## Answer to the round's question, for row 2e

Of §7's **13** unstated properties, **0** are now stated and **13** remain `N`.
