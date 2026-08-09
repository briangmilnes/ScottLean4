# Status — one line per numbered result

The short answer. `PaperInventory.md` is the long one and stays as the audit
trail; this file is the thing to read first.

Measured on `main` after r0047: build **1364 jobs, 0 errors, 0 warnings**,
`sorry` **0**, `axiom` **0**, `sorryAx` **0**. Package: 117 modules, 43,481
lines, 2,019 theorems.

## Labels

Every paper property carries one of five labels. They answer two questions —
**is it stated in Lean, and is it proved** — and the pair matters because
**`sorry` can only see the second.**

| # | Label | Stated? | Proved? | Meaning |
| -- | ---- | ------- | ------- | ------- |
| 1 | `S+P` | yes, as the paper states it | yes | done |
| 2 | **`S+H`** | yes, as the paper states it | **no — the proof is open** | a real Lean statement with a hole. `H` is for *hypothesis*: the result is available only conditionally, as a theorem taking the open claim as an argument |
| 3 | `S≠` | yes, but **not the paper's statement** | yes | a weakening, an added hypothesis, or a deliberate repair of a printed defect |
| 4 | `P` | no — prose only | — | asserted in a docstring, never under the kernel |
| 5 | `N` | **no statement at all** | — | nothing in Lean mentions it |

Two consequences worth stating once:

* **`sorry` 0 does not mean "everything is proved."** A `sorry` is a hole in a
  proof someone *started*. Rows 4 and 5 were never started, and row 2's holes are
  carried as explicit hypotheses rather than as `sorry`, so none of the three
  appears in a `sorry` count. That is why this file reports rows 8–11 of the
  counts separately.
* **`S≠` is not automatically a defect.** Five of the 18 are repairs of the
  paper's own printed errors, which is correct work; 13 are ours.

## Counts

| # | | Count |
| -- | --- | ----: |
| 1 | Numbered results in Gunter & Scott | 30 |
| 2 | — **fully proved** | **25** |
| 3 | — partly proved, some part open | 3 |
| 4 | — **refuted as stated** (our transcription or the paper) | 2 |
| 5 | — status not yet established | 1 (result 2; r0048 in flight) |
| 6 | Paper properties (numbered conjuncts + prose claims) | 239 |
| 7 | — `S+P` stated and proved | 169 |
| 8 | — **`S+H` stated, proof open** | **12** |
| 9 | — `S≠` stated, but not as the paper states it | 18 (13 ours, 5 repairs) |
| 10 | — `P` + `N` no Lean statement at all | 36 |
| 11 | `Prop`-valued claims nothing proves | **7** (8 strict) |

Rows 8 and 11 are the two kinds of unfinished work, and they are different:
row 8 is a real Lean statement whose proof is open; row 11 is a `def` naming a
claim **nobody attempted**. **`sorry` 0 sees neither** — which is why both are
counted here and neither shows up in a build.

## The 30 numbered results

`P` proved · `p` partly proved · `R` refuted as stated · `—` not in the tree

| # | Result | | Status |
| -- | ----- | -- | ------ |
| 1 | Theorem 1 | `P` | least fixed point, and below every fixed point |
| 2 | Theorem 2 | `—` | **not quoted anywhere in the tree or the docs** |
| 3 | Theorem 3 | `P` | `theorem3`, `theorem3_existsUnique` |
| 4 | Lemma 4 | `P` | `NormalSubposet.lean` |
| 5 | Lemma 5 | `P` | `FinitaryProjection.lean` |
| 6 | Theorem 6 | `P` | `theorem6` |
| 7 | Theorem 7 | `p` | sentence 1 proved; sentences 2–3 proved only at the degenerate strength — **every domain has an `EffectivePresentation`** because `Classical.dec` fills its fields. The recursive forms are open: `Theorem7ArrowRecursive`, `Theorem7StrictRecursive` |
| 8 | Lemma 8 | `P` | `Product.lean` |
| 9 | Lemma 9 | `P` | `lem9_*` — **two printed misprints repaired** (items 3 and 5) |
| 10 | Lemma 10 | `P` | 7 conjuncts, `lem10_{prod,smash,sum,separated,lift,strict}` |
| 11 | Theorem 11 | `P` | `thm11`, with `thm11_converse` |
| 12 | Theorem 12 | `P` | `thm12` and the three powerdomains |
| 13 | Lemma 13 | `P` | `lem13_smyth`, `lem13_hoare` |
| 14 | Theorem 14 | `P` | `thm14`, both directions |
| 15 | **Proposition 15** | `P` | *"A bounded complete domain is bifinite"* — printed folio 31. `prop15` at `Skeleton/Section6.lean:134`, proved since that file was written. **It is a Proposition, not a Theorem or Lemma**, which is the whole reason it read as missing: both instruments that produced the gap searched only for `thm|theorem|lem|lemma` |
| 16 | Theorem 16 | `P` | `thm16`, `thm16_positive` |
| 17 | Lemma 17 | `P` | 10 conjuncts. r0047 **removed `[BoundedComplete β]`** from `lem17_fun` and `lem17_strictFun` |
| 18 | Theorem 18 | `P` | `thm18` — closed r0042, `[propext, Classical.choice, Quot.sound]` |
| 19 | Lemma 19 | `P` | `lem19` |
| 20 | Lemma 20 | `P` | `lem20` |
| 21 | Theorem 21 | `P` | `thm21` |
| 22 | Theorem 22 | `P` | `thm22` |
| 23 | Lemma 23 | `P` | `lem23` |
| 24 | Lemma 24 | `P` | `lem24` (Gunter & Scott's; **not** Gunter 1987's Lemma 24, below) |
| 25 | Theorem 25 | `P` | `thm25`, `thm25_isUniversal` |
| 26 | Theorem 26 | `p` | `thm26` carries an added `hs : ∀ i, 0 < s i` — no nullary operations — which the paper does not assume. The recorded justification, that Theorem 26 is **false** for a signature admitting arity 0, **is not established**: the contradiction is derived from `fst(ψ(x)) = x`, a property of the paper's *construction* and of our own conclusion, whereas the printed statement asks only that `A` "be made isomorphic to a subalgebra" — and two one-point algebras are isomorphic to the same one-point subalgebra `{Fᵢ}`. **The argument refutes the paper's proof at arity 0, not its theorem.** So `hs` is a defect of ours, not a repair. To settle it: exhibit a genuine arity-0 counterexample to the *printed* conclusion, or drop `hs` and prove `thm26` without it |
| 27 | Theorem 27 | `P` | `thm27` |
| 28 | Lemma 28 | `R` | **refuted at generic `U`** (`not_forall_lemma28`, witness `Flat Empty`), and stays false after adding `[Domain U]` and `[BoundedComplete U]`. **Proved at `U`**: `lemma28AtU`, all nine conjuncts. The blocker is `UniversalForBCD U` |
| 29 | Theorem 29 | `p` | sentence 1 proved (`thm29`). Sentence 2: `Thm29Second` **refuted** — our transcription dropped the paper's word "domain". `Thm29SecondAtDomains`, the true reading, is **open** |
| 30 | Lemma 30 | `R` | universal closure **refuted** (`not_forall_lemma30`). `Lemma30AtV` is **open**, now at arity 3 |

**Result 15 was never missing — the instruments were.** Both the declaration scan
and the docstring grep searched only for `thm|theorem|lem|lemma`, and Gunter &
Scott number **Propositions in the same sequence**. `scripts/numbered-status.sh`
now matches `prop|proposition|cor|corollary` as well; the widening was measured
before it was made, and over results 1–30 it adds exactly one hit and no false
positive.

**Result 2's status is not yet established** and is being checked against the
printed text. Results 4, 5 and 8 carry no numbered declaration either, but are
each quoted in a module docstring — `NormalSubposet.lean`,
`FinitaryProjection.lean`, `Product.lean` — so **a result stated under a
descriptive name is the normal case here**, and a missing number is not evidence
of a missing proof.

**The figure "30 numbered results" is still unverified** against the printed
text. It comes from `PropertiesVsTheorems.md` and no round has checked it.

## What is open, in one table

| # | Item | What it needs |
| -- | ---- | ------------- |
| 1 | `StepFunctionsDecidable` | **restate over `consistentEnum`** — the guard `IsCompactElement (ofPairs Q)` is *not* the boundedness test, kernel-checked. Machinery built. Closes 4 claims |
| 2 | `Theorem7ArrowRecursive` | item 1, then `Primrec` facts for the `Finset (ℕ × ℕ)` coding |
| 3 | `Theorem7StrictRecursive` | item 1, likewise |
| 4 | `Thm29Normal` | the `M(f)` tower refutes Theorem 25's hypothesis; the `η` tower is not a fixed point. Three routes named, one is refuting it outright |
| 5 | `Thm29SecondAtDomains` | item 4 |
| 6 | `Lemma30AtV` | item 4, plus `FpImagesBifinite V` |
| 7 | `Lem30Arrow` | item 6 |
| 8 | `PreservesRecursivePresentation` | proved at `fstOp`/`sndOp`; open at the arrow, where it is equivalent to item 2 |

**Items 2–3 and 5–7 are downstream of 1 and 4.** Only items 1 and 4 are real
work, and item 1 is mechanical.

## Additional theories

Results from other authors, formalized here because the paper's proofs need
them. None is part of Gunter & Scott's 30.

### Jung, *Cartesian Closed Categories of Domains*

| # | Result | Status |
| -- | ----- | ------ |
| 1 | Corollary 1.36 | **proved** — `JungCor136`, not by Jung's route (which goes through Prop. 1.22 and a retraction pair) but by indexing below `cap e` |
| 2 | Theorem 1.37 | **proved at `[Domain D]`** — `R45.Agent5.thm137`. Full generality open |
| 3 | Theorem 1.37 for chains | **proved at `[Domain D]`** — `thm137Chains` |
| 4 | Proposition 1.22 | not needed — the route around it is item 1 |
| 5 | Theorem 2.1, 2.3 | quoted; five printed defects in Jung's write-up recorded |

### Iwamura and Markowsky

| # | Result | Status |
| -- | ----- | ------ |
| 1 | Iwamura's lemma | **proved** — `exists_chain_directed_cover`. **Never in Mathlib** |
| 2 | Markowsky's theorem | **proved** — `hasChainSuprema_iff_hasDirectedSuprema`. **Never in Mathlib** |
| 3 | `HasWellOrderedInfima` | **no producer exists** — five occurrences, all consumers. A complete reduction chain with an empty left end |

### Spreen 2005

| # | Result | Status |
| -- | ----- | ------ |
| 1 | Lemma 5.8 | **proved** — `PropertyM.hasOmegaOpBoundsAbove_pair`. This, not Iwamura, is what closed Jung's 1.37 here |

### Gunter 1987, *Universal Profinite Domains*

| # | Result | Status |
| -- | ----- | ------ |
| 1 | Lemma 24 at `M(A)` | **proved** — `R47.Agent1.lemma24_MPair`. **The first proof anywhere**: Gunter's printed Lemma 24 produces *some* `A⁺` and is not about `M(A)`; the `M(A)` form is a remark with no theorem and no proof |
| 2 | `HasNormalRealizations` at `Ainf` | **refuted** — `not_hasNormalRealizations_Ainf`. The route to `Thm29Normal` is sound but its hypothesis is unsatisfiable at this tower |
| 3 | Proposition 21, Theorems 22 and 25 | used, via the implication `thm29Normal_of_hasNormalRealizations` |

## Defects in the printed paper

**Nine**, recorded in `StatementRecovery.md`. Three suspected tenths were checked
and turned out to be **our** transcription errors, not the paper's:

| # | Suspected | Actually |
| -- | -------- | -------- |
| 1 | Theorem 26 false at arity 0 | refutes the paper's *proof*, not its statement |
| 2 | Theorem 29's second sentence false | our transcription dropped "domain" from "any bifinite domain" |
| 3 | the step-function enumeration | our guard tests compactness where the paper tests boundedness |

## Reproducing

    scripts/counts.sh                     # modules, lines, theorems, sorry
    scripts/numbered-status.sh            # declarations per numbered result
    scripts/a6-env-scan.sh <out>          # then a6-summarize.py for row 11
    scripts/a5-r47-conditional.sh         # row 8, the S+H conditional surface
    scripts/compile.sh -r <round>         # build
