---
round: r0046
from: agent2
to: orchestrator
subject: thm29normal
date: 2026-0809-00:10
started: 2026-0808-23:15
finished: 2026-0809-00:10
related:
  - plans/r0046-plan-from-orchestrator-to-orchestrator-zero-props-zero-false-prose.md
  - reports/r0045-report-from-agent3-to-orchestrator-discharge-thm29.md
---

# r0046 agent2 — `Thm29Normal` (Goal A row 10)

**Status: reduced, not open.** The three questions asked, answered first.

| # | Question | Answer |
| -- | -------- | ------ |
| 1 | Is the missing input now precisely stated? | **Yes** — `R46.Agent2.HasNormalRealizations`, a Lean `def`, and localized to one stage of the tower by `hasNormalRealizations_of_stages` |
| 2 | Is the implication to `Thm29Normal` proved? | **Yes, kernel-checked** — `thm29Normal_of_hasNormalRealizations : HasNormalRealizations Ainf → LemThirty.Thm29Normal`, `[propext, Classical.choice, Quot.sound]`, no added binder |
| 3 | Can it be reconstructed without [Gun87]? | **Yes** — the argument is published in two sources this repository already holds. The plan's premise that it is lost is wrong |

New file `ScottDomains/A2Thm29Universal.lean`, 823 lines, 38 top-level
declarations, namespace `ScottDomains.R46.Agent2`. Package: 1353 jobs, **0
errors, 0 warnings, 0 `sorry`**.

## 1. The plan's premise is wrong, and this is the round's main finding

The plan says of row 10:

> a universal property of `M` among finite posets under normal embedding. …
> That content is [Gun87] — a paper requested from Gunter and never received. We
> do not have it.

[Gun87] — `C. A. Gunter, Sets and the semantics of bounded nondeterminism,
Manuscript, 1987` — is indeed unobtainable. **The mathematics it carries is
not.** `ScottDomains/papers/` holds two independent sources for it:

| # | source | location | what it carries |
| -- | ------ | -------- | --------------- |
| 1 | `papers/Gunter 1987 Universal Profinite Domains.pdf` (Inf. & Comput. **72**, 1–30) | §5, pp. 16–23 | the complete universality argument with proofs |
| 2 | `papers/Gunter 1985 A Universal Domain Technique for Profinite Posets.pdf` | ch. 5, pp. 58–67 | the same, in more detail |

`BifiniteUniversal.lean:47` already cites source 1 — but only for the
*construction*, saying "The construction itself is not lost with the
manuscript" and quoting p. 23. That understates it. The same section carries the
**proof of universality**:

| # | result | page | content |
| -- | ------ | ---: | ------- |
| 1 | Proposition 21 | 18 | `A ◁ B` finite, `A ≠ B` ⟹ the inclusion factors through singleton steps |
| 2 | Theorem 22 (Enumeration) | 19 | a countable Plotkin poset `A` has an enumeration `X₀, X₁, …` with `rt(A) ∪ {Xᵢ ∣ i < n} ◁ A` |
| 3 | Lemma 23 | 19 | a normal type over `B ◁ A` is realized by one new point of a finite `A₁ ▷ A` |
| 4 | Lemma 24 | 20 | for finite `A` there is a finite `A⁺ ▷ A` realizing **every** normal type over **every** `B ◁ A`, normally |
| 5 | Theorem 25 | 21 | a countable Plotkin poset `V` with property 4 is universal: `rt(B) ≅ rt(V)` ⟹ `B ⊴ V` |
| 6 | Corollary 26 | 21 | `V_A = ⋃ₙ Aₙ` with `Aₙ₊₁ = Aₙ⁺` has property 4 |
| 7 | remark | 23 | "an even more explicit way … remarked to the author by Dana Scott": `A⁺` **is** `M(A)` |

Row 7 is the sentence `BifiniteUniversal.lean` already quotes. Read together
with rows 4–6 it says: **`M(A)` is Gunter's `A⁺`, row 4 is exactly the universal
property of `M` that `LemThirty.lean:426` names as missing, and row 5 is exactly
the implication from it to `Thm29Normal`.**

Row 10 is therefore not blocked on an unobtainable manuscript. It is
unformalized work with a published proof in hand.

**Two corrections to the file record, for whoever edits prose next** (I changed
no existing file; only agent1/4/5 are authorized to):

* `BifiniteUniversal.lean:38–45` and `LemThirty.lean:426, 453, 703` should say
  that §7.4's deferral is recoverable from Gunter 1987 §5, not merely that the
  construction is. As written they leave the reader believing the proof is lost.
* The file `papers/Gunter 1985 A Universal Domain Technique for Profinite
  Posets.pdf` is **not** that paper. It is Gunter's CMU dissertation *Profinite
  Solutions for Recursive Domain Equations* (1985), 96 pp., whose chapter 5 is
  "Universal Domains". The filename misdescribes the contents; `PaperInventory.md`
  should be corrected.

## 2. The missing input, stated

`HasNormalRealizations α` (`A2Thm29Universal.lean:256`) is Gunter's Theorem 25
hypothesis:

```lean
def HasNormalRealizations (α : Type) [PartialOrder α] : Prop :=
  ∀ A : Set α, A.Finite → A ◁ (Set.univ : Set α) →
    ∀ (β : Type) [PartialOrder β] (T : Set β), T.Finite → ∀ (g : α → β) (z : β),
      (∀ a ∈ A, ∀ b ∈ A, (g a ≤ g b ↔ a ≤ b)) →
      g '' A ◁ T → insert z (g '' A) ◁ T →
      ∃ y : α, SameTypeOver A g z y ∧ insert y A ◁ (Set.univ : Set α)
```

Two modelling decisions, both recorded in the docstring:

* **Gunter's diagram types are not formalized as syntax.** A *complete* diagram
  type — the only kind the argument realizes — is determined by two
  biconditionals, which is `SameTypeOver`. Gunter's *normal* (p. 19) means
  "realized in some poset `β` with `A ◁ β`", so the witness `(β, T, g, z)` is
  quantified over directly. This is if anything weaker than his statement, since
  a syntactic type need not be complete.
* Three hypotheses beyond Gunter's are carried (`T` finite, `g '' A ◁ T`,
  `insert z (g '' A) ◁ T`). **Each makes the property weaker**, so nothing is
  asked for that Lemma 24 does not deliver.

**The property is not vacuous.** `not_hasNormalRealizations_unit` proves
`¬ HasNormalRealizations Unit` — the type of `true` over `{false}` in `Bool` is
normal and demands a point strictly above, which a one-point poset lacks. A
reduction to a property everything satisfies would be worthless; this one is not.

**Localized to a single stage.** `hasNormalRealizations_of_stages` (line 799)
proves that `HasNormalRealizations Ainf` follows from the same property asked of
the *stages* — realize the type inside some `Stg m` and `A∞` inherits it. That is
Gunter's Corollary 26, and it uses `LemThirty.exists_stage_ge_of_finite` and
`Colimit.isNormalIn_range_incl`, both already in the development. Its hypothesis
is `LemThirty.lean:426`'s sentence verbatim: extend a normal embedding of a
finite normal subposet from one stage to the next. **That is Lemma 24 at
`M(Stg n)`, and it is the whole of what remains.** It is stated as a theorem
hypothesis, not a named `Prop`, so it adds nothing to Goal A's count.

## 3. The implication, proved

```
HasNormalRealizations A∞
  ─ hasFiniteExtensions_of_hasNormalRealizations  (Gunter Prop. 21)
      ⟹ HasFiniteExtensions A∞
  ─ thm29Normal_of_hasFiniteExtensions            (Gunter Thm. 22 + 25)
      ⟹ LemThirty.Thm29Normal
```

`thm29Normal_of_hasNormalRealizations` composes the two.
`thm29SecondAtDomains_of_hasNormalRealizations` then composes with
`LemThirty.thm29SecondAtDomains_of_thm29Normal`.

`LemThirty.Thm29Normal` is applied **exactly as `LemThirty.lean:464` states it** —
same `E`, same `[CompletePartialOrder E] [Domain E]`, same conclusion. **No
instance binder is added and no hypothesis is weakened**; this is a discharge of
the implication, not a "discharged at".

What each step contains:

| # | declaration | Gunter | content |
| -- | ----------- | ------ | ------- |
| 1 | `exists_singleton_step` | Prop. 21 | a maximal point of `B ∖ A` extends `A` normally on both sides. Gunter needs finiteness to turn directedness into a maximum; `IsNormalIn` asks only for directedness, so only `B ∖ A` need be finite |
| 2 | `exists_step`, `hasFiniteExtensions_of_hasNormalRealizations` | Prop. 21 induction | one appeal to the realization property per singleton step, induction on `Set.ncard (T ∖ S)`. The ambient poset never changes, so no auxiliary poset has to be built to witness normality of the type |
| 3 | `cover`, `cover_mono`, `exists_mem_cover` | Thm. 22 | the chain of finite normal subposets exhausting a countable Plotkin order. Crude rather than singleton-stepped, because step 2 already absorbed Prop. 21 |
| 4 | `exists_base` | Thm. 25 base | `rt(B) ≅ rt(V)` discharged: `isRoot_singleton_bot` makes both roots `{⊥}`, so the recursion starts at `⊥ ↦ ⊥` |
| 5 | `stage`, `stage_agree`, `stage_stable` | Thm. 25 recursion | Gunter's `fₙ : Aₙ ≅ Vₙ`, carried as *total* maps `K(E) → A∞` constrained on the `n`-th stage, so the union is an ordinary function |
| 6 | `limitMap`, `thm29Normal_of_hasFiniteExtensions` | Thm. 25 limit | the union map; range normality by `isNormalIn_sUnion` on the `◁`-directed family of stage images |

Both halves of "bifinite **domain**" are spent, in different places:
`IsBifinite E` makes `K(E)` a Plotkin order (supplying the chain), and
`[Domain E]` makes `K(E)` countable (supplying the enumeration the chain runs
along). This is consistent with r0045's `not_thm29NormalWithoutDomain`: the
`[Domain E]` binder is necessary, and now it is visibly *used*.

Gunter's root obstruction (p. 18, "no profinite domain can be a continuous
projection of a profinite domain that has a different root") is why there is no
projection-universal ω-profinite domain at all. `isRoot_singleton_bot` shows it
is vacuous here — every poset in sight has a least element — so the realization
property is Theorem 25's only substantive hypothesis in this development.

## 4. Measurements

* `scripts/compile.sh -r r0046`: 1353 jobs, exit 0, **0 errors, 0 warnings, 0 `sorry`**.
  Log `ScottDomains/logs/compile-20260809-000537.agent2.log`.
* `scripts/axioms.sh` over 15 declarations, including every headline theorem —
  and since `#print axioms` is transitive, that covers all 25 new theorems.
  Every one on `[propext, Classical.choice, Quot.sound]`; `isRoot_singleton_bot`
  on none. **No `sorryAx` anywhere.**
* New file: 823 lines, 38 top-level declarations — 25 theorems, 4 `def … : Prop`
  (`IsRoot`, `SameTypeOver`, `HasNormalRealizations`, `HasFiniteExtensions`), 5
  `noncomputable def`, 1 `structure`, 1 `abbrev`. Of the four `Prop`s, only
  `HasNormalRealizations` and `HasFiniteExtensions` are claim-shaped; `IsRoot`
  and `SameTypeOver` are parameterized predicates used inside statements.
* Commits on `agent2`: `e9b5867`, `c9659fb`. Not pushed, per the rule.

## 5. Effect on Goal A, stated honestly

Row 10 moves from **open** to **reduced**: `Thm29Normal` now has a proved
sufficient condition that is one precisely stated property of `A∞`, itself
reduced to one property of `M` at a single stage, for which a published proof
exists in `papers/`. Rows 5, 8 and 9 inherit the reduction through
`thm29SecondAtDomains_of_hasNormalRealizations` and
`A3Thm29.five_conjuncts_of_thm29Normal`.

**But the detector count will go up, not down, unless it is taught the
difference.** `HasNormalRealizations` and `HasFiniteExtensions` are two new
`def … : Prop` naming statements that nothing in the package proves. If
`a6-env-scan.sh` scores "a `Prop` with no theorem concluding it", Goal A reads
**10 → 12** from this stream alone, while the mathematical situation improved.
This is the same defect agent1 is fixing for rows 1–3 (a refutation produces
`¬ Foo`, not `Foo`), in a third form: **a `Prop` that is reduced to is not a
`Prop` that is open.** Recommendation for the instrument: score a claim as
resolved when a theorem concludes it, refutes it, **or** is a proved implication
into another claim of the list. Under that rule this stream reads 10 → 9 and
`HasNormalRealizations` is the single named residue.

I have not changed `a6-summarize.py` — that is agent1's stream, and coordinating
one rule across two agents mid-round would be worse than reporting it.

## 6. What remains, and what it would cost

One statement: **Gunter's Lemma 24 at `M(A)`** — for a finite poset `A`, every
normal type over every `B ◁ A` is realized by a point of `M(A)` with
`B ∪ {Z} ◁ M(A)`. Sources: Gunter 1987 pp. 19–20 (Lemma 23, Lemma 24) plus the
p. 23 identification of `A⁺` with `M(A)`; and the 1985 dissertation ch. 5.
The exact Lean statement is `hasNormalRealizations_of_stages`'s hypothesis.

Gunter proves Lemma 24 through his abstract `Ãtp` construction (p. 23) and
records the `M(A)` form as a remark without redoing the proof, so a formalization
must either (a) verify the remark — check that `M(A)` realizes every normal type
— or (b) formalize `Ãtp` and the isomorphism. Route (a) is the shorter one and
is the natural next round: `BifiniteUniversal.lean` already has `MPair`, its
repaired order, `eta`, `MSub_isNormalIn` and `isPlotkinOrder_MPair`, so the
missing piece is the map from a normal type over `B ◁ A` to the pair
`(x, u) ∈ M(A)` realizing it — the base `x` and cover `u` are readable off the
type's two halves. I did not attempt it in this round; the round asked for the
statement and the implication, and the implication was the larger job.

## 7. Coordination

Nothing here touches agent3's `PRep` schemes. r0045's agent3 established
`Thm29Normal ⟹ Thm29SecondAtDomains` (kernel-checked) but *not*
`Thm29Normal ⟹ Lemma30AtV`, because a conjunct needs a `PRep` scheme as well as
a retraction pair. That is unchanged: this stream supplies `Thm29Normal`'s
sufficient condition and nothing about the schemes. Row 5 still needs agent3's
three schemes **and** this reduction.

No existing `def` was changed. No prose in another file was edited.
