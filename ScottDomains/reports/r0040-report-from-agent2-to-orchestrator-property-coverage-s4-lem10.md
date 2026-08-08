---
round: r0040
from: agent2
to: orchestrator
subject: property-coverage-s4-lem10
date: 2026-0808-11:52
started: 2026-0808-11:34
finished: 2026-0808-11:52
related:
  - plans/r0040-plan-from-orchestrator-to-orchestrator-property-coverage.md
  - docs/PropertiesVsTheorems.md
  - docs/PaperInventory.md
---

# r0040 — §4.1 through Lemma 10: does every property have a Lean statement?

Range: Gunter & Scott, *Semantic Domains*, **§4 in its entirety** — printed pages
12–22, physical PDF pages 13–23. §4.5 ends at Lemma 10, so "§4.1 through §4.5 up
to and including Lemma 10" is the whole of section 4.

## 0. Result

| # | Label | Numbered conjuncts | Prose claims | Total |
| -- | ----- | -----------------: | -----------: | ----: |
| 1 | `S+P` | 15 | 25 | **40** |
| 2 | `S+H` | 0 | 0 | **0** |
| 3 | `S≠`  | 2  | 0  | **2** |
| 4 | `P`   | 0  | 0  | **0** |
| 5 | `N`   | 0  | 12 | **12** |
| — | total | 17 | 37 | **54** |

**Every one of the 17 numbered conjuncts has a Lean statement.** All twelve `N`
rows are unnumbered prose claims, and eleven of the twelve are the *universal
properties and functorial actions* of §4.1, §4.3 and §4.4 — the equational
apparatus the paper builds its "system of equational reasoning about continuous
functions" on. The development has every **object** the section defines and every
**closure property** it asserts; what it does not have is the **morphism-level
algebra**: no `f × g`, no `f ⊗ g`, no `f ⊕ g`, no `f + g`, and no multiary
notation anywhere.

The `sorry` count contributes nothing here: **zero** of my 54 properties is
`S+H`. A hole would have been visible to `lake build`; the twelve `N` rows are
exactly what a `sorry` count cannot see.

## 1. Method

The operator glyphs were read from **rendered pages**, not `pdftotext`:
`scripts/pdf-render.sh "Gunter Scott 1990.pdf" 22` and `… 23` at 200 dpi, read as
images. That was necessary: the layout extraction of physical page 22 prints
Lemma 8.1 as `D  E ∼ = E  D` (the `×` vanishes) and Lemma 9.3's `⇸` as `!`, so
Lemma 9's operator list is unreadable from text alone. The rendered pages are
legible and gave the printed text below with no ambiguity.

The property list was written **before** any Lean file was opened, from the
extracted text of physical pages 13–19 and the rendered images of 22–23.
Declaration names were then found with `scripts/lean-decls.py --list` and `grep`.

## 2. The 17 numbered conjuncts

### Lemma 8 (printed p. 21) — `Let D, E and F be cpo's, then`

| # | The paper's sentence | Label | Declaration | Evidence |
| -- | ------------------- | ----- | ----------- | -------- |
| 1 | `D × E ≅ E × D` | `S+P` | `ScottDomains.prodComm` | `Product.lean:74`, a term of `α × β ≃o β × α` at `[CompletePartialOrder α] [CompletePartialOrder β]` |
| 2 | `(D × E) × F ≅ D × (E × F)` | `S+P` | `ScottDomains.prodAssoc` | `Product.lean:82` |
| 3 | `D → (E × F) ≅ (D → E) × (D → F)` | `S+P` | `ScottDomains.scottHomProd` | `Product.lean:104` |
| 4 | `D → (E → F) ≅ (D × E) → F` | `S+P` | `ScottDomains.scottHomCurry` | `Currying.lean:135`, on `ScottHom.curry`/`ScottHom.uncurry` |

All four are `def`s producing `≃o`, not `theorem`s. That is not a weakening: an
inhabitant of `α × β ≃o β × α` is a kernel-checked proof of the isomorphism, and
the hypothesis class is exactly the paper's (`CompletePartialOrder`, i.e. cpo).
`≃o` rather than a bundled continuous isomorphism is right and `Product.lean:31–36`
argues why: an order isomorphism between cpos preserves directed suprema, because
least upper bounds are defined by the order.

### Lemma 9 (printed pp. 21–22) — `Let D, E and F be cpo's, then`

The printed text, decoded from the rendered pages:

> 1. `D ⊗ E ≅ E ⊗ D`
> 2. `(D ⊗ E) ⊗ F ≅ D ⊗ (E ⊗ F)`
> 3. `(E ⊕ F) ⇸ D ≅ (E ⇸ D) × (E ⇸ F)`
> 4. `D ⇸ (E ⇸ F) ≅ (D ⊗ E) ⇸ F`
> 5. `D ⊗ (E ⊕ F) ≅ (D ⊗ E) ⊕ (D ⊗ E)`
> 6. `D⊥ ⇸ E ≅ D → E`

Items 3 and 5 are as printed on page 21 of the rendered image; I confirm the two
misprints independently of the development's own claim. In item 3 the second
factor is `(E ⇸ F)`, which does not mention `D` at all; in item 5 the second
summand is `(D ⊗ E)`, and `F` never appears on the right.

| # | The paper's sentence | Label | Declaration | Evidence |
| -- | ------------------- | ----- | ----------- | -------- |
| 5 | `D ⊗ E ≅ E ⊗ D` | `S+P` | `Recovered.lem9_1`, via `Isomorphism.smashComm` | `Skeleton/Recovered.lean:110`; `Isomorphism/Smash.lean:54` |
| 6 | `(D ⊗ E) ⊗ F ≅ D ⊗ (E ⊗ F)` | `S+P` | `Recovered.lem9_2`, via `Isomorphism.smashAssoc` | `Recovered.lean:117`; `Smash.lean:109` |
| 7 | `(E ⊕ F) ⇸ D ≅ (E ⇸ D) × (E ⇸ F)` | **`S≠`** | `Recovered.lem9_3`, via `Isomorphism.coalescedSumCopair`; refuted by `Isomorphism.lem9_3_printed_false` | see §3 |
| 8 | `D ⇸ (E ⇸ F) ≅ (D ⊗ E) ⇸ F` | `S+P` | `Recovered.lem9_4`, via `Isomorphism.smashCurry` | `Recovered.lean:145`; `Isomorphism/StrictCurry.lean:271` |
| 9 | `D ⊗ (E ⊕ F) ≅ (D ⊗ E) ⊕ (D ⊗ E)` | **`S≠`** | `Recovered.lem9_5`, via `Isomorphism.smashDistribCoalescedSum`; refuted by `Isomorphism.lem9_5_printed_false` | see §3 |
| 10 | `D⊥ ⇸ E ≅ D → E` | `S+P` | `Recovered.lem9_6`, via `Isomorphism.liftStrictHomIso` | `Recovered.lean:170`; `Isomorphism/Lift.lean:128` |

The four `S+P` rows carry the paper's hypotheses and no more:
`[CompletePartialOrder α] [CompletePartialOrder β] [CompletePartialOrder γ]`
(`Recovered.lean:102`). No `Domain`, no `BoundedComplete`.

### Lemma 10 (printed p. 22)

> **Lemma 10** If `D` and `E` are bounded complete domains then so are the cpo's
> `D → E`, `D ⇸ E`, `D × E`, `D ⊗ E`, `D + E`, `D ⊕ E`, `D⊥`.

Read from the rendered page 23 image. **Seven operators**, in that printed order.

`ClosureProperties.lemma10` (`ClosureProperties.lean:78`) is a **seven-fold
conjunction in exactly the printed order** — `ScottHom`, `StrictHom`, `×`,
`Smash`, `SeparatedSum`, `CoalescedSum`, `WithBot` — so the conjunct count is
kernel-checked, not read off a docstring. Its hypotheses are
`[Domain α] [BoundedComplete α] [Domain β] [BoundedComplete β]`, which is the
paper's "bounded complete domains" and nothing more.

One qualification applies to all seven and is stated once here rather than seven
times. The paper's "**so are**" means "so are bounded complete *domains*";
`lemma10`'s conjuncts conclude only `BoundedComplete X`. The `Domain X` half is
proved for each operator, but in a different declaration, listed in the last
column. The property is therefore stated, split across two declarations — I label
it `S+P` and name both.

| # | Operator | Label | Bounded-completeness half | Domain half |
| -- | -------- | ----- | ------------------------- | ----------- |
| 11 | `D → E`  | `S+P` | `ScottHom`'s `BoundedComplete` instance | `instance : Domain (ScottHom α β)`, `FunctionSpaceCountable.lean:122`; both together as `isBoundedCompleteDomain_scottHom`, `:134` |
| 12 | `D ⇸ E`  | `S+P` | `lem10_strict`, `Skeleton/Lemma10.lean:218` | `PRepFun.strictHomDomain`, `PRepFun.lean:450` |
| 13 | `D × E`  | `S+P` | `lem10_prod`, `Skeleton/Lemma10.lean:75` | `Powerdomain.Universal.domain_prod`, `:240` |
| 14 | `D ⊗ E`  | `S+P` | `lem10_smash`, `Skeleton/Lemma10.lean:112` | `PRepFun.smashDomain`, `PRepFun.lean:992` |
| 15 | `D + E`  | `S+P` | `lem10_separated`, `ClosureProperties/SeparatedSum.lean:150` | `domain_coalescedSum` at `D⊥`, `E⊥`, through `liftDomain` |
| 16 | `D ⊕ E`  | `S+P` | `lem10_sum`, `Skeleton/Sum.lean` | `PRepSum.domain_coalescedSum`, `:390` |
| 17 | `D⊥`     | `S+P` | `lem10_lift`, `Skeleton/Lemma10.lean:180` | `ClosureProperties.liftDomain` (instance), `SeparatedSum.lean:126` |

Row 11 is the one conjunct stated in the paper's full form by a single
declaration: `isBoundedCompleteDomain_scottHom : Domain (ScottHom α β) ∧
BoundedComplete (ScottHom α β)`.

**Docstring defect, already on record and re-confirmed.** `Skeleton/Lemma10.lean:12–13`
quotes Lemma 10 with **six** operators — `D ⊕ E` is missing. `ClosureProperties.lean:12–13`
quotes all seven. The six-wide quotation is the `pdftotext` glyph loss that
`PaperInventory.md` row 4.5 already records; I confirm the module docstring still
carries it. No `.lean` file was edited this round, so it stands.

## 3. Ruling on Lemma 9's items 3 and 5

**A refutation does not state the claim; it decides it. The correct label is
`S≠`, and it is the strongest `S≠` in the audit.**

The argument, in three steps.

**Step 1 — what "stated" has to mean.** A declaration states a proposition `P`
when some declaration's *type* is `P`, up to instantiating that declaration's own
arguments. Item 3, read literally off the page, is

    P₃ ≔ ∀ D E F : cpo, Nonempty ((E ⊕ F) ⇸ D ≃o (E ⇸ D) × (E ⇸ F)).

`lem9_3_printed_false`'s type (`Isomorphism/Counterexample.lean:100`) is

    ¬ Nonempty (StrictHom (CoalescedSum Prop Prop) PUnit ≃o
                StrictHom Prop PUnit × StrictHom Prop Prop)

which is neither `P₃` nor `¬P₃`. It is `¬P₃` **at a witness** — it entails `¬P₃`
(whose literal form is `∃ D E F, ¬Nonempty …`), and entailment is not statement.
So `P₃` is not stated, and `S+P` is wrong.

**Step 2 — why `N` is also wrong.** `N` reports the development as *silent*. On
item 3 it is the opposite of silent: item 3 is the **only** conjunct in my whole
range whose truth value the kernel has decided. Labelling it `N` would put it in
the same bucket as `up ∘ down ⊒ id`, about which the development says nothing at
all. That destroys the measurement.

**Step 3 — `S≠` is what `S≠` is for.** The round's own definition of `S≠` is
"stated, but not the paper's statement — different hypotheses, weaker conclusion,
or **a repaired form**. Name the declaration and say exactly how it differs."
`Recovered.lem9_3` is the repaired form; the difference is one sub-term. The
difference is not an artefact of formalization — it is *proved necessary*.

Both rows in the legible form a reader with neither the paper nor the development
can check:

| # | Item | Printed | Stated in Lean | Difference | Refutation of the printed form |
| -- | --- | ------- | -------------- | ---------- | ------------------------------ |
| 7 | 9.3 | `(E ⊕ F) ⇸ D ≅ (E ⇸ D) × (E ⇸ F)` | `(E ⊕ F) ⇸ D ≅ (E ⇸ D) × (F ⇸ D)` — `Recovered.lem9_3`, `Recovered.lean:135` | second factor `E ⇸ F` → `F ⇸ D`; the printed right side does not mention `D` | `lem9_3_printed_false` at `D = PUnit`, `E = F = Prop`: left side is a subsingleton (every map into `PUnit` is the same map), printed right side has ≥ 2 elements because `Prop ⇸ Prop` holds both the constant-`⊥` map and `propId` |
| 9 | 9.5 | `D ⊗ (E ⊕ F) ≅ (D ⊗ E) ⊕ (D ⊗ E)` | `D ⊗ (E ⊕ F) ≅ (D ⊗ E) ⊕ (D ⊗ F)` — `Recovered.lem9_5`, `Recovered.lean:159` | second summand `D ⊗ E` → `D ⊗ F`; `F` never appears on the printed right side | `lem9_5_printed_false` at `D = Prop`, `E = PUnit`, `F = Prop`: printed right side is a one-element cpo (`Prop ⊗ PUnit` is a singleton, and `⊕` deletes both summands' bottoms), left side has two |

Two properties of these witnesses are worth recording because they are what makes
the ruling safe rather than convenient.

1. **Each witness is chosen so the corrected law survives it.** For 9.3 the
   corrected right side is `StrictHom Prop PUnit × StrictHom Prop PUnit`, a
   subsingleton, matching the left. For 9.5 the corrected right side gains its
   second element from `Prop ⊗ Prop`. So the separation is specific to the
   misprint and is not an accident of a degenerate carrier. Without this the
   witnesses would refute the corrected laws too and prove nothing about the
   misprint.
2. **The separating invariant is the coarsest one an order isomorphism must
   preserve** — one element versus more than one, discharged through
   `Equiv.subsingleton`. No cardinality arithmetic, no `Fintype` instances. The
   docstrings in `Recovered.lean` cite a different, larger witness
   (`D = E = Prop`, `F = Prop × Prop`, cardinalities 10 / 8 / 10 and 5 / 3 / 5)
   as the *motivation*; the kernel-checked witnesses in `Counterexample.lean` are
   the `PUnit`-based ones. Both are recorded, and only the second is evidence.

**Consistency across streams.** This is the ruling the plan already reaches for
agent4's Theorem 16: "Thm 16's second conjunct is **refuted**, and `thm16_positive`
states a repaired form — that is `S≠` plus a refutation, not `S+P`." Lemma 9.3
and 9.5 are the same shape and get the same label. If the orchestrator prefers a
distinct label for "refuted plus repaired", it should be introduced once and
applied to all three rows at consolidation time; I have not invented one.

**Consequence for the totals.** Lemma 9 counts 6 conjuncts, of which 4 are `S+P`
and 2 are `S≠`. It is **not** correct to say Lemma 9 is 6 of 6 proved: two of the
six printed conjuncts are false, and what is proved is their repair.

## 4. Definitions §4.1–§4.4

`PropertiesVsTheorems.md` §1 excludes definitions from the property count
("objects rather than assertions"), so these are **not** in the §0 totals. The
plan asked for them, and the pattern in this table is what explains the twelve
`N` rows in §5.

| # | § | Definition | Present? | Declaration |
| -- | - | ---------- | -------- | ----------- |
| 1 | 4.1 | product `D × E`, coordinatewise order | yes | Mathlib `Prod` + `instance : CompletePartialOrder (α × β)`, `Product.lean:60` |
| 2 | 4.1 | `fst`, `snd` | yes | Mathlib `Prod.fst`/`Prod.snd` |
| 3 | 4.1 | pairing `⟨f, g⟩` | yes (twice) | `ScottHom.pair`, `Product.lean:98`; `Combinator.prodMkHom`, `Combinator.lean:119` — **duplicate definitions of the same map** |
| 4 | 4.1 | `f × g` on continuous maps | **no** | only `Powerdomain.Universal.prodMap`, `:261`, at `ScottHom U U` |
| 5 | 4.1 | `apply : ((E → F) × E) → F` | not named | obtainable as `ScottHom.uncurry (ScottHom.id)` |
| 6 | 4.1 | `curry` | yes | `ScottHom.curry`, `Currying.lean:68` |
| 7 | 4.1 | multiary `(D₁,…,Dₙ)`, `onᵢ`, `⟨f₁,…,fₙ⟩` | **no** | — |
| 8 | 4.2 | Church's λ-notation | yes | Lean's own `fun`, bundled by `ScottHom`; continuity preservation is `ScottHom.curry` |
| 9 | 4.3 | smash product `D ⊗ E` | yes | `ScottDomains.Smash` + `smashCpo`, `Smash.lean:162` |
| 10 | 4.3 | `smash : D × E → D ⊗ E` | yes (twice) | `smashPair`, `Isomorphism/StrictCurry.lean:134`; `smashCollapse`, `PRepFun.lean:695` — **duplicate** |
| 11 | 4.3 | `unsmash : D ⊗ E → D × E` | yes (twice) | `smashVal`, `StrictCurry.lean:88`; `smashEmbed`, `PRepFun.lean:684` — **duplicate** |
| 12 | 4.3 | `f ⊗ g = smash ∘ (f × g) ∘ unsmash` | **no** — `P` | the formula is recited in a docstring at `CombinatorRep.lean:506–507` and never put under the kernel; `PRepFun.smashMap`, `:1028`, is this construction only at `ScottHom U U` |
| 13 | 4.4 | coalesced sum `D ⊕ E` | yes | `CoalescedSum` + `sumCpo`, `CoalescedSum.lean:411` |
| 14 | 4.4 | `inl`, `inr` | yes | `sumInl`/`sumInr`, `Isomorphism/Copair.lean:210`/`214` |
| 15 | 4.4 | `[f, g]` | yes | `copair`, `Copair.lean:410` |
| 16 | 4.4 | `f ⊕ g` | **no** | only `PRepSum.coalSumMap`, `:566`, at `ScottHom U U` with strictness hypotheses |
| 17 | 4.4 | multiary `(D₁,…,Dₙ)`, `inᵢ = inr ∘ inlⁿ⁻ⁱ` | **no** | — |
| 18 | 4.4 | lift `D⊥` | yes | `WithBot` + `liftCpo`, `Lift.lean:70` |
| 19 | 4.4 | `up : D → D⊥` | yes | Mathlib coercion; continuity `scottContinuous_coe`, `Isomorphism/Lift.lean:48` |
| 20 | 4.4 | `down : D⊥ → D` | not named | equals `liftExtendFun (ScottHom.id)`, `Isomorphism/Lift.lean:64` |
| 21 | 4.4 | `f†` | yes | `liftExtend`, `Isomorphism/Lift.lean:120` |
| 22 | 4.4 | `f⊥ = (up ∘ f)†` | **no** | only `Combinator.liftMap`, `CombinatorRep.lean:385`, at `ScottHom U U` |
| 23 | 4.4 | separated sum `D + E = D⊥ ⊕ E⊥` | yes | `ClosureProperties.SeparatedSum`, an `abbrev`, `SeparatedSum.lean:142` — the paper's definition *is* an equation between cpos, and an `abbrev` is the right rendering |
| 24 | 4.4 | `f + g = f⊥ ⊕ g⊥` | **no** | — |

Rows 4, 12, 16, 22, 24 are the pattern: **every one of the section's five
functorial actions on morphisms is missing in general**, and where a version
exists it is specialized to `U` for §7's representability work, not stated as
§4's operator. Rows 7 and 17 are the two multiary notations, both missing.

Rows 3, 10 and 11 record three pairs of duplicate definitions — the same map
defined twice under different names in different modules, with continuity proved
twice. This is r0038's population-2 finding shape and is reported here as an
incidental observation, not as an audit conclusion.

## 5. The 37 unnumbered prose claims

Page numbers are the **printed** folio.

### §4.1 Products (pp. 12–15)

| # | Claim | p. | Label | Declaration / evidence |
| -- | ----- | -- | ----- | ---------------------- |
| 1 | `L ⊆ D × E` directed ⟹ `fst(L)` directed | 12 | `S+P` | `ScottDomains.directedOn_fst_image`, `Product.lean:47` |
| 2 | … ⟹ `snd(L)` directed | 12 | `S+P` | `ScottDomains.directedOn_snd_image`, `Product.lean:53` |
| 3 | `⊔L = (⊔M, ⊔N)` for cpos | 13 | `S+P` | Mathlib `isLUB_prod` with `Prod.supSet`, instantiated at `Product.lean:64`; the equation itself is `rfl` and appears inline at `Skeleton/Lemma10.lean:78`. Mathlib-supplied, no development declaration |
| 4 | `⊥_{D×E} = (⊥_D, ⊥_E)` | 13 | `S+P` | Mathlib `Prod.instBot`, the `to_dual` of `Prod.instTop`, `Order/BoundedOrder/Basic.lean:423`; consumed at `Product.lean:62`. Definitional |
| 5 | `D × E` is a cpo | 13 | `S+P` | `instance : CompletePartialOrder (α × β)`, `Product.lean:60` |
| 6 | `D`, `E` domains ⟹ `D × E` a domain | 13 | `S+P` | `Powerdomain.Universal.domain_prod`, `:240` |
| 7 | `K(D × E) = K(D) × K(E)` | 13 | `S+P` | `Skeleton.Lemma17.isCompactElement_prod_iff`, `:72`; set form `Powerdomain.Universal.compacts_prod`, `:208` |
| 8 | bounded completeness preserved by `×` | 13 | `S+P` | `lem10_prod`, `Skeleton/Lemma10.lean:75` (also Lemma 10 conjunct 3 — the paper asserts it twice) |
| 9 | `f : D × E → F` continuous **iff** continuous in each argument separately | 13 | **`N`** | see §6 |
| 10 | `fst` is continuous | 13 | `S+P` | Mathlib `ScottContinuous.fst`, `Order/ScottContinuity.lean:182`; consumed at `Product.lean:91` |
| 11 | `snd` is continuous | 13 | `S+P` | Mathlib `ScottContinuous.snd`, `Order/ScottContinuity.lean:186`; consumed at `Product.lean:95` |
| 12 | ∃ continuous `⟨f,g⟩` with `fst ∘ ⟨f,g⟩ = f` and `snd ∘ ⟨f,g⟩ = g` | 13 | `S+P` | `ScottHom.pair`, `Product.lean:98`, with `scottHomProd`'s `right_inv`, `:108` |
| 13 | `⟨fst ∘ h, snd ∘ h⟩ = h` (the uniqueness half) | 13 | `S+P` | `scottHomProd`'s `left_inv`, `Product.lean:107` — literally `(f.fstComp).pair (f.sndComp) = f` |
| 14 | `id_D × id_E = id_{D×E}` | 14 | **`N`** | see §6 |
| 15 | `(f × g) ∘ (f' × g') = (f ∘ f') × (g ∘ g')` | 14 | **`N`** | see §6 |
| 16 | `apply : ((E → F) × E) → F` is continuous | 14 | `S+P` | `ScottHom.uncurry`, `Currying.lean:103`, at `α := ScottHom β γ` and `g := ScottHom.id` (`FinitaryProjectionPoset.lean:82`) — pure instantiation, no further proof. No declaration is named `apply` |
| 17 | `curry(f)` is continuous | 14 | `S+P` | `ScottHom.curry`, `Currying.lean:68` |
| 18 | `curry(f)` is the unique continuous map with `apply ∘ (curry(f) × id) = f` | 14 | `S+P` | `scottHomCurry`'s `right_inv`, `Currying.lean:139` (`uncurry (curry f) = f`); uniqueness from the `≃o` being a bijection |
| 19 | equation (1): `curry(apply ∘ (h × id_E)) = h` | 14 | `S+P` | `scottHomCurry`'s `left_inv`, `Currying.lean:138`. `apply ∘ (h × id_E)` **is** `uncurry h`, so equation (1) is literally `curry (uncurry h) = h` |
| 20 | the multiary `onᵢ` and `⟨f₁,…,fₙ⟩` satisfy a universal property like the binary one | 15 | **`N`** | see §6 |

### §4.2 Church's λ-notation (pp. 15–17)

| # | Claim | p. | Label | Declaration / evidence |
| -- | ----- | -- | ----- | ---------------------- |
| 21 | λ-abstraction preserves continuity, because `curry(f)` is continuous whenever `f` is | 17 | `S+P` | `ScottHom.curry`, `Currying.lean:68`. §4.2 is otherwise expository — it introduces notation and types for variables, and makes exactly this one mathematical assertion |

### §4.3 Smash products (pp. 17–18)

| # | Claim | p. | Label | Declaration / evidence |
| -- | ----- | -- | ----- | ---------------------- |
| 22 | `smash : D × E → D ⊗ E` is continuous | 17 | `S+P` | `scottContinuous_smashPair`, `StrictCurry.lean:158`; and again `scottContinuous_smashCollapse`, `PRepFun.lean:766` |
| 23 | `smash` is a **surjection** | 17 | **`N`** | see §6 |
| 24 | `smash` is a projection whose corresponding embedding is `unsmash` | 18 | **`N`** | see §6 |
| 25 | `f` bistrict continuous ⟹ `g = f ∘ unsmash` is the unique strict continuous map with `g ∘ smash = f` | 18 | **`N`** | see §6 |
| 26 | `f`, `g` strict ⟹ `f ⊗ g = smash ∘ (f × g) ∘ unsmash` is the unique strict continuous map making the square commute | 18 | **`N`** | see §6 |
| 27 | ∃ strict continuous `strict apply`, and for each strict `f` a unique strict `strict curry(f)` making the diagram commute | 18 | `S+P` | `Isomorphism.smashCurry : StrictHom α (StrictHom β γ) ≃o StrictHom (Smash α β) γ`, `StrictCurry.lean:271`. The `≃o` carries both halves: `strict apply` is its forward image of `ScottHom.id`, and the bijection is uniqueness of `strict curry(f)` for each `f`. Neither map is separately named |

### §4.4 Sums and lifts (pp. 18–21)

| # | Claim | p. | Label | Declaration / evidence |
| -- | ----- | -- | ----- | ---------------------- |
| 28 | `inl : D → D ⊕ E` and `inr : E → D ⊕ E` are strict continuous | 19 | `S+P` | `sumInl`/`sumInr` as `StrictHom`s, `Copair.lean:210`/`214`, on `scottContinuous_sumInlFun`/`…InrFun` (`:105`/`:157`) and `sumInlFun_bot`/`…InrFun_bot` (`:73`/`:76`) |
| 29 | `f`, `g` strict continuous ⟹ unique strict continuous `[f,g]` completing the diagram | 19 | `S+P` | `copair`, `Copair.lean:410` (existence); `coalescedSumCopair : StrictHom (D ⊕ E) F ≃o StrictHom D F × StrictHom E F`, `:428` (uniqueness). The docstring at `Copair.lean:22` names exactly this split |
| 30 | one may also define `[f₁,…,fₙ]` and prove a universal property | 19 | **`N`** | see §6 |
| 31 | `D⊥` is a cpo when `D` is | 20 | `S+P` | `liftCpo`, `Lift.lean:70` |
| 32 | `down ∘ up = id_D` | 20 | `S+P` | `liftExtendFun_coe`, `Isomorphism/Lift.lean:69`, at `g := ScottHom.id`: `liftExtendFun id ↑a = a`. Pure instantiation; equivalently `liftStrictHomIso`'s `right_inv` at `id`, `:137`. No declaration names `down` |
| 33 | `up ∘ down ⊒ id_{D⊥}` | 20 | **`N`** | see §6 |
| 34 | for continuous `f : D → E` there is a unique strict continuous `f†` with `f† ∘ up = f` | 20 | `S+P` | `liftExtend`, `Isomorphism/Lift.lean:120` (existence + strictness); `liftStrictHomIso`, `:128` (uniqueness — `liftRestrict` *is* `· ∘ up`, `:124`) |
| 35 | for `D + E`: `h = [f†, g†]` is the unique strict continuous map completing the diagram | 21 | **`N`** | see §6 |
| 36 | `h` may **not** be the only *continuous* map completing that diagram | 21 | **`N`** | see §6 |

### §4.5 preamble (p. 22)

| # | Claim | p. | Label | Declaration / evidence |
| -- | ----- | -- | ----- | ---------------------- |
| 37 | "We remarked already that `D → E` and `D ⇸ E` are bounded complete domains whenever `D` and `E` are" | 22 | `S+P` | `isBoundedCompleteDomain_scottHom`, `FunctionSpaceCountable.lean:134`; `lem10_strict` + `PRepFun.strictHomDomain`. A back-reference — the same content as Lemma 10 conjuncts 1–2, counted once here and once there because the paper asserts it twice |

## 6. The twelve `N` rows, each with its three greps

Every grep below was run over `ScottDomains/ScottDomains/**/*.lean` (the whole
development, `Audit/` included) and returned **zero** matching declarations
unless noted.

| # | Property | Three names greped | What is there instead |
| -- | -------- | ------------------ | --------------------- |
| 9 | `f : D × E → F` continuous **iff** separately continuous in each argument | `ScottContinuous₂`; `scottContinuous_prod_iff`; `SeparatelyContinuous` / `separatelyContinuous` (also `continuous_uncurry_iff`, `scottContinuous_curry_iff`, `scottContinuous_iff`) | No biconditional anywhere. `ScottHom.curryApply`, `Currying.lean:62`, gives the ⟹ direction **in the second argument only**; the corresponding claim for the first argument exists only inside `ScottHom.curry`'s proof script. The ⟸ direction — separate ⟹ joint, which is the content, and the one the paper leaves "as an exercise for the reader" — is nowhere. `ScottHom.uncurry` is **not** it: its hypothesis is `ScottHom α (ScottHom β γ)`, continuity into the function space, which is strictly stronger than separate continuity |
| 14 | `id_D × id_E = id_{D×E}` | `prodMap_id`; `prodMap_comp`; `prodFunctor` (also `Prod.map_id` — 0 hits in the development) | The development defines no `f × g` on continuous maps at all (definitions table row 4). `Powerdomain.Universal.prodMap`, `:261`, is the only morphism-level `×`, exists only at `ScottHom U U`, and carries neither law — only `prodMap_apply`, `:266`. Mathlib states both equations for the **bare-function** operator `Prod.map`, which is a different operator from the paper's `f × g : (D → D') → (E → E') → (D × E → D' × E')` on continuous maps |
| 15 | `(f × g) ∘ (f' × g') = (f ∘ f') × (g ∘ g')` | same three | same |
| 20 | multiary product: `onᵢ`, `⟨f₁,…,fₙ⟩` and their universal property | `multiary`; `nary` / `n-ary`; `Multiary` (also `finProd`, `tupleProd`, `PiProd`, `projIdx`) | Nothing. The development has no `n`-ary product of cpos in any form |
| 23 | `smash` is a surjection | `smashCollapse_surjective`; `Function.Surjective (smash…`; `range_smashCollapse` | Nothing. The only hit for `Surjective` near the smash is `PRepFun.smashRangeMap_surjective`, `:1209`, about `smashRangeMap`, an unrelated §7 map between ranges of finitary projections |
| 24 | `smash` is a projection whose embedding is `unsmash` | `IsEmbeddingProjectionPair` (0 hits in `Smash.lean`, `StrictCurry.lean`, `PRepFun.lean`); `smashCollapse_smashEmbed` / `smashEmbed_smashCollapse`; `smashPair_smashVal` / `smashVal_smashPair` | Neither round-trip equation is stated: not `smash ∘ unsmash = id`, not `unsmash ∘ smash ⊑ id`. `PRepFun.isProjection_smashMap`, `:1050`, is about `smashMap r s`, the §7 conjugating family, not about `smash` |
| 25 | bistrict `f` ⟹ `f ∘ unsmash` is the unique strict continuous `g` with `g ∘ smash = f` | `bistrict`; `Bistrict`; `IsStrict₂` (also `strict₂`, `isStrict_pair`) | Nothing — the development has no predicate for "strict in each argument separately". `Isomorphism.curryStrictInner`, `StrictCurry.lean:241`, builds `f ∘ smash` for a *strict* `f : D ⊗ E ⇸ F`, which is the opposite direction and a different hypothesis |
| 26 | `f ⊗ g` on strict maps is the unique strict continuous map making the square commute | `smashMapStrict`; `tensorMap`; `strictSmashMap` | The defining formula is recited in a docstring at `CombinatorRep.lean:506–507` and never put under the kernel. `PRepFun.smashMap`, `:1028`, is `smash ∘ (r × s) ∘ unsmash` at `ScottHom U U` for **non-strict** `r`, `s`, built for §7; no uniqueness claim accompanies it |
| 30 | multiary `[f₁,…,fₙ]` and its universal property | `multiary`; `nary`; `Multiary` (as row 20) | Nothing |
| 33 | `up ∘ down ⊒ id_{D⊥}` | `up_down` / `down_up`; `le_coe_liftExtendFun`; `WithBot.unbot` used as a total `down` | Nothing. `WithBot.unbot` is a *partial* inverse taking a proof `z ≠ ⊥`, not the paper's total `down`, and no inequality relating `up`, `down` and `id` is stated. Note the paper's inequality here has `⊒`, not `⊑` — it is the one place §4.4 flags a difference from an embedding–projection pair, and it is the one of the pair's two equations that is missing |
| 35 | for `D + E`: `h = [f†, g†]` is the unique strict continuous map completing the diagram | `sepCopair`; `separatedCopair`; `sepSumUniversal` (also `SeparatedSum.*≃o`, `sepInl`/`sepInr`) | Nothing. **This one is one line away**: the property is `coalescedSumCopair` at `β := D⊥`, `γ := E⊥` composed with `liftStrictHomIso` on each factor — `StrictHom (D + E) F ≃o StrictHom D⊥ F × StrictHom E⊥ F ≃o (D → F) × (E → F)`. Both isomorphisms are proved (`Copair.lean:428`, `Lift.lean:128`); their composite is not declared, and it is exactly §4.4's diagram |
| 36 | `h` may **not** be the only *continuous* map completing that diagram | `not the only`; `not unique` / `non-unique`; `nonunique` | Nothing, in code or in any docstring. This is the section's one **negative** claim, and it is the claim that distinguishes `+` from `⊕`: without it the separated sum's universal property reads as a coproduct in the category of *continuous* maps, which it is not. A witness would be cheap — two distinct continuous maps out of `D + E` agreeing on both injections, differing at the adjoined bottom |

## 7. The `P` rows

**None** among the 54 properties. One definition is prose-only, recorded in §4
row 12: `f ⊗ g = smash ∘ (f × g) ∘ unsmash` is asserted in the docstring at
`CombinatorRep.lean:506–507` and never put under the kernel. It is a definition,
not an assertion, so it is not in the §0 totals; it is reported because it is
the same defect shape `PaperInventory.md` row 2f counts three of elsewhere, and
because the same docstring's counterexample is already on that list.

## 8. Re-derived counts against `docs/PropertiesVsTheorems.md` §1

| # | §1 row | Result | §1's count | Mine | Moved? |
| -- | ----- | ------ | ---------: | ---: | ------ |
| 1 | 6 | Lem 8 | 4 | **4** | no |
| 2 | 7 | Lem 9 | 6 | **6** | no |
| 3 | 8 | Lem 10 | 7 | **7** | no |
| — | — | numbered subtotal | 17 | **17** | no |

**No numbered conjunct count moved.** The three counts §1 carries for my range
are correct as printed, re-derived from the rendered pages rather than copied.
Lemma 10's seven were read off the page-23 image, where all seven operators are
legible; the six-wide list in `Skeleton/Lemma10.lean`'s docstring is a `pdftotext`
artefact and not the paper.

**The prose-claim count moves, and it moves a great deal.**
`PaperInventory.md` row 3 carries **13** unnumbered prose claims for the whole
paper, of which r0038 attributed **2** to §4.1 (`fst(L)` and `snd(L)`
directedness). Reading §4 from the PDF gives **37** in §4 alone — 20 in §4.1, 1
in §4.2, 6 in §4.3, 9 in §4.4, 1 in the §4.5 preamble.

That is not a defect in r0038's work. Its brief was §2–§3, and the two claims it
added are two of my 37 (rows 1 and 2), correctly identified. The gap is
structural: **row 3's list was assembled from claims the development happens to
prove, not from claims the paper makes.** Every entry in that 13-row table names
a Lean declaration; a paper claim with no declaration could never enter it. This
round asked the question in the other direction and found twelve.

Recommended consequence for the inventory, for the orchestrator to decide at
consolidation:

1. Row 3's number is a count of *proved* prose claims and should be labelled as
   such, not as a count of the paper's prose claims.
2. The paper-property total cannot stay at 100 once §4 contributes 37 prose
   claims in place of 2. My range alone takes the total from
   17 + 2 = 19 to 17 + 37 = **54**, a rise of 35. The other four streams will
   move it further, and the ratio in `PropertiesVsTheorems.md` §2
   ("1298 / 100 ≈ 13.0 theorems per paper property") falls correspondingly. I do
   not restate the global total here — four streams are still outstanding and a
   partial revision would be worse than none.
3. `PaperInventory.md` row 2e's "≥ 1 result with no Lean statement" is a lower
   bound on **numbered results**. My range adds **0** to it: all 17 numbered
   conjuncts are stated. The twelve `N`s are a different population and want
   their own row.

## 9. Confirmation that this round changed nothing

No `.lean` file was opened for writing. `git status --porcelain` on the worktree
is empty at the start of this report and the only file this round adds is the
report itself. The build, the `sorry` count and the numbered-result count are
therefore identical to the merge point by construction, not by re-measurement.
