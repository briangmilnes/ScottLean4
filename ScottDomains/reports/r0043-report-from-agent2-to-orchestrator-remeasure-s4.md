---
round: r0043
from: agent2
to: orchestrator
subject: remeasure-s4
date: 2026-0808-16:44
started: 2026-0808-16:29
finished: 2026-0808-16:44
related:
  - plans/r0043-plan-from-orchestrator-to-orchestrator-remeasure-unstated.md
  - reports/r0040-report-from-agent2-to-orchestrator-property-coverage-s4-lem10.md
  - reports/r0041-report-from-agent2-to-orchestrator-morphism-algebra.md
---

# r0043 — §4 through Lemma 10: the twelve `N` rows, re-measured

**12 of 12 are now `S+P`. `N` count for my range: 12 → 0.**

Every label below was re-derived from the compiled environment, not from r0041's
summary and not from the plan. This is the check on my own r0041 work that the
round asked for, and it is the reason the evidence column quotes kernel output.

## 0. What counts as evidence here, and why it is not the three greps

r0040's rule was "a row stays `N` only after grepping three ways". No row stays
`N`, so that rule is not what carries this report; the symmetric rule is the one
that does, and it is stricter: **`S+P` requires naming the declaration and
confirming it exists.**

Reading a `theorem` out of `Morphism.lean` confirms nothing — r0038 found two
files asserting false things about themselves, and a source file is exactly the
kind of artefact that can assert one thing and elaborate to another. So each
declaration named below was put through a new script,
`scripts/a2-r0043-check.sh`, which emits for each name

    #check @<decl>          -- the elaborated type, every implicit and instance shown
    #print axioms <decl>    -- the proof's axiom dependencies

and runs them through `lake env lean` against the built `.olean`s. Every type in
the tables below is **quoted from that output**, not transcribed from the source.
Every declaration reports exactly `[propext, Classical.choice, Quot.sound]` —
no `sorryAx`, and nothing beyond the three axioms the rest of the development
uses. (`SeparatelyScottContinuous`, `IsBistrict` and
`ScottHom.IsEmbeddingProjectionPair` are `Prop`-valued `def`s and report *no*
axioms at all.)

Three supporting facts were checked separately, because three rows are unreadable
without them:

| # | Fact | Where | Bears on |
| -- | ---- | ----- | -------- |
| 1 | `Combinator.comp g f` is `g ∘ f` — `comp_apply`, `Combinator.lean:115` | `Combinator.lean:111` | rows 15, 20, 30, 33 |
| 2 | `ScottHom.le_def : f ≤ g ↔ ∀ x, f x ≤ g x` — the order on maps is pointwise | `ScottHom.lean:126` | rows 24, 33 |
| 3 | `separatedSumCopair`'s forward map is restriction along the two injections: `coalescedSumCopair.toFun f = (restrictLeft f, restrictRight f)` (`Copair.lean:430`, `:414`, `:421`) and `liftStrictHomIso.toFun = liftRestrict = · ∘ up` (`Lift.lean:124`, `:129`) | — | rows 35, 36 |

Fact 3 is the one a name-only check would have missed. An `≃o` states a universal
property only if its forward map is the diagram's restriction; had it been any
other bijection, its injectivity would say nothing about uniqueness of a
completion. It composes to `h ↦ (h ∘ inl ∘ up, h ∘ inr ∘ up)`, which is §4.4's
diagram.

## 1. The twelve rows

Row numbers are r0040's §5 numbering; printed pages are the paper's folio.

| # | The paper's sentence | p. | r0040 | Now | Declaration and evidence |
| -- | ------------------- | -: | ----- | --- | ------------------------ |
| 9 | `f : D × E → F` is continuous **iff** continuous in each argument individually | 13 | `N` | **`S+P`** | `Morphism.scottContinuous_iff_separately : ∀ {α β γ} [CompletePartialOrder α] [CompletePartialOrder β] [CompletePartialOrder γ] {f : α × β → γ}, ScottContinuous f ↔ Morphism.SeparatelyScottContinuous f`. The right side is the `def` at `Morphism.lean:191`, the conjunction `(∀ e, ScottContinuous fun x => f (x,e)) ∧ (∀ d, ScottContinuous fun y => f (d,y))` — the paper's two conditions and nothing else. Hypotheses are three cpos, exactly the paper's |
| 14 | `id_D × id_E = id_{D×E}` | 14 | `N` | **`S+P`** | `Morphism.prodMap_id : prodMap ScottHom.id ScottHom.id = ScottHom.id`, at two cpos. `prodMap` is the paper's `⟨f ∘ fst, g ∘ snd⟩` and `prodMap_apply : prodMap f g p = (f p.1, g p.2)` holds by `rfl`, so the operator is the paper's, not merely a declaration wearing its name |
| 15 | `(f × g) ∘ (f' × g') = (f ∘ f') × (g ∘ g')` | 14 | `N` | **`S+P`** | `Morphism.prodMap_comp : comp (prodMap f g) (prodMap f' g') = prodMap (comp f f') (comp g g')`, at six cpos. With fact 1, `comp` is composition in the paper's order |
| 20 | the multiary `onᵢ`, `⟨f₁,…,fₙ⟩` and their universal property | 15 | `N` | **`S+P`** | Existence `Morphism.multiProj_comp_multiPair : ∀ n f i, comp (multiProj n i) (multiPair n f) = f i`; uniqueness `Morphism.multiPair_unique : ∀ n f k, (∀ i, comp (multiProj n i) k = f i) → k = multiPair n f`. Over `MultiProd D n` with `multiProd_two : MultiProd D 2 = ((PUnit × D 0) × D 1)` by `rfl`, which pins the recursion to the paper's `×() = I`, `×(D₁,…,Dₙ) = ×(D₁,…,Dₙ₋₁) × Dₙ` |
| 23 | `smash` is a **surjection** | 17 | `N` | **`S+P`** | `Morphism.smashPair_surjective : Function.Surjective Isomorphism.smashPair`. `Isomorphism.smashPair : α × β → Smash α β` (`StrictCurry.lean:134`) is the paper's `smash` — it collapses a pair with a `⊥` coordinate to the adjoined bottom — and is Scott continuous by `scottContinuous_smashPair`, `:158` |
| 24 | `smash` is a projection whose corresponding embedding is `unsmash` | 18 | `N` | **`S+P`** (qualified, §2) | `Morphism.isProjectionEmbeddingPair_smash : (∀ z : Smash α β, smashPair (smashVal z) = z) ∧ (∀ p : α × β, smashVal (smashPair p) ≤ p)`. That conjunction is `ScottHom.IsEmbeddingProjectionPair` (`Projection.lean:44`, `(∀ x, f (g x) = x) ∧ ∀ y, g (f y) ≤ y`) at embedding `g := unsmash`, projection `f := smash`, unbundled |
| 25 | bistrict continuous `f` ⟹ `f ∘ unsmash` is the **unique** strict continuous `g` with `g ∘ smash = f` | 18 | `N` | **`S+P`** | `Morphism.IsBistrict f := ∀ p, p.1 = ⊥ ∨ p.2 = ⊥ → f p = ⊥` (`:305`) is separate strictness; `bistrictFactor f hf` is `fun z => f (smashVal z)`, typed `StrictHom (Smash α β) γ`; `bistrictFactor_comp_smash : ↑(bistrictFactor f hf) (smashPair p) = f p`; `bistrictFactor_unique : ∀ g : StrictHom (Smash α β) γ, (∀ p, ↑g (smashPair p) = f p) → g = bistrictFactor f hf`. Strictness of the completion sits in the type, so the uniqueness quantifier ranges over exactly the paper's candidates |
| 26 | `f ⊗ g = smash ∘ (f × g) ∘ unsmash` is the unique strict continuous map completing the square | 18 | `N` | **`S+P`** | `Morphism.smashMap (f g : StrictHom …) : StrictHom (Smash α₁ α₂) (Smash β₁ β₂)`, defined as `bistrictFactor (smashProdMap f g) …` where `smashProdMap f g = smash ∘ (f × g)` (`:363`) — so the definition unfolds to the paper's formula. `smashMap_comp_smash : ↑(smashMap f g) (smashPair p) = smashPair (↑f p.1, ↑g p.2)` is the square; `smashMap_unique` is uniqueness among `StrictHom`s. r0040 recorded this formula as recited in a `CombinatorRep.lean` docstring and never under the kernel; it is now under the kernel |
| 30 | multiary `[f₁,…,fₙ]` and its universal property | 19 | `N` | **`S+P`** | `Morphism.multiCopair_comp_multiIn : ∀ n f i, strictComp (multiCopair n f) (multiIn n i) = f i`; `Morphism.multiCopair_unique : ∀ n f k, (∀ i, strictComp k (multiIn n i) = f i) → k = multiCopair n f`, over `MultiSum D n` with `multiSum_succ : MultiSum D (n+1) = CoalescedSum (MultiSum D n) (D n)` by `rfl` |
| 33 | `up ∘ down ⊒ id_{D⊥}` | 20 | `N` | **`S+P`** | `Morphism.up_comp_down_ge : ScottHom.id ≤ comp up down`. With fact 2 that is `∀ z, z ≤ up (down z)`, the paper's `⊒`. `down` is the paper's **total** `down` (`down_coe : down ↑a = a`, `down_bot : down ⊥ = ⊥`), not Mathlib's partial `WithBot.unbot`, which r0040 recorded as not being it. `not_up_comp_down_le` additionally refutes `⊑` at `D = I`, so the direction is content and not notation |
| 35 | for `D + E`: `h = [f†, g†]` is the unique strict continuous map completing the diagram | 21 | `N` | **`S+P`** | `ClosureProperties.separatedSumCopair : StrictHom (SeparatedSum α β) γ ≃o ScottHom α γ × ScottHom β γ` (`SeparatedSum.lean:202`). By fact 3 the forward map is `h ↦ (h ∘ inl ∘ up, h ∘ inr ∘ up)`, so bijectivity is existence-and-uniqueness of the strict completion; `Morphism.separatedSumCopair_symm_apply : separatedSumCopair.symm (f,g) = Isomorphism.copair (liftExtend f) (liftExtend g)` holds by `rfl` and identifies the completion as literally `[f†, g†]`. Not my work — introduced by the orchestrator in `48080f3`, before r0041 |
| 36 | `h` may **not** be the only *continuous* map completing that diagram | 21 | `N` | **`S+P`** | `Morphism.exists_ne_continuous_completions : ∃ h₁ h₂ : ScottHom (SeparatedSum PUnit PUnit) Prop, CompletesSepSum (const True) (const True) h₁ ∧ CompletesSepSum (const True) (const True) h₂ ∧ h₁ ≠ h₂`. `CompletesSepSum f g h := (∀ x, h (sumInlFun ↑x) = f x) ∧ (∀ y, h (sumInrFun ↑y) = g y)` — the same two equations as `separatedSumCopair`'s forward map by fact 3, but quantified over a `ScottHom`, i.e. an arbitrary **continuous** completion. `h₁` is the strict completion (`completesSepSum_separatedSumCopair`), `h₂` is `const True`; they differ at the adjoined bottom, which lies in the image of neither injection |

## 2. The one qualification, on row 24

`isProjectionEmbeddingPair_smash` states the two equations for the **unbundled**
functions `Isomorphism.smashPair` and `Isomorphism.smashVal`, not for bundled
`ScottHom`s, so it does not literally instantiate
`ScottHom.IsEmbeddingProjectionPair`. Continuity of both maps is proved, but in
two other declarations: `Isomorphism.scottContinuous_smashPair`
(`StrictCurry.lean:158`) and `Isomorphism.scottContinuous_smashVal` (`:93`).

The property is therefore stated across three declarations rather than one. I
label it `S+P` and name all three, which is the same ruling r0040 gave Lemma 10's
seven conjuncts (bounded-completeness half and `Domain` half in different
declarations) and the same one `LemThirty.lean:299` records for its own
`IsEmbeddingProjectionPair` with "the conjunction unfolded". A reader wanting one
declaration would bundle both maps and apply the existing predicate; that is a
presentation change, not a missing statement.

## 3. Two corrections to the record

**3.1 The launch brief's premise about row 36 is wrong, and it matters for
attribution.** The brief states that "`h` may not be the only *continuous*
completion" was not among r0041's eleven and should be checked specially. It
*was* among them — r0041's table row 11, `exists_ne_continuous_completions`. The
row that was **not** in the eleven is **row 35**, the separated sum's universal
property, closed by the orchestrator's own `ClosureProperties.separatedSumCopair`
in commit `48080f3` (whose message says "close one r0040 gap"; that build reports
1229 jobs, one fewer than r0041's 1230). Both rows were re-checked from the
kernel regardless, and both are `S+P`. The consequence for consolidation is only
one of credit: of my twelve, eleven were closed by agent2 in r0041 and one by the
orchestrator before it.

**3.2 The five functorial actions r0040 recorded as absent all exist now**, and
were checked the same way even though they are definitions and so outside the
54-property count (`PropertiesVsTheorems.md` §1 excludes them). r0040's
definitions-table rows 4, 12, 16, 22 and 24:

| # | Paper | Declaration | Type, from `#check` |
| -- | ----- | ----------- | ------------------- |
| 1 | `f × g` | `Morphism.prodMap` | `ScottHom α₁ β₁ → ScottHom α₂ β₂ → ScottHom (α₁ × α₂) (β₁ × β₂)` |
| 2 | `f ⊗ g` | `Morphism.smashMap` | `StrictHom α₁ β₁ → StrictHom α₂ β₂ → StrictHom (Smash α₁ α₂) (Smash β₁ β₂)` |
| 3 | `f ⊕ g` | `Morphism.coalSumMap` | `StrictHom α₁ β₁ → StrictHom α₂ β₂ → StrictHom (CoalescedSum α₁ α₂) (CoalescedSum β₁ β₂)` |
| 4 | `f⊥` | `Morphism.liftMap` | `ScottHom α β → StrictHom (WithBot α) (WithBot β)` |
| 5 | `f + g` | `Morphism.sepSumMap` | `ScottHom α₁ β₁ → ScottHom α₂ β₂ → StrictHom (SeparatedSum α₁ α₂) (SeparatedSum β₁ β₂)` |

All five are stated in general, at arbitrary cpos — not at `ScottHom U U`, which
was r0040's finding about every prior version. Rows 2 and 3 carry the paper's
strictness hypothesis; row 5 does not need it, because `f⊥` is strict whatever
`f` is.

## 4. Regressions

**None observed.** I did not re-survey the 42 non-`N` rows, per the plan. The two
`S≠` rows (Lemma 9.3 and 9.5) and the 15 `S+P` numbered conjuncts were not
re-checked and are not claimed here either way.

## 5. Counts, and confirmation that this round changed nothing

`scripts/compile.sh -r r0043`, log
`ScottDomains/logs/compile-20260808-163451.agent2.log`:

| # | Measure | r0043 head of `agent2` | Measured now |
| -- | ------- | ---------------------: | -----------: |
| 1 | `lake build` jobs | 1339 | **1339** |
| 2 | exit code | 0 | **0** |
| 3 | `sorry` | 0 | **0** |
| 4 | non-`sorry` warnings | 0 | **0** |
| 5 | lake errors | 0 | **0** |
| 6 | modules | 100 | **100** |
| 7 | lines | 37 300 | **37 300** |
| 8 | theorem-ish declarations | 1773 | **1773** |
| 9 | numbered results | 25 of 29 | unchanged — no `.lean` file was opened for writing |

No `.lean` file was edited. The round adds two files: this report and
`scripts/a2-r0043-check.sh`.

## 6. Result

| # | Label | r0040 | r0043 |
| -- | ----- | ----: | ----: |
| 1 | `S+P` | 0 | **12** |
| 2 | `S+H` | 0 | 0 |
| 3 | `S≠` | 0 | 0 |
| 4 | `P` | 0 | 0 |
| 5 | `N` | 12 | **0** |

**§4-through-Lemma-10 contributes 0 to the remaining unstated count.** My range's
whole property total is unchanged at 54: 15 `S+P` numbered conjuncts, 2 `S≠`,
and now 37 `S+P` prose claims — 40 as of r0040 plus the twelve here, which is 52
`S+P` in all.

## 7. Reproduction

    scripts/compile.sh -r r0043
    scripts/counts.sh
    scripts/a2-r0043-check.sh -i ScottDomains.Projection -i ScottDomains.Morphism \
      ScottDomains.Morphism.scottContinuous_iff_separately \
      ScottDomains.Morphism.prodMap_id ScottDomains.Morphism.prodMap_comp \
      ScottDomains.Morphism.multiProj_comp_multiPair ScottDomains.Morphism.multiPair_unique \
      ScottDomains.Morphism.smashPair_surjective \
      ScottDomains.Morphism.isProjectionEmbeddingPair_smash \
      ScottDomains.Morphism.bistrictFactor_comp_smash ScottDomains.Morphism.bistrictFactor_unique \
      ScottDomains.Morphism.smashMap_comp_smash ScottDomains.Morphism.smashMap_unique \
      ScottDomains.Morphism.multiCopair_comp_multiIn ScottDomains.Morphism.multiCopair_unique \
      ScottDomains.Morphism.up_comp_down_ge ScottDomains.Morphism.not_up_comp_down_le \
      ScottDomains.ClosureProperties.separatedSumCopair \
      ScottDomains.Morphism.separatedSumCopair_symm_apply \
      ScottDomains.Morphism.exists_ne_continuous_completions
