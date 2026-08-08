---
round: r0041
from: agent3
to: orchestrator
subject: powerdomain-map
date: 2026-0808-13:30
started: 2026-0808-13:05
finished: 2026-0808-13:30
related:
  - plans/r0041-plan-from-orchestrator-to-orchestrator-close-unstated.md
  - reports/r0040-report-from-agent3-to-orchestrator-property-coverage-thm11-s5.md
  - ScottDomains/PowerdomainMap.lean
  - ScottDomains/PowerdomainCompacts.lean
  - ScottDomains/PowerdomainMapRep.lean
---

# r0041 — the action of a map on a powerdomain, and the compacts verdict

**All three actions landed, proved, with both functor laws. The compacts
question is settled in the negative with a Lean-checked counterexample. Lemma 28
moved: its two open conjuncts are now four named propositions about the functor
instead of two about an object that did not exist.**

Measured: three new modules, 1112 lines, 103 declarations, **0 errors, 0
warnings, 1 `sorry`** — the pre-existing `thm18` at `Skeleton/Section6.lean:196`,
unchanged. Every new headline declaration depends on exactly `[propext,
Classical.choice, Quot.sound]`; none on `sorryAx`.

## 1. What landed

| # | Module | Lines | Decls | Content |
| -- | ------ | ----: | ----: | ------- |
| 1 | `ScottDomains/PowerdomainMap.lean` | 539 | 46 | `f♮`, `f♯`, `f♭` and their laws |
| 2 | `ScottDomains/PowerdomainCompacts.lean` | 317 | 37 | the counterexample to `p(K(D)) ⊆ K(D)` |
| 3 | `ScottDomains/PowerdomainMapRep.lean` | 256 | 20 | Lemma 28's two conjuncts, reduced |

### 1.1 The construction, and why it costs nothing

r0040 row 29 measured §5.3's sentence as `N`. The paper gives the definition in
the sentence itself: *"there is a unique homomorphism `f♮ : D♮ → E♮` … namely
`f♮ = ext({|·|} ∘ f)`. Of course, there are functions `f♯` and `f♭` with similar
definitions."*

That definition needs **nothing new**. `E♮` is itself a continuous algebra
satisfying `T♮` — `ContinuousAlgebra.instIsSemilatticeIdealCompletion`, which is
the paper's own "*each of the algebras `D♮`, `D♯` and `D♭` satisfies `T♮`*" — and
`{|·|} ∘ f : D → E♮` is continuous. So **Theorem 12 applies with the target
powerdomain as its algebra**, and its `ext` *is* `f♮`:

    map f := ext (unitComp f)  :  IdealCompletion A → IdealCompletion B

`PowerdomainMap.map` (`:163`) is that, generic in the presentations `A` of
`Pf(K(D))` and `B` of `Pf(K(E))`, so one definition serves all three
powerdomains. The `∃!` of `thm12` delivers the paper's whole sentence in one
step: `exists_unique_map` (`:222`).

| # | Statement | Declaration | Note |
| -- | --------- | ----------- | ---- |
| 1 | `f♮ = ext({\|·\|} ∘ f)` | `map` | generic in `A`, `B` |
| 2 | `f♮({\|x\|}) = {\|f x\|}` — the naturality square | `map_unit` | |
| 3 | `f♮` is a homomorphism of continuous algebras | `isHom_map` | |
| 4 | `f♮` is Scott continuous | `scottContinuous_map` | |
| 5 | **existence and uniqueness** — the paper's sentence | `exists_unique_map` | `thm12` at `E♮` |
| 6 | **`(id)♮ = id`** | `map_id` | functor law 1 |
| 7 | **`(g ∘ f)♮ = g♮ ∘ f♮`** | `map_comp` | functor law 2 |
| 8 | `f ⊑ g` implies `f♮ ⊑ g♮` | `map_le_map` | local monotonicity |
| 9 | `p` a projection implies `p♮` a projection | `isProjection_map` | from 6, 7, 8 |

Rows 6 and 7 are uniqueness arguments: the candidate is shown to be a
homomorphism completing the same square, and `exists_unique_map` identifies it
with `map`. The two supporting facts about `IsHom` — that the identity is one and
that composites are — did not exist (`ContinuousAlgebra.lean` produces a single
homomorphism and never composes two); they are `isHom_id` and `isHom_comp`.

Each of the three powerdomains then instantiates the generic development by
discharging one hypothesis, `Monotone (foldGen ({|·|} ∘ f))`, exactly as
Theorem 12 does:

| # | Powerdomain | discharge | theory spent | names |
| -- | ----------- | --------- | ------------ | ----- |
| 1 | `D♭` | `fold_le_fold_of_hoare` | `T♭` at `E♭`, `instIsLowerHoare` | `hoare`, `thm_map_hoare`, `hoare_id`, `hoare_comp`, `isProjection_hoare` |
| 2 | `D♯` | `fold_le_fold_of_smyth` | `T♯` at `E♯`, `instIsUpperSmyth` | `smyth`, `thm_map_smyth`, `smyth_id`, `smyth_comp`, `isProjection_smyth` |
| 3 | `D♮` | `fold_le_fold_of_convex` | `T♮` alone | `plotkin`, `thm_map_plotkin`, `plotkin_id`, `plotkin_comp`, `isProjection_plotkin` |

So r0040's row 29 moves from `N` to `S+P`, and it moves for all three glyphs, not
only the one the paper writes out.

## 2. The verdict on `p(K(D)) ⊆ K(D)`: **false**, and it was the wrong question

The plan asked: *"Determine whether it holds for a general finitary projection,
and say which. If it fails, a counterexample is as valuable as a proof."*

**It fails, and the counterexample is formally checked.**
`PowerdomainCompacts.finitaryProjection_not_maps_compacts` and its contrapositive
form `not_forall_isCompactElement_apply` are the statements; here is the witness.

### 2.1 Why it must fail

A projection satisfies `p(x) ⊑ x`, and **compactness is not downward closed**. So
`p(K) ⊆ K` could hold in general only if every element below a compact element
were compact. That is false in any domain with a non-compact element strictly
under a compact one, and such a domain is one line away from Theorem 11.

This is also exactly why the closure analogue *does* hold and does not dualize.
`IsClosure.isCompactElement_apply` (`FinitaryProjectionPoset.lean:176`) argues
from `k ⊑ r(k) ⊑ u`, using `k ⊑ r(k)`; a projection has the inequality the other
way and the step has no replacement.

### 2.2 The witness

Take `A = ⟨ℕ ∪ {⊤}, ≤⟩` — countable, with a least element, so `D = Idl(A)` is a
domain by `IdealCompletion.instDomain` with no further work.

| # | element of `D` | as a set of `A` | compact? | declaration |
| -- | -------------- | --------------- | -------- | ----------- |
| 1 | `↓⊤` | all of `A` | **yes**, principal | `isCompactElement_topIdeal` |
| 2 | `natIdeal` | `{a \| a ≠ ⊤}` | **no** | `not_isCompactElement_natIdeal` |
| — | and `natIdeal < ↓⊤` | | | `natIdeal_lt_topIdeal` |

`natIdeal` is an ideal (downward closed because nothing below a natural is `⊤`,
directed by `max` because `A` is linearly ordered) and is not principal: a
generator would be some `↑n`, and `↑(n+1)` lies in it.

The projection is `p(I) = I ∩ natIdeal` — delete `⊤`. Scott continuous because a
directed supremum of ideals has the union as its underlying set
(`IdealCompletion.mem_sSup_iff`) and intersection with a fixed set commutes with
union; idempotent and below the identity because intersection is. And
`p(↓⊤) = natIdeal` (`p_topIdeal`).

### 2.3 It is *finitary*, so the counterexample is at full strength

The obligation was stated for a **finitary** projection, so `im(p)` must be shown
to be a domain — the only real work in that module. `im(p)` is the ideals of `A`
avoiding `⊤`, and

    up  : Idl(ℕ) → im(p),  up(K)  = {↑n | n ∈ K}
    down: im(p) → Idl(ℕ),  down(J) = {n | ↑n ∈ J}

are mutually inverse and order-reflecting (`rangeOrderIso`). `Idl(ℕ)` is a domain
by Theorem 11 again, and `PRep.domain_orderIso` transports it
(`domain_range`). Hence `isFinitaryProjection_pHom`.

**So the answer is: it fails for a general finitary projection, not merely for a
general projection.**

### 2.4 And the obligation dissolves rather than being discharged

r0038 recorded the missing action as blocked *on* this fact. Measured, the
dependence runs the other way: the paper's `ext` factors through the ideal
completion's universal property, which quantifies over **ideals** and never over
a transported basis, so `f♮` is defined for every continuous `f` with no
hypothesis about compacts at all. The construction that wanted
`p(K(D)) ⊆ K(D)` — transport finite sets of compacts, then act on ideals — cannot
be carried out for any map whatever, since even a finitary projection breaks it.
It was the wrong construction, not a construction waiting on a lemma.

What Lemma 28 actually needs from the action is that a projection acts as a
projection, and that is `isProjection_map`, proved from `map_comp` (idempotence)
and `map_le_map` with `map_id` (`p♮ ⊑ (id)♮ = id`) — no compacts anywhere.

## 3. Lemma 28: it moved, from 2 hypotheses to 4 of a different kind

`PowerdomainMapRep.lean` spends the action on conjuncts 8 and 9.
`PRep.isPRepresentable_of_repFamily` takes five inputs; measured against `(·)♯`:

| # | Input | Before r0041 | After |
| -- | ----- | ------------ | ----- |
| 1 | conjugating family `C : Fp(U) → ScottHom (U♯) (U♯)` | **did not exist** | `smythFamily p = (p.val)♯` |
| 2 | `C p` is a projection | not statable | **proved**, `isProjection_smythFamily` |
| 3 | `C` monotone in `p` | not statable | **proved**, `smythFamily_mono` |
| 4 | the retraction pair `(fn, gr)` at `U` | not posed | **discharged**, `PRepSum.pairAtU` |
| 5 | `im(C p) ≅ (im p)♯` | — | **open**: `SmythImageIso` |
| 6 | the index least upper bound | — | **open**: `SmythFamilyLUB` |

Row 4 is worth stating separately because it costs nothing and was not obviously
free: Theorem 27 supplies the pair for any bounded complete domain, and

| # | carrier | `Domain` | `BoundedComplete` |
| -- | ------- | -------- | ----------------- |
| 1 | `U♯` | Theorem 11, `Smyth.instDomain` | **Lemma 13**, `instBoundedCompleteSmyth`, spending `BoundedComplete Dyadic.U` |
| 2 | `U♭` | Theorem 11 | **Lemma 13**, `instBoundedCompleteHoare`, which needs only `[Domain α]` |

So this is the **second** place Lemma 28 spends Lemma 13, after Lemma 10's role
in `⇸` and `⊗` — a composition worth recording in the inventory.

`repSmythAtU` and `repHoareAtU` are the conjuncts at `Dyadic.U` from their two
obligations alone, and `lemma28AtU_of''` is Lemma 28 at `U` from four:

| # | theorem | arity |
| -- | ------- | ----: |
| 1 | `PRep.lemma28_of` | 9 |
| 2 | `PRepSum.lemma28AtU_of` | 5 |
| 3 | `Lemma28AtU.lemma28AtU_of'` (r0037) | 2 |
| 4 | `Rep.lemma28AtU_of''` (this round) | 4 |

**The arity went up and the position improved**, and the report should not hide
that. The two hypotheses of `lemma28AtU_of'` were `IsPRepresentable Dyadic.U
smythOp` and its Hoare twin — the conjuncts themselves, restated. The four
hypotheses here are ordinary statements about a functor that now exists, none of
which mentions `Fp(U)`, p-representability, or the retraction pair. **Numbered
results are unchanged at 7 of 9 for Lemma 28**; the conjuncts did not land.

### 3.1 What the two remaining obligations are, and their difficulty

`SmythImageIso` / `HoareImageIso` — **`im(p♯) ≅ (im p)♯`**. This is the real
theorem: the powerdomain commutes with the image of a finitary projection. It
cannot be proved by transporting a basis, because §2 shows `p(K(U)) ⊄ K(U)`; it
has to go through `IsProjection.isCompactElement_iff` (Lemma 5, r0014), which
characterises `K(im p)` intrinsically. I judge this a round of its own.

`SmythFamilyLUB` / `HoareFamilyLUB` — **local continuity**, `p ↦ p♯` preserves
directed suprema pointwise. This one is reachable and I did not have the budget
for it. The route is measured, not guessed: `map f I = ⨆ {foldGen ({|f ·|}) u |
u ∈ I}`, so it is an interchange of two suprema whose inner term is a finite
`⋓`-fold. The missing lemma is that the fold is continuous along a directed
family — an induction over the finite set with
`ContinuousAlgebra.isLUB_op_image` at the step, plus the observation that the
diagonal of `d ×ˢ d` is cofinal when `d` is directed. Everything else in the
chain exists: `isLUB_val_image_of_isLUB_fp'`,
`ScottHom.isLUB_eval_image_of_isLUB`, `scottContinuous_unit`. Estimate: one
lemma of ~100 lines, and it takes the four obligations to two.

## 4. Corrections to what was written before

| # | Where | Claim | Measured |
| -- | ----- | ----- | -------- |
| 1 | `Lemma28AtU.lean:48–51`, r0038 | *"the natural construction … wants `p(K(D)) ⊆ K(D)`; whether that holds is the step to settle first"* | **false twice over**: it does not hold, and the paper's construction does not want it. Docstring rewritten in place |
| 2 | r0041 plan, stream 3 | *"All three are `IdealCompletion (Pf K(D))` … so the natural construction acts on finite sets of compacts and then on ideals"* | that construction is exactly the one that fails. The action goes through `ext`, not through finite sets of compacts |
| 3 | r0041 plan, stream 3 | rows: 2 (+2 Lemma 28 conjuncts) | 1 property row (r0040 row 29) closed for **three** glyphs; the 2 Lemma 28 conjuncts reduced but **not** closed |
| 4 | `IsClosure.isCompactElement_apply` as a model | the projection analogue "does not exist" | it does not exist because it is **false** — worth recording, since a future round might otherwise try to prove it |

## 5. Measurements

| # | Quantity | Value |
| -- | -------- | ----: |
| 1 | full-library jobs | 1232 |
| 2 | lean diagnostics | 0 |
| 3 | lake errors | 0 |
| 4 | non-`sorry` warnings | 0 |
| 5 | `sorry` declarations | **1** (`thm18`, unchanged) |
| 6 | wall clock, incremental full build | 2.24 s |
| 7 | peak rss, single process | 1768 MiB |
| 8 | new lines | 1112 |
| 9 | new declarations | 103 |

Build log: `ScottDomains/logs/compile-20260808-132639.agent3.log`.

Axiom audit (`scripts/axioms.sh`), all `[propext, Classical.choice, Quot.sound]`,
none `sorryAx`: `map`, `exists_unique_map`, `map_id`, `map_comp`, `map_le_map`,
`isProjection_map`, `thm_map_hoare`, `thm_map_smyth`, `thm_map_plotkin`,
`isProjection_smyth`, `isProjection_hoare`, `Compacts.isFinitaryProjection_pHom`,
`Compacts.finitaryProjection_not_maps_compacts`,
`Compacts.not_forall_isCompactElement_apply`, `Rep.rep_smyth_of`,
`Rep.rep_hoare_of`, `Rep.repSmythAtU`, `Rep.repHoareAtU`, `Rep.lemma28AtU_of''`.

## 6. Import structure, for the merge

`PowerdomainMap.lean` imports only `ContinuousAlgebra` and `Projection`, so it
stays importable **by** `PRep` — deliberate, because a future round proving
`SmythImageIso` will want the action inside `PRep`'s own development. The two
consumers sit above: `PowerdomainCompacts.lean` imports `PRep` (for
`domain_orderIso`) and `PowerdomainMapRep.lean` imports `PRepSum` and
`Lemma28AtU`. No cycle, and no existing module's imports changed.

One existing file was edited: `Lemma28AtU.lean`'s module docstring, whose
staleness note is the one row 1 of §4 corrects. No `.lean` proof text elsewhere
was touched.
