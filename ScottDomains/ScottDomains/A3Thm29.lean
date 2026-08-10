import ScottDomains.LemThirty
import ScottDomains.Flat
import ScottDomains.FlatSection6
import ScottDomains.PRepFun
import ScottDomains.PRepSum
import ScottDomains.Skeleton.Section6

/-!
# r0045, agent3: `Colimit.Theorem29Second` is false

Round r0045 asked whether the six `Prop`-valued claims of the §7.4 cluster
(`Colimit.Theorem29Second`, `Colimit.Lemma30Arrow`, `LemThirty.Theorem29SecondAtDomains`,
`LemThirty.Theorem29Normal`, `LemThirty.Lemma30`, `LemThirty.Lemma30AtV`) can be
discharged. One of them cannot: **`Colimit.Theorem29Second` is refutable**, and
`not_thm29Second` below is the kernel-checked refutation.

## What is refuted, and what is not

`Colimit.Theorem29Second` reads

    ∀ (E : Type) [CompletePartialOrder E], IsBifinite E →
      ∃ g p, ScottHom.IsEmbeddingProjectionPair g p

with `IsBifinite E` alone — the Plotkin condition on `K(E)` — and **no `[Domain E]`**.
Gunter & Scott's printed sentence says "`E` is any bifinite *domain*", so the
refutation convicts this development's transcription of Theorem 29's second
sentence and **not the paper**. `LemThirty.Theorem29SecondAtDomains`, which restores
the missing word, is untouched by the argument below and remains open.

## The argument, in three steps

| # | Step | Declaration |
| - | ---- | ----------- |
| 1 | every flat cpo is bifinite, with no countability hypothesis | `isBifinite_flat` |
| 2 | an embedding of an embedding–projection pair carries compact elements to compact elements | `isCompactElement_embedding` |
| 3 | `K(V)` is countable but `Flat (Set ℕ)` is not | `not_thm29Second` |

Step 2 is the only one with content. Given `p ∘ g = id` and `g ∘ p ⊑ id` and a
compact `x`, let `s` be directed with `g x ⊑ ⨆ s`. Scott continuity of `p` makes
`p '' s` directed with supremum `p (⨆ s)`, and `x = p (g x) ⊑ p (⨆ s)`, so
compactness of `x` yields `s₀ ∈ s` with `x ⊑ p s₀`; then
`g x ⊑ g (p s₀) ⊑ s₀`. Nothing about algebraicity or countability is used.

Step 3 instantiates at `E := Flat (Set ℕ)`. Every element of a flat cpo is
compact (`Flat.isCompactElement`), so step 2 makes `g` an injection of
`Flat (Set ℕ)` into `↥(compacts V)`. `Domain V` is an instance and
`Domain.countable_compacts` makes `↥(compacts V)` countable, while Cantor's
theorem makes `Set ℕ` — hence `Flat (Set ℕ)` — uncountable. `Set ℕ` is used
rather than `ℝ` only to avoid pulling `Mathlib.Analysis` into this library;
any uncountable type does.

## Consequence for the rest of `LemThirty.lean`

Seven declarations take `Colimit.Theorem29Second` as a hypothesis:
`retracts_of_isBifinite`, `theorem_29_secondAtDomains_of_thm29Second`,
`retracts_smash`, `retracts_sepSum`, `retracts_coalSum`,
`retracts_fun_of_boundedComplete`, `retracts_strictFun_of_boundedComplete`.
All seven are still theorems and all seven are now **vacuous**: their hypothesis
is refuted, so they carry no information about `V`. In particular Lemma 30's
conjuncts `⊗`, `+` and `⊕` have *no* route to a retraction pair over `V` in this
development — the route recorded in `LemThirty.lean`'s header table, row 5, is
through a false proposition. Repairing it needs `Domain (Smash V V)`,
`Domain (SeparatedSum V V)` and `Domain (CoalescedSum V V)`, none of which this
development proves, after which those three go through
`Theorem29SecondAtDomains` like the other five.

## The dependency order among the six claims

Kernel-checked here (`lemma_30_arrow_of_lemma30AtV`, `lemma_30_atV_iff`) or already in
`LemThirty.lean` (`theorem_29_secondAtDomains_of_thm29Normal`,
`theorem_29_secondAtDomains_of_thm29Second`):

    Theorem29Normal ⟹ Theorem29SecondAtDomains ⟹ 5 of Lemma 30's 10 retraction pairs
    Theorem29Second ⟹ Theorem29SecondAtDomains        (vacuous: Theorem29Second is false)
    Lemma30AtV = Lemma30 V ⟹ Lemma30Arrow       (first conjunct)

`Theorem29Normal` is *not* above `Lemma30AtV`: it supplies the retraction pairs, but
seven of the ten `PRep` representation schemes those pairs feed are themselves
unproved, so no implication runs from `Theorem29Normal` to `Lemma30AtV` today.
-/

namespace ScottDomains.R45.Agent3

open ScottDomains ScottDomains.Colimit ScottDomains.LemThirty

/-! ## Step 1: every flat cpo is bifinite -/

/-- **Every flat cpo is bifinite**, with no hypothesis on the carrier `X`.
`compacts (Flat X)` is all of `Flat X` (`Flat.compacts_eq_univ`), and for a
finite `u` the witness is `insert ⊥ u`: a set of a flat order intersected with
`↓x` lies inside `{⊥, x}`, which is a chain, so directedness is immediate.

This is where the missing `[Domain E]` bites. `Skeleton.proposition_15` also proves
bifiniteness, but through `[Domain α]`, whose `countable_compacts` field is
exactly what an uncountable flat cpo lacks. -/
theorem isBifinite_flat (X : Type) : IsBifinite (Flat X) := by
  rw [IsBifinite, Flat.compacts_eq_univ]
  intro u hu _
  refine ⟨insert ⊥ u, hu.insert ⊥, ⟨Set.subset_univ _, fun x _ => ⟨⟨⊥, Set.mem_insert _ _, ?_⟩, ?_⟩⟩,
    Set.subset_insert _ _⟩
  · exact Set.mem_Iic.mpr bot_le
  · rintro a ⟨haN, hax⟩ b ⟨hbN, hbx⟩
    rcases Flat.le_iff.mp (Set.mem_Iic.mp hax) with h | h
    · refine ⟨b, ⟨hbN, hbx⟩, ?_, le_rfl⟩
      rw [h]
      exact Flat.bot_le' b
    · refine ⟨a, ⟨haN, hax⟩, le_rfl, ?_⟩
      rw [h]
      exact Set.mem_Iic.mp hbx

/-! ## Step 2: an embedding preserves compactness -/

/-- **The embedding of an embedding–projection pair carries `K(α)` into `K(β)`.**

Standard, and stated nowhere in this development before now. The proof spends
`p ∘ g = id` once (to move `x` under `p (⨆ s)`), Scott continuity of `p` once (to
know `p '' s` is a directed set with that supremum), and `g ∘ p ⊑ id` once (to
come back). Neither carrier is assumed algebraic and neither basis is assumed
countable. -/
theorem isCompactElement_embedding {α β : Type*} [CompletePartialOrder α]
    [CompletePartialOrder β] {g : ScottHom α β} {p : ScottHom β α}
    (h : ScottHom.IsEmbeddingProjectionPair g p) {x : α} (hx : IsCompactElement x) :
    IsCompactElement (g x) := by
  intro s u hne hdir hlub hle
  have hpdir : DirectedOn (· ≤ ·) (⇑p '' s) := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    obtain ⟨c, hc, hac, hbc⟩ := hdir a ha b hb
    exact ⟨p c, ⟨c, hc, rfl⟩, p.monotone hac, p.monotone hbc⟩
  have hplub : IsLUB (⇑p '' s) (p u) := p.scottContinuous hne hdir hlub
  have hxle : x ≤ p u := by
    rw [← h.1 x]
    exact p.monotone hle
  obtain ⟨y, hy, hxy⟩ := hx (⇑p '' s) (p u) (hne.image _) hpdir hplub hxle
  obtain ⟨c, hc, rfl⟩ := hy
  exact ⟨c, hc, (g.monotone hxy).trans (h.2 c)⟩

/-! ## Step 3: the refutation -/

/-- `Set ℕ` is uncountable — Cantor's theorem, in the form Mathlib's
`Uncountable` class consumes. -/
theorem uncountable_setNat : Uncountable (Set ℕ) :=
  uncountable_iff_forall_not_surjective.mpr fun f => Function.cantor_surjective f

/-- `Flat.up` is injective, so a flat cpo is at least as big as its carrier. -/
theorem up_injective {X : Type*} : Function.Injective (Flat.up : X → Flat X) :=
  fun _ _ hab => Flat.up_le_up_iff.mp (le_of_eq hab)

/-- `Flat (Set ℕ)` is uncountable: the bifinite cpo that `Colimit.Theorem29Second`
cannot accommodate. -/
theorem uncountable_flat_setNat : Uncountable (Flat (Set ℕ)) :=
  haveI := uncountable_setNat
  up_injective.uncountable

/-- **`Colimit.Theorem29Second` is false.**

The claim asserts an embedding–projection pair `E ⇄ V` for every cpo `E`
satisfying `IsBifinite E`, with no `[Domain E]`. Take `E := Flat (Set ℕ)`:
`isBifinite_flat` supplies the hypothesis, every element of a flat cpo is
compact, and `isCompactElement_embedding` therefore makes the embedding an
injection of the uncountable `Flat (Set ℕ)` into the countable `↥(compacts V)`.

This does **not** refute Gunter & Scott's printed sentence, which says "`E` is
any bifinite *domain*"; `LemThirty.Theorem29SecondAtDomains` is the transcription
that keeps the word, and it survives. -/
theorem not_thm29Second : ¬ Colimit.Theorem29Second := by
  intro h
  obtain ⟨g, p, hgp⟩ := h (Flat (Set ℕ)) (isBifinite_flat (Set ℕ))
  haveI : Countable ↥(compacts V) := (Domain.countable_compacts (α := V)).to_subtype
  haveI := uncountable_flat_setNat
  refine not_injective_uncountable_countable
    (fun x : Flat (Set ℕ) =>
      (⟨g x, isCompactElement_embedding hgp (Flat.isCompactElement x)⟩ : ↥(compacts V))) ?_
  intro a b hab
  exact hgp.injective_embedding (congrArg Subtype.val hab)

/-! ## The added `[Domain E]` is load-bearing in `Theorem29Normal` too

`LemThirty.Theorem29SecondAtDomains` is `Colimit.Theorem29Second` with one instance
binder added, `[Domain E]`, and nothing else changed — compare the two `def`
lines, `Colimit.lean:1028` and `LemThirty.lean:277`. `not_thm29Second` therefore
does more than refute one claim: it shows that binder is **necessary**, so
`Theorem29SecondAtDomains` is not a restatement that could have been skipped.

`LemThirty.Theorem29Normal` carries the same binder inside its own statement, and
`LemThirty.lean:506–512` asserts in a docstring that the version without it "is
refutable rather than open". **Nothing proved that.** It is proved here, by the
same witness, so that the necessity of the binder is kernel-checked at both
places rather than asserted at one and argued at the other. -/

/-- `LemThirty.Theorem29Normal` with the `[Domain E]` binder deleted. Defined in
agent3's namespace purely so the next theorem can refute it; `Theorem29Normal` itself
is untouched, and this is **not** a restatement of it — it is the strictly
stronger proposition the docstring claims is refutable. -/
def Theorem29NormalWithoutDomain : Prop :=
  ∀ (E : Type) [CompletePartialOrder E], IsBifinite E →
    ∃ f : ↥(compacts E) → Ainf,
      (∀ a b, f a ≤ f b ↔ a ≤ b) ∧ Set.range f ◁ (Set.univ : Set Ainf)

/-- **`Theorem29Normal` without `[Domain E]` is false**, as `LemThirty.lean:506–512`
says but does not prove. `A∞` is countable and an order-reflecting map has a
countable source (`LemThirty.countable_compacts_of_reflects`), while
`Flat (Set ℕ)` is bifinite with an uncountable basis.

Read together with `not_thm29Second`, this fixes the status of the whole cluster
precisely: both §7.4 claims are false at the binders the paper does not assume
and open at the binders it does. Adding `[Domain E]` and proving the result would
be a discharge **at** `[Domain E]`, not a discharge of the general statement —
and here the general statement is not merely unproved, it is refuted. -/
theorem not_thm29NormalWithoutDomain : ¬ Theorem29NormalWithoutDomain := by
  intro h
  obtain ⟨f, hf, _⟩ := h (Flat (Set ℕ)) (isBifinite_flat (Set ℕ))
  haveI : Countable ↥(compacts (Flat (Set ℕ))) :=
    LemThirty.countable_compacts_of_reflects hf
  haveI := uncountable_flat_setNat
  refine not_injective_uncountable_countable
    (fun x : Flat (Set ℕ) =>
      (⟨x, Flat.isCompactElement x⟩ : ↥(compacts (Flat (Set ℕ))))) ?_
  intro a b hab
  exact congrArg Subtype.val hab

/-! ## The dependency order, kernel-checked -/

/-- `LemThirty.Lemma30AtV` is `LemThirty.Lemma30 Colimit.V` — the `abbrev`
unfolds, and the kernel confirms it. -/
theorem lemma_30_atV_iff : LemThirty.Lemma30AtV ↔ LemThirty.Lemma30 Colimit.V := Iff.rfl

/-- **`Colimit.Lemma30Arrow` is Lemma 30's first conjunct at `V`.**
`Colimit.lean:1024` asserts this in a docstring; `PRep.funOp` is
`Cpo.funSpace` by definition, so the two propositions are definitionally equal
and `Lemma30AtV` implies `Lemma30Arrow` by first projection. The docstring is
correct. -/
theorem lemma_30_arrow_iff :
    Colimit.Lemma30Arrow ↔ BifiniteUniversal.IsPRepresentable₂ Colimit.V PRep.funOp := Iff.rfl

/-- `Lemma30AtV ⟹ Lemma30Arrow`: the dependency the round asked for, as a term. -/
theorem lemma_30_arrow_of_lemma30AtV (h : LemThirty.Lemma30AtV) : Colimit.Lemma30Arrow := h.1

/-! ## Repairing `⊗`, `+` and `⊕`: they never needed `Theorem29Second`

`LemThirty.lean:346–355` gives a measurement to justify routing the `⊗`, `+` and
`⊕` retraction pairs through `Colimit.Theorem29Second` rather than through
`Theorem29SecondAtDomains`:

> Measured over the whole library, `IsAlgebraic` instances exist for `ScottHom`,
> `Set X`, `IdealCompletion` and `WithBot` … `Smash`, `CoalescedSum` and
> `SeparatedSum` have Lemma 10's bounded completeness and Lemma 17's
> bifiniteness but no algebraicity and no `Domain`.

**That measurement is false.** `PRepFun.smashIsAlgebraic`, `PRepFun.smashDomain`,
`PRepSum.isAlgebraic_coalescedSum` and `PRepSum.domain_coalescedSum` all exist
and are proved, and `ClosureProperties.SeparatedSum A B` is by definition
`CoalescedSum A⊥ B⊥`, so the third case is the second one at `WithBot V`
(`PRepSum.lean:1053` already uses it that way at `Dyadic.U`).

So all three pairs go through `retracts_of_isDomain`, and the three results below
replace `LemThirty.retracts_smash`, `retracts_sepSum` and `retracts_coalSum` —
each **one refuted hypothesis lighter**, since `Colimit.Theorem29Second` is false and
`Theorem29SecondAtDomains` is open.

The same correction applies to `LemThirty.lean:388–393` ("`PRep.rep_lift` and
`PRep.rep_prod` are the only two of Lemma 28's nine schemes already proved"):
measured on this branch, **seven** of the nine exist — `PRep.rep_lift`,
`PRep.rep_prod`, `PRepFun.rep_arrow`, `PRepFun.rep_strictArrow`,
`PRepFun.rep_smash`, `PRepSum.rep_coalSum`, `PRepSum.rep_sepSum`. Only the three
powerdomain schemes `(·)♯`, `(·)♭`, `(·)♮` are missing. -/

theorem domain_smash_V : Domain (Smash V V) := PRepFun.smashDomain

theorem domain_coalSum_V : Domain (CoalescedSum V V) := PRepSum.domain_coalescedSum

theorem domain_sepSum_V : Domain (ClosureProperties.SeparatedSum V V) :=
  PRepSum.domain_coalescedSum

/-- Conjunct 4's pair, `⊗`, from `Theorem29SecondAtDomains` — the hypothesis
`LemThirty.retracts_smash` should have taken. -/
theorem retracts_smash_V (h : LemThirty.Theorem29SecondAtDomains) :
    LemThirty.Retracts (Smash V V) := by
  haveI := domain_smash_V
  exact LemThirty.retracts_of_isDomain h _ (lemma_17_smash isBifinite_V isBifinite_V)

/-- Conjunct 6's pair, `⊕`, from `Theorem29SecondAtDomains`. -/
theorem retracts_coalSum_V (h : LemThirty.Theorem29SecondAtDomains) :
    LemThirty.Retracts (CoalescedSum V V) := by
  haveI := domain_coalSum_V
  exact LemThirty.retracts_of_isDomain h _ (lemma_17_sum isBifinite_V isBifinite_V)

/-- Conjunct 5's pair, `+`, from `Theorem29SecondAtDomains`. -/
theorem retracts_sepSum_V (h : LemThirty.Theorem29SecondAtDomains) :
    LemThirty.Retracts (ClosureProperties.SeparatedSum V V) := by
  haveI := domain_sepSum_V
  exact LemThirty.retracts_of_isDomain h _
    (ClosureProperties.lemma_17_separated isBifinite_V isBifinite_V)

/-- **Conjunct 4 of Lemma 30: `⊗` is p-representable over `V`**, given Theorem
29's second sentence at the paper's own hypothesis. `PRepFun.rep_smash` at
`U := V`, exactly as `LemThirty.rep_lift_V` is `PRep.rep_lift` at `U := V`. -/
theorem rep_smash_V (h : LemThirty.Theorem29SecondAtDomains) :
    BifiniteUniversal.IsPRepresentable₂ V PRep.smashOp := by
  obtain ⟨_gr, _fn, hfg, hgf⟩ := retracts_smash_V h
  exact PRepFun.rep_smash hfg hgf

/-- **Conjunct 6 of Lemma 30: `⊕` is p-representable over `V`.** -/
theorem rep_coalSum_V (h : LemThirty.Theorem29SecondAtDomains) :
    BifiniteUniversal.IsPRepresentable₂ V PRep.coalSumOp := by
  obtain ⟨_gr, _fn, hfg, hgf⟩ := retracts_coalSum_V h
  exact PRepSum.rep_coalSum hfg hgf

/-- **Conjunct 5 of Lemma 30: `+` is p-representable over `V`.** -/
theorem rep_sepSum_V (h : LemThirty.Theorem29SecondAtDomains) :
    BifiniteUniversal.IsPRepresentable₂ V PRep.sepSumOp := by
  obtain ⟨_gr, _fn, hfg, hgf⟩ := retracts_sepSum_V h
  exact PRepSum.rep_sepSum hfg hgf

/-- **Five of Lemma 30's ten conjuncts, from `Theorem29Normal` alone.** Conjuncts 3,
4, 5, 6 and 7 — `×`, `⊗`, `+`, `⊕`, `(·)⊥`. Before this round the figure was two
(`LemThirty.rep_lift_V_of_thm29Normal`, `rep_prod_V_of_thm29Normal`); the other
three were routed through the now-refuted `Colimit.Theorem29Second` and were
therefore vacuous. The three that remain open are the powerdomain conjuncts
`(·)♯`, `(·)♭`, `(·)♮`, and the two function-space conjuncts `→`, `⇸`, which
`not_boundedComplete_V` below shows are blocked by a structural obstruction
rather than by missing work.

*Corrected in r0046 (agent5).* This sentence used to say the powerdomain
conjuncts are open "whose `PRep` schemes do not exist". Two of the three schemes
do exist: `PRep.smythOp` (`PRep.lean:214`) and `PRep.hoareOp` (`PRep.lean:225`),
both `Cpo → Cpo`, and `PRep.Lemma28AtU` is stated over them
(`PRep.lean:260-261`). Checked against the built `.olean` by
`scripts/a5-r46-exists.lean`, where both `#check`s resolve. Only `(·)♮`
(Plotkin) has no `PRep` scheme. What is actually open for `♯` and `♭` at `V` is
the representability, not the scheme — and at `U` even that is discharged
(`R45.Agent4.repSmythAtU`, `repHoareAtU`). -/
theorem five_conjuncts_of_thm29Normal (h : LemThirty.Theorem29Normal) :
    BifiniteUniversal.IsPRepresentable₂ V PRep.prodOp ∧
    BifiniteUniversal.IsPRepresentable₂ V PRep.smashOp ∧
    BifiniteUniversal.IsPRepresentable₂ V PRep.sepSumOp ∧
    BifiniteUniversal.IsPRepresentable₂ V PRep.coalSumOp ∧
    BifiniteUniversal.IsPRepresentable V PRep.liftOp :=
  let h' := LemThirty.theorem_29_secondAtDomains_of_thm29Normal h
  ⟨LemThirty.rep_prod_V h', rep_smash_V h', rep_sepSum_V h', rep_coalSum_V h',
    LemThirty.rep_lift_V h'⟩

/-! ## `→` and `⇸` are blocked, and the obstruction survives the refutation

`LemThirty.lean:107–110` argues that `Colimit.Theorem29Second` and
`BoundedComplete V` cannot both hold. With `Theorem29Second` refuted that argument
proves nothing, so it is redone here from the *live* hypothesis: even
`Theorem29SecondAtDomains` is incompatible with `BoundedComplete V`.

The witness is the paper's own. `T × T` is a bounded complete domain
(`Flat.instDomainTT`, `Flat.instBoundedCompleteTT`), hence bifinite by
Proposition 15, and `(T × T)♮` is a bifinite domain that is **not** bounded
complete (`Flat.not_boundedComplete_plotkin_TT`). If `V` were bounded complete,
`Theorem29SecondAtDomains` would make `(T × T)♮` a retract of it, and bounded
completeness transfers along a retraction.

The consequence is sharp: `PRepFun.rep_arrow` and `PRepFun.rep_strictArrow` are
this development's only routes to Lemma 30's conjuncts 1 and 2, and both carry
`[BoundedComplete U]`. So those two conjuncts are unreachable here for as long as
Theorem 29's second sentence is assumed. This is a defect of the development's
route to `Domain (D → E)` — through Theorem 7's step functions, which need
bounded completeness of the codomain — and **not** of Lemma 30, which is a true
statement about the bifinite `V`. `ClosureProperties.lean` already records the
`[BoundedComplete β]` in `lemma_17_fun` as "a real open item, not a formality". -/

/-- **Bounded completeness transfers along an embedding–projection pair**, in the
existence form. Stated as `∃ u, IsLUB s u` rather than as `BoundedComplete E`
because `BoundedComplete` constrains `E`'s own `sSup`, which a retraction says
nothing about; the existence form is what `Flat.not_exists_isLUB` refutes. -/
theorem exists_isLUB_of_embeddingProjectionPair {E β : Type*} [CompletePartialOrder E]
    [CompletePartialOrder β] [BoundedComplete β] {g : ScottHom E β} {p : ScottHom β E}
    (h : ScottHom.IsEmbeddingProjectionPair g p) {s : Set E} (hs : BddAbove s) :
    ∃ u, IsLUB s u := by
  obtain ⟨b, hb⟩ := hs
  have hgs : BddAbove (⇑g '' s) := ⟨g b, by rintro _ ⟨x, hx, rfl⟩; exact g.monotone (hb hx)⟩
  obtain ⟨u, hu⟩ := exists_isLUB_of_bddAbove hgs
  refine ⟨p u, fun x hx => ?_, fun c hc => ?_⟩
  · rw [← h.1 x]
    exact p.monotone (hu.1 ⟨x, hx, rfl⟩)
  · rw [← h.1 c]
    exact p.monotone (hu.2 (by rintro _ ⟨x, hx, rfl⟩; exact g.monotone (hc hx)))

/-- `(T × T)♮` is a bifinite domain — Proposition 15 on `T × T`, then Lemma 17's
`♮` conjunct. This is the witness `not_boundedComplete_V` needs. -/
theorem isBifinite_plotkin_TT : IsBifinite (Plotkin.Powerdomain Flat.TT) :=
  ClosureProperties.lemma_17_plotkin (proposition_15 (α := Flat.TT))

/-- **`Theorem29SecondAtDomains` forces `V` not to be bounded complete.**
Consequently Lemma 30's conjuncts 1 (`→`) and 2 (`⇸`) have no route in this
development: `PRepFun.rep_arrow` and `PRepFun.rep_strictArrow` both require
`[BoundedComplete U]`, and `LemThirty.retracts_fun_of_boundedComplete` and
`retracts_strictFun_of_boundedComplete` take it as an instance argument. -/
theorem not_boundedComplete_V (h : LemThirty.Theorem29SecondAtDomains) : ¬ BoundedComplete V := by
  intro hbc
  haveI := hbc
  obtain ⟨g, p, hgp⟩ := h (Plotkin.Powerdomain Flat.TT) isBifinite_plotkin_TT
  exact Flat.not_exists_isLUB
    (exists_isLUB_of_embeddingProjectionPair hgp Flat.bddAbove_pair)

end ScottDomains.R45.Agent3
