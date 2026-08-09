---
round: r0045
from: agent3
to: orchestrator
subject: discharge-thm29
date: 2026-0808-21:35
started: 2026-0808-21:05
finished: 2026-0808-21:35
related:
  - plans/r0045-plan-from-orchestrator-to-orchestrator-discharge-nineteen.md
  - reports/r0044-report-from-agent6-to-orchestrator-undischarged-defs.md
  - ScottDomains/A3Thm29.lean
---

# r0045 agent3 — §7.4: Theorem 29's second sentence and Lemma 30

One new file, `ScottDomains/A3Thm29.lean`, 15 theorems and one auxiliary `def`,
all in namespace `ScottDomains.R45.Agent3`. Full package build: **1340 jobs,
0 errors, 0 warnings, `sorry` 0**. Every theorem's axiom footprint is
`[propext, Classical.choice, Quot.sound]` or smaller; no `sorryAx`.

**Headline: `ScottDomains.Colimit.Thm29Second` is false, and the refutation is
kernel-checked** (`not_thm29Second`). It convicts this development's
transcription, not the paper.

This report uses the orchestrator's corrected acceptance criterion: *discharged*
means the binders are exactly those the claim's own `def` line carries;
*discharged at `<binder>`* means an instance binder was added and the general
claim remains open. **Nothing in this round is a discharge at an added binder**,
and §2b is the binder audit that establishes it declaration by declaration.
Outcome 1 of the orchestrator's three — refutation — is what happened, twice.

## 1. The dependency order among the six claims

Asked for first, and it is not what the plan supposed. Measured against the built
`.olean`, not against docstrings.

| # | Edge | Status | Witness |
| -- | ---- | ------ | ------- |
| 1 | `Thm29Normal ⟹ Thm29SecondAtDomains` | proved before this round | `LemThirty.thm29SecondAtDomains_of_thm29Normal` |
| 2 | `Thm29Second ⟹ Thm29SecondAtDomains` | proved, now **vacuous** | `LemThirty.thm29SecondAtDomains_of_thm29Second` |
| 3 | `Lemma30AtV ≡ Lemma30 V` | `abbrev`, definitional | `lemma30AtV_iff` (this round) |
| 4 | `Lem30Arrow ≡` conjunct 1 of `Lemma30 V` | definitional (`PRep.funOp` is `Cpo.funSpace`) | `lem30Arrow_iff`, `lem30Arrow_of_lemma30AtV` (this round) |
| 5 | `Thm29Normal ⟹ Lemma30AtV` | **does not hold as an implication** | see below |

The plan's premise — "if `LemThirty.lean:469` is right, discharging
`Thm29Normal` discharges more than one row" — is **half right**. Line 469 is
right: `exists_embeddingProjectionPair_of_thm29Normal` and
`thm29SecondAtDomains_of_thm29Normal` are proved and kernel-checked, so
`Thm29Normal` really does discharge `Thm29SecondAtDomains` outright, row 1 above.

It does **not** reach `Lemma30AtV`. `Thm29Normal` supplies retraction pairs; a
Lemma 30 conjunct also needs the corresponding `PRep` representation scheme, and
three of the ten schemes do not exist. Measured on this branch:

| # | Conjunct | Retraction pair over `V` | `PRep` scheme | Status under `Thm29Normal` |
| -- | -------- | ------------------------ | ------------- | -------------------------- |
| 1 | `→` | needs `[BoundedComplete V]` | `PRepFun.rep_arrow` needs `[BoundedComplete U]` | **structurally blocked** (§4) |
| 2 | `⇸` | needs `[BoundedComplete V]` | `PRepFun.rep_strictArrow` needs `[BoundedComplete U]` | **structurally blocked** (§4) |
| 3 | `×` | `LemThirty.retracts_prod` | `PRep.rep_prod` | **follows** |
| 4 | `⊗` | `retracts_smash_V` (this round) | `PRepFun.rep_smash` | **follows** (new) |
| 5 | `+` | `retracts_sepSum_V` (this round) | `PRepSum.rep_sepSum` | **follows** (new) |
| 6 | `⊕` | `retracts_coalSum_V` (this round) | `PRepSum.rep_coalSum` | **follows** (new) |
| 7 | `(·)⊥` | `LemThirty.retracts_lift` | `PRep.rep_lift` | **follows** |
| 8 | `(·)♯` | `LemThirty.retracts_smyth` | missing | open — agent4's stream |
| 9 | `(·)♭` | `LemThirty.retracts_hoare` | missing | open — agent4's stream |
| 10 | `(·)♮` | `LemThirty.retracts_plotkin` | missing | open — agent4's stream |

`five_conjuncts_of_thm29Normal` states rows 3–7 as one theorem from
`Thm29Normal` alone. Before this round the figure was **two** (rows 3 and 7);
rows 4, 5, 6 were routed through the refuted `Thm29Second` and were vacuous.

## 2. `Colimit.Thm29Second` is FALSE — refuted

`theorem not_thm29Second : ¬ Colimit.Thm29Second`, footprint
`[propext, Classical.choice, Quot.sound]`.

The claim as recorded is

    ∀ (E : Type) [CompletePartialOrder E], IsBifinite E →
      ∃ g p, ScottHom.IsEmbeddingProjectionPair g p

with **no `[Domain E]`**. Take `E := Flat (Set ℕ)`. Three steps, all new:

| # | Step | Theorem |
| -- | ---- | ------- |
| 1 | every flat cpo is bifinite, no hypothesis on the carrier | `isBifinite_flat` |
| 2 | the embedding of an embedding–projection pair carries compacts to compacts | `isCompactElement_embedding` |
| 3 | `↥(compacts V)` is countable, `Flat (Set ℕ)` is not | `not_thm29Second` |

Step 2 is the only one with content: `x = p (g x) ⊑ p (⨆ s)`, compactness of `x`
gives `s₀ ∈ s` with `x ⊑ p s₀`, and `g x ⊑ g (p s₀) ⊑ s₀`. It needs neither
algebraicity nor countability of either carrier, and it is stated nowhere else in
the development. Every element of a flat cpo is compact
(`Flat.isCompactElement`), so `g` becomes an injection of an uncountable type
into `↥(compacts V)`, which `Domain.countable_compacts` makes countable.

`Set ℕ` is the uncountable carrier rather than the plan's `ℝ`, to keep
`Mathlib.Analysis` out of this library; `Function.cantor_surjective` supplies
`Uncountable (Set ℕ)` in three lines. Any uncountable type works.

**The paper is not convicted.** Gunter & Scott write "`E` is any bifinite
*domain*"; `Flat (Set ℕ)` is bifinite and is not a domain (uncountable basis).
This is the development's own over-strengthening, exactly as
`LemThirty.lean:143–150` predicted. `Thm29SecondAtDomains` restores the word and
survives. **No tenth printed defect** — the count in
`docs/StatementRecovery.md` stays at nine.

### Consequence: seven declarations became vacuous

`retracts_of_isBifinite`, `thm29SecondAtDomains_of_thm29Second`,
`retracts_smash`, `retracts_sepSum`, `retracts_coalSum`,
`retracts_fun_of_boundedComplete`, `retracts_strictFun_of_boundedComplete` all
take `Colimit.Thm29Second` as a hypothesis. All seven are still theorems and all
seven now carry no information. Three of them are repaired below; the other four
are subsumed.

## 2b. Binder audit — the three outcomes kept apart

The orchestrator's warning is acute here because
`LemThirty.Thm29SecondAtDomains` **is** `Colimit.Thm29Second` with one instance
binder added. The two `def` lines, `Colimit.lean:1028` and `LemThirty.lean:277`,
are character-for-character identical except for `[Domain E]`. So the three
outcomes are not hypothetical in this cluster — they are three different rows
that already exist in the tree, and conflating them is exactly the failure mode.

| # | Outcome | What it would be here | Actual |
| -- | ------- | --------------------- | ------ |
| 1 | refuted | `¬ Thm29Second` | **done**, `not_thm29Second` |
| 2 | discharged at `[Domain E]` | a proof of `Thm29SecondAtDomains` | **not done** — it is `Thm29Normal`'s content and open |
| 3 | open | — | applies to rows 3, 4, 6 of §7 |

Outcome 2 did not happen and is not claimed anywhere in this round. I did not add
`[Domain E]` to `Thm29Second` and call it proved; `Thm29SecondAtDomains` is a
pre-existing separate `def` that I left open.

Every declaration added this round, with its binders compared against the binders
of the claim it addresses:

| # | Declaration | Binders in signature | Verdict |
| -- | ----------- | -------------------- | ------- |
| 1 | `not_thm29Second` | none | refutation of a claim whose `def` has no binders — clean |
| 2 | `not_thm29NormalWithoutDomain` | none | refutation, clean |
| 3 | `isBifinite_flat (X : Type)` | `(X : Type)` only — **no `[Countable X]`** | general lemma; the absent binder is the point |
| 4 | `isCompactElement_embedding` | the two `[CompletePartialOrder]` the statement needs to typecheck | general lemma, not a claim |
| 5 | `exists_isLUB_of_embeddingProjectionPair` | `[BoundedComplete β]`, genuinely used | general lemma, not a claim |
| 6 | `retracts_{smash,coalSum,sepSum}_V` | none; hypothesis `Thm29SecondAtDomains` | reduction — `Domain (Smash V V)` etc. are **proved** (`domain_smash_V`), not assumed as binders |
| 7 | `rep_{smash,coalSum,sepSum}_V` | none; hypothesis `Thm29SecondAtDomains` | reduction |
| 8 | `five_conjuncts_of_thm29Normal` | none; hypothesis `Thm29Normal` | reduction |
| 9 | `not_boundedComplete_V` | none; hypothesis `Thm29SecondAtDomains` | reduction |
| 10 | `lem30Arrow_of_lemma30AtV`, `lem30Arrow_iff`, `lemma30AtV_iff` | none | dependency edges |

Row 6 is the one worth checking twice, because it is where an added binder would
most naturally have crept in: `LemThirty.retracts_smash` could have been repaired
by writing `[Domain (Smash V V)]` into the signature. It is not — the instance is
discharged inside the proof from `PRepFun.smashDomain`, so the theorem's binder
list is empty.

### The added binder is necessary, and that is now kernel-checked twice

`not_thm29Second` shows `[Domain E]` cannot be dropped from
`Thm29SecondAtDomains`. `LemThirty.lean:506–512` asserts the same about
`Thm29Normal` — "the version without `[Domain E]` is refutable rather than open"
— and **nothing proved it**. It is proved now:

    theorem not_thm29NormalWithoutDomain : ¬ Thm29NormalWithoutDomain

where `Thm29NormalWithoutDomain` is `Thm29Normal` with the binder deleted,
defined in agent3's namespace so `LemThirty.Thm29Normal` is untouched. Footprint
`[propext, Classical.choice, Quot.sound]`. So for both §7.4 claims the position
is now exact: **false at the binders the paper does not assume, open at the
binders it does.** That is the strongest form of "the added binder is
load-bearing", and it means neither `Thm29SecondAtDomains` nor `Thm29Normal` is a
weakening that could be criticised as restating the claim — they are the only
true readings.

## 3. Two false measurements in `LemThirty.lean`, corrected

Both were the stated justification for routing conjuncts through the refuted
hypothesis, and both are wrong on this branch.

**(a) `LemThirty.lean:346–355`** says "Measured over the whole library …
`Smash`, `CoalescedSum` and `SeparatedSum` have Lemma 10's bounded completeness
and Lemma 17's bifiniteness but **no algebraicity and no `Domain`**." False.
`PRepFun.smashIsAlgebraic`, `PRepFun.smashDomain`,
`PRepSum.isAlgebraic_coalescedSum` and `PRepSum.domain_coalescedSum` exist and
are proved; `ClosureProperties.SeparatedSum A B` is by definition
`CoalescedSum A⊥ B⊥`, so the third case is the second at `WithBot V`
(`PRepSum.lean:1053` already uses it that way at `Dyadic.U`).
`domain_smash_V`, `domain_coalSum_V`, `domain_sepSum_V` are the three
instantiations at `V`, each a one-line `exact`.

**(b) `LemThirty.lean:387–393`** says "`PRep.rep_lift` and `PRep.rep_prod` are
the only two of Lemma 28's nine schemes already proved". False: **seven** of the
nine exist — add `PRepFun.rep_arrow`, `PRepFun.rep_strictArrow`,
`PRepFun.rep_smash`, `PRepSum.rep_coalSum`, `PRepSum.rep_sepSum`. Only the three
powerdomain schemes are missing.

Together, (a) and (b) are why `⊗`, `+`, `⊕` never needed `Thm29Second`.
`retracts_smash_V`, `retracts_coalSum_V`, `retracts_sepSum_V` and
`rep_smash_V`, `rep_coalSum_V`, `rep_sepSum_V` take `Thm29SecondAtDomains`
instead — **one refuted hypothesis lighter**, and live rather than vacuous.

## 4. `→` and `⇸` are blocked, from the live hypothesis

`LemThirty.lean:107–110` argues `Thm29Second` and `BoundedComplete V` cannot both
hold. With `Thm29Second` refuted that argument proves nothing, so it is redone
from the hypothesis that survives:

    theorem not_boundedComplete_V (h : Thm29SecondAtDomains) : ¬ BoundedComplete V

The witness is the paper's own. `T × T` is a bounded complete domain
(`Flat.instDomainTT`, `Flat.instBoundedCompleteTT`), hence bifinite by
Proposition 15 (`isBifinite_plotkin_TT`), and `(T × T)♮` is a bifinite domain
that is not bounded complete (`Flat.not_boundedComplete_plotkin_TT`). Bounded
completeness transfers along a retraction —
`exists_isLUB_of_embeddingProjectionPair`, stated in existence form because
`BoundedComplete` constrains the carrier's own `sSup`, which a retraction says
nothing about.

So conjuncts 1 and 2 are unreachable in this development for as long as Theorem
29's second sentence is assumed, in either form. **This is a defect of the route
to `Domain (D → E)`** — through Theorem 7's step functions, which need bounded
completeness of the codomain — **not of Lemma 30**, which is a true statement
about the bifinite `V`. `ClosureProperties.lean` already calls the
`[BoundedComplete β]` in `lem17_fun` "a real open item, not a formality"; this
measures how much it costs: two of Lemma 30's ten conjuncts, unconditionally.

**Under the corrected criterion this also reclassifies two pre-existing
theorems.** `LemThirty.retracts_fun_of_boundedComplete` and
`retracts_strictFun_of_boundedComplete` carry both a hypothesis and an added
instance binder:

    theorem retracts_fun_of_boundedComplete (h : Colimit.Thm29Second)
        [BoundedComplete V] : Retracts (ScottHom V V)

That is "reduced at `[BoundedComplete V]`", never a discharge — and it is now
**doubly vacuous**: the hypothesis is refuted (§2), and `not_boundedComplete_V`
shows the added binder is incompatible with the weaker hypothesis that would have
replaced it. Neither theorem can ever be applied. They belong in the same
bookkeeping row as the other five vacuous consequences.

## 5. `LemThirty.Lemma30` is not a claim — reclassify the row

`scripts/a6-claims.txt` lists both `LemThirty.Lemma30` and
`LemThirty.Lemma30AtV`. `Lemma30` is

    def Lemma30 (W : Type u) [CompletePartialOrder W] : Prop

— a **parameterized family**, not a proposition. Under the corrected criterion,
discharging it means a theorem whose binders are exactly `(W : Type u)` and
`[CompletePartialOrder W]` — nothing added. Any proof would have to add
`[Domain W]`, `[BoundedComplete W]`, `IsBifinite W`, or fix `W := V`; every one
of those is an added binder, so the best attainable is "discharged at …", and at
`W := V` that is just `Lemma30AtV`, the row already on the list. The unadorned
claim `∀ W [CompletePartialOrder W], Lemma30 W` is not Lemma 30 and is false.
Counterexample by counting (argued, **not** kernel-checked): at
`W := Flat Bool`, every finitary projection `p ⊑ id` fixes `⊥` and maps each of
`T`, `F` to itself or `⊥`, so the four `FpImage`s have 1, 2, 2 and 3 elements;
`funOp (Flat Bool) (Flat Bool)` has 11 elements (9 with `f ⊥ = ⊥`, plus the two
constants), and 11 is not the size of any `FpImage`, so no `R` exists.

**The detector should count `Lemma30AtV` and drop `Lemma30`**, reducing the
project's undischarged-claim total by one for a reason that is a correction, not
a proof. The paper's Lemma 30 is a statement about §7.4's `V`.

## 6. `Thm29Normal`: open, and what is missing is now exact

`Thm29Normal` is the genuine unproved theorem of the cluster, and nothing in this
round closes it. What is missing, measured against `BifiniteUniversal.lean`:

* `MSub`, `MSub_finite`, `MSub_isNormalIn` and `isPlotkinOrder_MPair` build the
  stage tower and prove each stage normal in `A∞`
  (`Colimit.isNormalIn_range_incl`), and `LemThirty.exists_stage_ge_of_finite`
  shows the stages are already **cofinal** among finite subsets of `A∞`. So the
  stage-by-stage extension is not the gap, and the docstring saying so is right.
* What does not exist anywhere in the tree is a **universal property of `M`
  among finite posets under normal embedding**: given finite `N ◁ N' ◁ K(E)` and
  a normal embedding `N → Stg n`, produce `N' → Stg m` with `n ≤ m` commuting
  with both inclusions. Every declaration in `BifiniteUniversal.lean` is about
  `MPair A` for a *fixed* `A`; none is about maps between two different bases.
* Supplying that one extension step, plus the colimit of the resulting cone, is
  the whole of `Thm29Normal` — the reduction from there to Theorem 29's second
  sentence is already proved (`exists_embeddingProjectionPair_of_thm29Normal`,
  ~60 lines, kernel-checked). This is [Gun87]'s content and §7.4 defers it in
  full; it is a multi-round construction, not a round's work.

## 7. Per-claim status

| # | Claim | Status | Evidence |
| -- | ----- | ------ | -------- |
| 1 | `Colimit.Thm29Second` | **REFUTED** | `not_thm29Second`, `[propext, Classical.choice, Quot.sound]` |
| 2 | `Colimit.Lem30Arrow` | open, **and blocked** | `lem30Arrow_of_lemma30AtV`; blocked by `not_boundedComplete_V` — no route while Theorem 29's second sentence is assumed |
| 3 | `LemThirty.Thm29SecondAtDomains` | open — this **is** row 1 at `[Domain E]` | implied by `Thm29Normal` (already proved); not refutable by this round's argument, which needs an uncountable basis and so cannot meet `[Domain E]`. Proving it would be "discharged at `[Domain E]`" relative to row 1, and row 1 is false, so the binder is necessary |
| 4 | `LemThirty.Thm29Normal` | open; its binder-free version **refuted** | §6: missing input is `M`'s universal property among finite posets under normal embedding. `not_thm29NormalWithoutDomain` proves the `[Domain E]` in its own statement is load-bearing — the docstring claim at `:506–512` that nothing had proved |
| 5 | `LemThirty.Lemma30` | **not a claim** | parameterized family; universal closure false (§5). Reclassify, do not count |
| 6 | `LemThirty.Lemma30AtV` | open, **reduced** | conjuncts following from `Thm29Normal` went 2 → 5 (`five_conjuncts_of_thm29Normal`); 2 shown blocked; 3 waiting on agent4's powerdomain schemes |

Movement: **1 refuted, 1 reduced, 1 reclassified, 3 open with sharpened
obstructions**, plus a second refutation (`not_thm29NormalWithoutDomain`) of a
proposition that was not on the list but whose status the list depended on.
**Nothing was discharged and nothing was discharged at an added binder** —
neither could honestly be, because the cluster's content is `Thm29Normal`, which
is [Gun87]'s theorem.

## 8. Declarations added

All in `ScottDomains/A3Thm29.lean`, namespace `ScottDomains.R45.Agent3`.

| # | Declaration | Axioms |
| -- | ----------- | ------ |
| 1 | `isBifinite_flat` | `[propext, Classical.choice, Quot.sound]` |
| 2 | `isCompactElement_embedding` | `[propext, Quot.sound]` |
| 3 | `uncountable_setNat` | `[propext, Classical.choice, Quot.sound]` |
| 4 | `up_injective` | none |
| 5 | `uncountable_flat_setNat` | `[propext, Classical.choice, Quot.sound]` |
| 6 | `not_thm29Second` | `[propext, Classical.choice, Quot.sound]` |
| 6b | `Thm29NormalWithoutDomain` (`def`), `not_thm29NormalWithoutDomain` | `[propext, Classical.choice, Quot.sound]` |
| 7 | `lemma30AtV_iff` | `[propext, Classical.choice, Quot.sound]` |
| 8 | `lem30Arrow_iff` | `[propext, Classical.choice, Quot.sound]` |
| 9 | `lem30Arrow_of_lemma30AtV` | `[propext, Classical.choice, Quot.sound]` |
| 10 | `domain_smash_V`, `domain_coalSum_V`, `domain_sepSum_V` | `[propext, Classical.choice, Quot.sound]` |
| 11 | `retracts_smash_V`, `retracts_coalSum_V`, `retracts_sepSum_V` | `[propext, Classical.choice, Quot.sound]` |
| 12 | `rep_smash_V`, `rep_coalSum_V`, `rep_sepSum_V` | `[propext, Classical.choice, Quot.sound]` |
| 13 | `five_conjuncts_of_thm29Normal` | `[propext, Classical.choice, Quot.sound]` |
| 14 | `exists_isLUB_of_embeddingProjectionPair`, `isBifinite_plotkin_TT`, `not_boundedComplete_V` | `[propext, Quot.sound]` / `[propext, Classical.choice, Quot.sound]` |

## 9. For the orchestrator

1. `Colimit.Thm29Second`'s docstring says "Unproved." It should say **false**,
   and `PaperInventory.md` row 2f should record the refutation rather than the
   suspicion. That is a specification-level edit and belongs to you, not to a
   proving stream, so this round did not make it.
2. `LemThirty.lean`'s header table rows 4, 5, 6 and the two paragraphs at
   `:346–355` and `:387–393` are measurably false (§3). They should be rewritten
   against `A3Thm29.lean`, and `retracts_smash`, `retracts_sepSum`,
   `retracts_coalSum` should be deleted in favour of the `_V` forms.
3. `scripts/a6-claims.txt` should drop `LemThirty.Lemma30` (§5), so the round's
   re-derived total is one lower for a classification reason.
4. Nothing here collides with another stream: agent2 and agent4 work at `U` and
   on the powerdomain schemes, which this file only cites.
5. On the corrected criterion: `LemThirty.retracts_fun_of_boundedComplete` and
   `retracts_strictFun_of_boundedComplete` are "reduced at `[BoundedComplete V]`"
   and now doubly vacuous (§4). If the detector scores added instance binders,
   these two are the shape it should catch in this cluster — and
   `LemThirty.Thm29SecondAtDomains` is `Colimit.Thm29Second` at `[Domain E]`, so
   the two rows should be linked in `PaperInventory.md` rather than counted as
   unrelated claims.
