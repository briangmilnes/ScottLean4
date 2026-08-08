---
round: r0038
from: agent3
to: orchestrator
subject: audit-skeleton
date: 2026-0808-09:51
started: 2026-0808-09:39
finished: 2026-0808-09:51
related:
  - plans/r0038-plan-from-orchestrator-to-orchestrator-theorem-audit.md
  - docs/PropertiesVsTheorems.md
---

# r0038 — `Audit.Skeleton`: 170 declarations classified

Area: all of `Skeleton/` (6 files), all of `ClosureProperties*` (4 files), all of
`Isomorphism/` (6 files). 16 modules, 4783 lines.

## 0. Two measurements to record before the table

**The area holds 170 `theorem`/`lemma` declarations, not 172.**
`scripts/module-counts.sh` and `scripts/counts.sh` count a line matching
`^(@\[…\] )?(theorem|lemma) ` as a declaration. Two lines in this area match that
pattern inside a **module docstring**, where the word begins a wrapped sentence:

| # | File:line | The matched text |
| -- | --------- | ---------------- |
| 1 | `Skeleton/Recovered.lean:260` | `theorem on printed page 30: each `p ∈ M` has compact image, …` |
| 2 | `Skeleton/Section6.lean:176` | `theorem is due to Smyth and its proof may be found in [Smy83a]. …` |

Both are prose, not declarations. The counting rule therefore over-reports this
area by 2, and by extension over-reports the development's 1308. The rule is
cheap and its bias is known; this is the first measurement of the bias, and the
orchestrator should subtract at tier 2 rather than treat 1308 as exact. Every
count below is of the 170 real declarations.

**The `sorry` count is 1, not 2.** `scripts/counts.sh` at `702def0` reports one
`sorry`, at `Skeleton/Section6.lean:197` (`thm18`) — in this area. The r0035
restart note's "sorry 8 to 2" is stale; r0036 closed one more. No number moved in
this round: after adding `ScottDomains/Audit/Skeleton.lean` the build is 1224
jobs, zero errors, zero warnings, one `sorry`, and the theorem count moves
1308 → 1312 by exactly the four audit equations, which is the plan's authorized
exception.

## 1. Per-label totals

| # | Label | Count | Share of 170 |
| -- | ----- | ----- | ------------ |
| 1 | `P` — states a paper property | 32 | 18.8% |
| 2 | `S` — support, something cites it | 114 | 67.1% |
| 3 | `A` — projection / `simp` API | 17 | 10.0% |
| 4 | `U` — uncited, not a property, not API | **1** | 0.6% |
| 5 | `D` — duplicate | **6** (3 pairs) | 3.5% |
| 6 | `W` — over-declared strength | 0 as a primary label; **6 declarations carry surplus hypotheses**, §5 | — |
| — | **total** | **170** | |

**The answer to the round's question for this area: 1 of 170 declarations, 0.6%,
serves neither a paper property nor a proof of one.** That is below r0020's 3%.
The duplicates are a separate defect and are counted separately, because a `D`
row does serve a proof — the wrong copy of it.

`P` is dense here as predicted: 32 of the paper's 87 numbered conjuncts are
stated in these 16 modules — Lemma 10's 7, Lemma 17's 10, Lemma 9's 6, plus
Theorem 14, Proposition 15, Theorem 16, Theorem 18, Lemma 19, Lemma 20, the two
`_printed_false` negations, and the two whole-lemma conjunctions.

### Labelling rule used, stated so the orchestrator can re-derive a row

- `A` when the declaration's content is a definitional unfolding of another
  declaration — a `.1`/`.2` accessor, an `_apply`/`_coe`/`_bot` equation, or an
  `Iff.rfl` membership lemma. Whether it is `@[simp]` is given per row. 13 of the
  17 carry the tag; that matches `module-counts.sh`'s `simp` column for this area
  exactly (1+2+2+2+2+2+2).
- `S` when the declaration carries an argument and at least one declaration cites
  it. The evidence column names one citer, preferring a cross-module one.
- `P` beats `S` when both apply: the whole-lemma conjunctions `lemma10`/`lemma17`
  and the per-conjunct `lem10_*`/`lem17_*` are all paper properties in the plan's
  own sense ("a conjunct of a numbered result"), even though the conjunctions
  cite the conjuncts.

## 2. The question the orchestrator asked directly

> Check whether the per-conjunct theorems and the conjunction theorems duplicate
> each other, or whether the conjunction merely cites them.

**The conjunctions cite them. This is not duplication.** `ClosureProperties.lemma10`'s
entire proof term is the anonymous constructor applied to seven names:

    ⟨inferInstance, lem10_strict, lem10_prod, lem10_smash, lem10_separated, lem10_sum, lem10_lift⟩

and `lemma17`'s is the same shape over ten. Neither re-proves anything; each adds
exactly one thing, which its own docstring names correctly — *the conjunct count
becomes a type error rather than an absence*. That is worth its two declarations:
it is what caught `+` being read as a second name for `⊕`, and the three
powerdomain conjuncts being dropped with the `♮`/`♯`/`♭` glyphs.

**And `Skeleton/Sum.lean` does not duplicate `ClosureProperties/SeparatedSum.lean`.**
They address different operators. `Sum.lean` proves the `⊕` conjuncts
(`CoalescedSum`, Lemma 10 row 6 / Lemma 17 row 6) and the `⊗` conjunct of Lemma 17;
`SeparatedSum.lean` proves the `+` conjuncts (`SeparatedSum α β :=
CoalescedSum (WithBot α) (WithBot β)`, rows 5), by composing the lift conjunct
with the `⊕` conjunct. The paper's §4.4 defines `D + E` to *be* `D⊥ ⊕ E⊥`, so the
two are genuinely different claims and the second is two lines long.

The real duplication is elsewhere and the orchestrator's framing did not predict
it: it is between `Skeleton/Sum.lean` and `Isomorphism/`, §4.

## 3. `Isomorphism/Distribute.lean` and `Isomorphism/Smash.lean` — 0 theorems, 13 defs

Both files are asked about because a file with no theorem looks empty. It is not:
**these two files carry the proofs of four of Lemma 9's six conjuncts, and the
proofs are `def`s because the propositions are `Nonempty (_ ≃o _)`.**

`Skeleton/Recovered.lean` states Lemma 9 as six `Nonempty (X ≃o Y)` claims —
"Lemma 9 asserts that an isomorphism *exists*", so each conjunct is inhabitation
of an order-isomorphism type. An `≃o` is a structure with four fields
(`toFun`, `invFun`, `left_inv`/`right_inv`, `map_rel_iff'`): it is **data**, so
it is built by `def`, and the theorem is the one-line `⟨thatDef⟩`. The division of
labour is exact:

| # | File | Contributes | Consumed by |
| -- | ---- | ----------- | ----------- |
| 1 | `Isomorphism/Smash.lean` (6 defs) | `nonBotPairComm`, `smashComm`, `NonBotTriple`, `smashAssocLeft`, `smashAssocRight`, `smashAssoc` | `Recovered.lem9_1 := ⟨Isomorphism.smashComm⟩`, `lem9_2 := ⟨Isomorphism.smashAssoc⟩` |
| 2 | `Isomorphism/Distribute.lean` (7 defs) | `splitNonBotPair`, `joinNonBotPair`, `distribLeft`, `unsmashSum`, `resmashSum`, `distribRight`, `smashDistribCoalescedSum` | `Recovered.lem9_5 := ⟨Isomorphism.smashDistribCoalescedSum⟩` |

Neither file needs a theorem because neither needs a continuity obligation:
`Smash X Y = WithBot (NonBotPair X Y)` and `CoalescedSum X Y = WithBot (NonBotSum X Y)`,
so both laws are proved on the base and transported by `OrderIso.withBotCongr`,
and an `≃o` between cpos preserves every directed supremum for free. The four
`OrderIso` fields are discharged inside the `def` by `rfl`, `WithBot.coe_unbot`
and `WithBot.unbot_le_unbot_iff`.

Measured conclusion: **0 theorems is the correct count for both files, and
neither is a candidate for anything.** They are 323 lines carrying 3 of the
paper's 87 conjuncts. `Isomorphism/Lift.lean` (4 theorems) and
`Isomorphism/StrictCurry.lean` (10) have theorems only because their maps need
Scott continuity proved before the `≃o` can be assembled — `liftExtendFun` and
`smashPair` are not order isomorphisms on the nose.

## 4. `D` — three duplicate pairs, kernel-checked

`ScottDomains/Audit/Skeleton.lean` (new, 98 lines, 4 theorems, all `rfl`) converts
each claim into something the build checks. **Each equation is well-typed only if
the two declarations have definitionally equal statements**, which is the
duplicate claim; `rfl` then closes it by definitional proof irrelevance. The
module builds: `✔ Built ScottDomains.Audit.Skeleton`, 844 jobs, 0 errors,
0 warnings, 0 `sorry`.

| # | Statement | Copy A | Copy B | Audit equation |
| -- | --------- | ------ | ------ | -------------- |
| 1 | `IsLUB s ↑r → (sumBase s).Nonempty` | `ScottDomains.sumBase_nonempty_of_isLUB_coe`, `Skeleton/Sum.lean:357` | `ScottDomains.Isomorphism.sumBase_nonempty_of_isLUB_coe`, `Isomorphism/Copair.lean:236` | `sumBase_nonempty_of_isLUB_coe_dup` |
| 2 | `smashPair p = ↑⟨p,h⟩` | `ScottDomains.smashPair_of_ne_bot`, `Skeleton/Sum.lean:692` | `ScottDomains.Isomorphism.smashPair_of_ne`, `Isomorphism/StrictCurry.lean:137` | `smashPair_of_ne_bot_dup` |
| 3 | `smashPair p = ⊥` | `ScottDomains.smashPair_of_bot`, `Skeleton/Sum.lean:696` | `ScottDomains.Isomorphism.smashPair_of_bot`, `Isomorphism/StrictCurry.lean:140` | `smashPair_of_bot_dup` |

**Root cause of rows 2 and 3.** The two modules each define, under
`open Classical in`, the *same six tokens*:

    noncomputable def smashPair (p : α × β) : Smash α β :=
      if h : p.1 ≠ ⊥ ∧ p.2 ≠ ⊥ then ↑(⟨p, h⟩ : NonBotPair α β) else ⊥

`Skeleton/Sum.lean:689` and `Isomorphism/StrictCurry.lean:134`, character for
character, same `Classical.propDecidable` instance. `smashPair_dup` proves the
two functions equal by `rfl` — they are definitionally the same, not merely
extensionally equal. Every lemma about either is therefore a lemma about both.
Row 3 is the sharper case: the two carry **the same name** and only the namespace
separates them, which is precisely the r0028 failure mode
`docs/PropertiesVsTheorems.md` §5 item 2 records — invisible to `lake build`
because no module imports both halves. `Skeleton/Sum.lean` is imported by
`ClosureProperties*` and `PRepSum`; `Isomorphism/StrictCurry.lean` only by
`Skeleton/Recovered.lean`, which does not import `Skeleton/Sum`. Nothing in the
development imports both, so nothing has ever seen the clash. `Audit/Skeleton.lean`
now does, which is the point of adding it.

Row 1 is the same story at the coalesced sum, with different proof scripts:
`Sum.lean` argues by `rcases Set.eq_empty_or_nonempty`, `Copair.lean` by
`by_contra`. Same proposition, two proofs, two names.

**Recommendation (for the follow-on round, not acted on here).** Keep the
`Skeleton/Sum.lean` copies. They are the ones the rest of the development reaches:
`Skeleton/Sum.lean` is imported by `ClosureProperties.lean` and
`ClosureProperties/SeparatedSum.lean` and is in scope unqualified throughout
`PRepSum.lean`, whereas `Isomorphism/StrictCurry.lean` is imported by exactly one
module (`Skeleton/Recovered.lean`) and `Isomorphism/Copair.lean` by three. Have
`Isomorphism/Copair.lean` and `Isomorphism/StrictCurry.lean` import
`ScottDomains.Skeleton.Sum` and delete their re-declarations — `smashPair`,
`smashPair_of_ne`, `smashPair_of_bot`, `sumBase_nonempty_of_isLUB_coe`, and
`smashPair_mono` after rows 86–87 are derived from it. Cost: two import lines. The
import is acyclic: `Skeleton/Sum.lean` imports only `CoalescedSum`, `Smash`,
`Bifinite` and `Mathlib.Data.Finite.Prod`.

### Near-duplicates that are not `D` — repeated *proofs*, distinct statements

Four more places re-derive an argument that exists as a named lemma. None is a
duplicate declaration, so none is labelled `D`, but each is a place the
development pays twice:

| # | Re-derived at | Already available as | Why it was not cited |
| -- | ------------- | -------------------- | -------------------- |
| 1 | `Isomorphism/StrictCurry.lean:106–113` (inline `obtain … (smashBase s).Nonempty`) | `Skeleton/Sum.lean:799` `smashBase_nonempty_of_isLUB_coe` | `StrictCurry` does not import `Skeleton/Sum` |
| 2 | `Isomorphism/Lift.lean:90–97` (inline `hne' : (liftBase s).Nonempty`) | `Skeleton/Lemma17.lean:154` `liftBase_nonempty_of_isLUB` | `Isomorphism/Lift` does not import `Skeleton/Lemma17` |
| 3 | `Isomorphism/Copair.lean:65–103` — `sumInlFun`/`sumInrFun` with `_bot`, `_of_ne`, `_mono` | `Skeleton/Sum.lean:201–243` — `sumInl`/`sumInr` with `_bot`, `_of_ne_bot`, `monotone_` | same function, opposite `dite` polarity (`if h : x = ⊥ then ⊥ else …` against `if h : x ≠ ⊥ then … else ⊥`), so equal but **not** definitionally — this pair is not `rfl`-provable and is why it is not in the `D` table |
| 4 | `Skeleton/Lemma17.lean:406–450` (`lem17_fun`'s body) | `ClosureProperties/StrictFunction.lean:249` `exists_finite_projection_fixing` | the factoring was done but not applied — see below |

Row 4 is a documentation defect as well as a duplication. `exists_finite_projection_fixing`'s
docstring claims it exists "so that neither proof restates it", but `lem17_fun`
still contains the same 45-line script verbatim — `choose! S`, `choose! π`, `hK`,
`hE`, the two `_h` applications, `isProjection_compHom`, `finite_range_compHom`,
and the identical `by_cases hkx` calc block. `lem17_fun` does not cite
`exists_finite_projection_fixing`. Either the claim or the code should change.

**Row 3 is already known to the development, and already being paid for.**
`PRepSum.lean:472` and `:477` are two theorems that exist for no other purpose
than to reconcile the two names:

    theorem sumInlFun_eq_sumInl (x : A) : Isomorphism.sumInlFun (β := A) (γ := B) x = sumInl B x
    theorem sumInrFun_eq_sumInr (y : B) : Isomorphism.sumInrFun (β := A) (γ := B) y = sumInr A y

with the docstring "*`Skeleton/Sum.lean`'s `sumInl` and `Isomorphism/Copair.lean`'s
`sumInlFun` are the same function with the `dite` branches swapped. Recorded so
that the continuity proof written for one name serves the other, which is what
lets the compactness criterion (stated at `sumInl`) and the copairing construction
(stated at `sumInlFun`) be used in the same proof.*"

So the duplication is not merely latent: a downstream module has diagnosed it
correctly, and pays two bridge theorems plus a `rw` at every use site to work
around it. `PRepSum.lean` is **agent5's area**, so this is a cross-area
corroboration for the orchestrator at tier 2 — unifying the two injections
retires the six `Isomorphism/Copair.lean` re-declarations (rows 135–140) **and**
these two bridges, eight declarations in total, and removes the
`Isomorphism.sumInlFun_of_ne`/`sumInl_of_ne_bot` double rewrite from `PRepSum`.

## 5. `W` — six declarations state hypotheses their proofs never use

No declaration receives `W` as its primary label, because all six are Lemma 10's
conjuncts and `P` takes precedence; the finding is reported here instead so it is
not lost. The plan's `W` tell is "results proved at strictly weaker hypotheses
than declared", the `thm25`/`thm12` pattern from r0032 and r0034. This area has
that pattern across the whole of Lemma 10.

`Domain` and `BoundedComplete` are **independent** classes over
`[CompletePartialOrder α]` (`Domain.lean:128, 168`; `Domain extends IsAlgebraic`,
`BoundedComplete` does not). Every Lemma 10 conjunct is declared at
`[Domain _] [BoundedComplete _]` on each operand. No proof step uses algebraicity
or countability of the basis:

| # | Declaration | Declared | Proof actually uses | Surplus |
| -- | ----------- | -------- | ------------------- | ------- |
| 1 | `lem10_prod` | `[Domain α] [BoundedComplete α] [Domain β] [BoundedComplete β]` | `isLUB_sSup_of_bddAbove` on α and on β; `Prod`'s cpo instance (bare cpo) | `[Domain α]`, `[Domain β]` |
| 2 | `lem10_lift` | `[Domain α] [BoundedComplete α]` | `isLUB_sSup_of_bddAbove` on α; `liftSup_of_nonempty`/`_of_empty` | `[Domain α]` |
| 3 | `lem10_strict` | `[Domain α] [BoundedComplete α] [Domain β] [BoundedComplete β]` | `isLUB_sSup_of_bddAbove` on `ScottHom α β`, whose instance (`ScottHom.lean:286`) needs only `[BoundedComplete β]` | `[Domain α]`, `[BoundedComplete α]`, `[Domain β]` |
| 4 | `lem10_smash` | as row 1 | `lem10_prod`, `smashSup_of_ne_bot`, `smashSup_of_empty` | `[Domain _]`, but only once row 1 is fixed |
| 5 | `lem10_sum` | as row 1 | `isLUB_sSup_of_bddAbove` on the `leftParts`/`rightParts` of α and β | `[Domain α]`, `[Domain β]` |
| 6 | `lem10_separated` | as row 1 | `lem10_lift` then `lem10_sum`; `[Domain α]` **is** consumed, via `liftDomain`, only because row 5 demands it | cascades from row 5 |

Rows 4 and 6 are cascades: their `Domain` hypotheses are consumed only to satisfy
rows 1 and 5. Fixing rows 1, 2, 3 and 5 releases all six.

**Confidence, stated honestly.** This is read off the proof terms and the class
declarations, **not kernel-checked**, because confirming it means deleting a
hypothesis from a live declaration and rebuilding — an edit this round forbids.
Treat it as a measured conjecture with a one-command test in the follow-on round.

**It is not a defect in the statement.** The paper says "bounded complete
*domains*", and `ClosureProperties.lean`'s docstring is right that `[Domain _]
[BoundedComplete _]` renders that sentence. The theorem as declared is faithful
and true. What the measurement shows is that the *development* proves more than
the paper claims, and that Lemma 10 holds for bounded complete cpos that are not
domains — which is a fact about the paper worth recording rather than a fault.

## 6. `U` — the one declaration serving nothing

| # | Declaration | Module:line | `@[simp]` | Evidence |
| -- | ----------- | ----------- | --------- | -------- |
| 1 | `strictHom_val_of_isStrict` | `ClosureProperties/StrictFunction.lean:144` | no | Occurs **once** in the whole `.lean` corpus — its own declaration. On `scripts/unused-theorems.sh`'s list. Untagged, so `simp` cannot fire it unnamed, which removes the script's stated escape hatch. |

What it was written for is recoverable from its docstring: "`σ` fixes the strict
functions: that is what makes it a retraction onto `D →⊥ E` and not merely a
monotone map into it." That is true and it is the conceptual justification for
`strictHom`, but no proof consumes it — `lem17_strictFun` reaches its goal through
`isStrict_compHom` and `exists_finite_projection_fixing`'s `hfix`, never through
the retraction property. Population 3 of `PropertiesVsTheorems.md` §4: API written
for a caller that never appeared.

**Recommendation:** the r0020 treatment — comment out in place with a note saying
it records why `strictHom` is a retraction, rebuild, confirm the build is
unchanged. It is not `@[simp]`, so the r0020 surprise (a tagged lemma that had
never been firing) cannot arise here.

## 7. The full table — 170 rows

Columns: declaration, module, label, evidence. `§` references are to Gunter &
Scott 1990 and were checked against the rendered PDF, not taken from the
docstring (see §8).

### `ClosureProperties.lean` — 2

| # | Declaration | Module | Label | Evidence |
| -- | ----------- | ------ | ----- | -------- |
| 1 | `lemma10` | `ClosureProperties.lean` | `P` | §4.5 Lemma 10, all 7 conjuncts as one conjunction. Paper printed p.22 verified: `D → E, D →⊥ E, D × E, D ⊗ E, D + E, D ⊕ E, D⊥` = 7. Cited only in prose (`PRepSum.lean:57`); terminal by design |
| 2 | `lemma17` | `ClosureProperties.lean` | `P` | §6.2 Lemma 17, all 10 conjuncts. Paper printed p.32 verified: 7 above plus `D♮, D♯, D♭` = 10. Cited only in prose (`LemThirty.lean:88`) |

### `Skeleton/Lemma10.lean` — 9

| # | Declaration | Module | Label | Evidence |
| -- | ----------- | ------ | ----- | -------- |
| 3 | `bddAbove_fst_image` | `Skeleton/Lemma10.lean` | `S` | cited by `lem10_prod` (line 80) |
| 4 | `bddAbove_snd_image` | `Skeleton/Lemma10.lean` | `S` | cited by `lem10_prod` (line 81) |
| 5 | `lem10_prod` | `Skeleton/Lemma10.lean` | `P` | §4.5 Lemma 10 conjunct 3, `D × E`. Cited by `ClosureProperties.lemma10`, `lem10_smash`, `PRepSum.lean`. See §5 row 1 |
| 6 | `exists_coe_of_mem_upperBounds_smash` | `Skeleton/Lemma10.lean` | `S` | cited by `lem10_smash` (lines 121, 139) |
| 7 | `lem10_smash` | `Skeleton/Lemma10.lean` | `P` | Lemma 10 conjunct 4, `D ⊗ E`. Cited by `ClosureProperties.lemma10`, `Isomorphism/Counterexample.lean`, `Lemma28AtU.lean`. See §5 row 4 |
| 8 | `bddAbove_liftBase` | `Skeleton/Lemma10.lean` | `S` | cited by `lem10_lift` (line 187) |
| 9 | `exists_coe_of_mem_upperBounds` | `Skeleton/Lemma10.lean` | `S` | cited by `lem10_lift` (lines 185, 195), `Skeleton/Sum.lean` |
| 10 | `lem10_lift` | `Skeleton/Lemma10.lean` | `P` | Lemma 10 conjunct 7, `D⊥`. Cited by `ClosureProperties.lemma10`, `SeparatedSum.lem10_separated`, `PRepSum.lean`. See §5 row 2 |
| 11 | `lem10_strict` | `Skeleton/Lemma10.lean` | `P` | Lemma 10 conjunct 2, `D →⊥ E`. Cited by `ClosureProperties.lemma10`, `Lemma28AtU.lean`, `PRepFun.lean`. See §5 row 3 |

### `Skeleton/Lemma17.lean` — 22

| # | Declaration | Module | Label | Evidence |
| -- | ----------- | ------ | ----- | -------- |
| 12 | `directedOn_image_mk_right` | `Skeleton/Lemma17.lean` | `S` | cited by `isCompactElement_prod_iff` (line 80) |
| 13 | `directedOn_image_mk_left` | `Skeleton/Lemma17.lean` | `S` | cited by `isCompactElement_prod_iff` (line 86) |
| 14 | `isLUB_image_mk_right` | `Skeleton/Lemma17.lean` | `S` | cited by `isCompactElement_prod_iff` (line 80) |
| 15 | `isLUB_image_mk_left` | `Skeleton/Lemma17.lean` | `S` | cited by `isCompactElement_prod_iff` (line 86) |
| 16 | `isCompactElement_prod_iff` | `Skeleton/Lemma17.lean` | `S` | `K(D×E)=K(D)×K(E)`, elided by the paper. Cited by `lem17_prod`, `Powerdomain/Universal.lean:209,442` |
| 17 | `lem17_prod` | `Skeleton/Lemma17.lean` | `P` | §6.2 Lemma 17 conjunct 3, `D × E`. Cited by `ClosureProperties.lemma17`, `LemThirty.lean`, `Skeleton/Sum.lean` |
| 18 | `isLUB_liftBase` | `Skeleton/Lemma17.lean` | `S` | cited by `isCompactElement_coe_iff` (line 197) |
| 19 | `liftBase_nonempty_of_isLUB` | `Skeleton/Lemma17.lean` | `S` | cited by `isCompactElement_coe_iff` (line 196). Re-derived inline at `Isomorphism/Lift.lean:90` — §4 near-duplicate 2 |
| 20 | `directedOn_image_coe` | `Skeleton/Lemma17.lean` | `S` | cited by `isCompactElement_coe_iff` (line 189) |
| 21 | `isLUB_image_coe` | `Skeleton/Lemma17.lean` | `S` | cited by `isCompactElement_coe_iff` (line 189) |
| 22 | `isCompactElement_coe_iff` | `Skeleton/Lemma17.lean` | `S` | `K(D⊥)={⊥}∪↑K(D)`, elided by the paper. Cited by `lem17_lift`, `SeparatedSum.compactsBelow_coe`, `SeparatedSum.compacts_withBot_subset` |
| 23 | `lem17_lift` | `Skeleton/Lemma17.lean` | `P` | Lemma 17 conjunct 7, `D⊥`. Cited by `ClosureProperties.lemma17`, `SeparatedSum.lem17_separated`, `LemThirty.lean` |
| 24 | `exists_greatest_of_finite_directedOn` | `Skeleton/Lemma17.lean` | `S` | cited by `isCompactElement_of_mem_range_of_finite` (line 277), `ClosureProperties/Powerdomain.lean:129` |
| 25 | `isCompactElement_of_mem_range_of_finite` | `Skeleton/Lemma17.lean` | `S` | cited by `isNormalIn_range_of_finite` (line 293), `ClosureProperties/StrictFunction.lean:331`, `SFP.lean` |
| 26 | `isNormalIn_range_of_finite` | `Skeleton/Lemma17.lean` | `S` | cited by `lem17_fun` (line 431) |
| 27 | `finite_range_normalHom` | `Skeleton/Lemma17.lean` | `S` | cited by `lem17_fun` (line 428), `ClosureProperties/StrictFunction.lean:278` |
| 28 | `compFun_apply` | `Skeleton/Lemma17.lean` | `A` | `@[simp]`, `rfl`. Uncited by name (on `unused-theorems.sh`'s list); unfolds `compFun` |
| 29 | `scottContinuous_compFun` | `Skeleton/Lemma17.lean` | `S` | cited by the `compHom` def (line 346) |
| 30 | `compHom_apply` | `Skeleton/Lemma17.lean` | `A` | `@[simp]`, `rfl`. Uncited by name (on `unused-theorems.sh`'s list); unfolds `compHom` |
| 31 | `isProjection_compHom` | `Skeleton/Lemma17.lean` | `S` | cited by `lem17_fun` (426), `ClosureProperties/StrictFunction.lean:276,326`, `PRepFun.lean`, `UniversalDomain.lean` |
| 32 | `finite_range_compHom` | `Skeleton/Lemma17.lean` | `S` | cited by `lem17_fun` (428), `ClosureProperties/StrictFunction.lean:278` |
| 33 | `lem17_fun` | `Skeleton/Lemma17.lean` | `P` | Lemma 17 conjunct 1, `D → E` — §6's substantive conjunct. Cited by `ClosureProperties.lemma17`, `LemThirty.lean`, `Colimit.lean`. Proof body duplicated — §4 near-duplicate 4 |

### `Skeleton/Recovered.lean` — 7

| # | Declaration | Module | Label | Evidence |
| -- | ----------- | ------ | ----- | -------- |
| 34 | `lem9_1` | `Skeleton/Recovered.lean` | `P` | §4 Lemma 9.1, `D ⊗ E ≅ E ⊗ D`. Witness `Isomorphism.smashComm`. Terminal by design |
| 35 | `lem9_2` | `Skeleton/Recovered.lean` | `P` | Lemma 9.2, `(D ⊗ E) ⊗ F ≅ D ⊗ (E ⊗ F)`. Witness `Isomorphism.smashAssoc`. Terminal |
| 36 | `lem9_3` | `Skeleton/Recovered.lean` | `P` | Lemma 9.3 **corrected** to `(E ⊕ F) ◦→ D ≅ (E ◦→ D) × (F ◦→ D)`. Witness `Isomorphism.coalescedSumCopair`. Printed form refuted by row 152 |
| 37 | `lem9_4` | `Skeleton/Recovered.lean` | `P` | Lemma 9.4, strict currying. Witness `Isomorphism.smashCurry`. Terminal |
| 38 | `lem9_5` | `Skeleton/Recovered.lean` | `P` | Lemma 9.5 **corrected** to `D ⊗ (E ⊕ F) ≅ (D ⊗ E) ⊕ (D ⊗ F)`. Witness `Isomorphism.smashDistribCoalescedSum`. Printed form refuted by row 156 |
| 39 | `lem9_6` | `Skeleton/Recovered.lean` | `P` | Lemma 9.6, `D⊥ ◦→ E ≅ D → E`. Witness `Isomorphism.liftStrictHomIso`. Terminal |
| 40 | `thm14` | `Skeleton/Recovered.lean` | `P` | §4 Theorem 14, both directions as one `↔`. Proof `SFP.thm14_forward`/`thm14_converse`. Cited in prose by `SFP.lean` |

### `Skeleton/Section6.lean` — 12

| # | Declaration | Module | Label | Evidence |
| -- | ----------- | ------ | ----- | -------- |
| 41 | `IsClosure.idem` | `Skeleton/Section6.lean` | `A` | not `@[simp]`; accessor `h.1 x` for the `IsClosure` conjunction. 26 external mentions: `CombinatorRep.lean`, `NormalProjection.lean`, `Powerdomain/Universal.lean` |
| 42 | `IsClosure.le_apply` | `Skeleton/Section6.lean` | `A` | not `@[simp]`; accessor `h.2 x`. 13 external mentions incl. `FinitaryProjectionPoset.lean` |
| 43 | `IsClosure.apply_of_mem_range` | `Skeleton/Section6.lean` | `S` | carries an `obtain`; 51 external mentions — the most-cited declaration in the area. `ClosureProperties/StrictFunction.lean`, `ContinuousConstruction.lean`, `FinitaryProjectionEmbedding.lean` |
| 44 | `exists_upperBound_mem_of_finite` | `Skeleton/Section6.lean` | `S` | the paper's own step "Since `M` is directed, there is some `z ∈ M` …". Cited by `isCompactElement_of_isLUB_finite` (125), `FinitaryProjectionEmbedding.lean` |
| 45 | `mem_lubClosure` | `Skeleton/Section6.lean` | `A` | `@[simp]`, `Iff.rfl`. Uncited by name (on `unused-theorems.sh`'s list); `prop15` uses the anonymous-constructor form directly. Tag may or may not be firing — worth the r0020 tag-removal check |
| 46 | `isCompactElement_of_isLUB_finite` | `Skeleton/Section6.lean` | `S` | the first paragraph of the paper's Prop 15 proof, as a step. Cited by `prop15` (152) |
| 47 | `prop15` | `Skeleton/Section6.lean` | `P` | §6.2 Proposition 15, "A bounded complete domain is bifinite." Paper printed p.31 verified. Cited by `Section62.lean`, `Skeleton/Recovered.lean` |
| 48 | `thm18` | `Skeleton/Section6.lean` | `P` | §6.2 Theorem 18, "If `D` and `D → D` are domains, then `D` is bifinite." Paper printed p.32 verified — stated with **no proof**, referred to [Smy83a]. **Carries the development's only `sorry`** (line 197). Cited by `JungFinite.lean`, `Section62.lean` |
| 49 | `IsClosure.isLUB_range` | `Skeleton/Section6.lean` | `S` | cited by `IsClosure.rangeCompletePartialOrder` (243), `FinitaryProjectionPoset.lean` |
| 50 | `lem19` | `Skeleton/Section6.lean` | `P` **at reduced strength** | §7.1 Lemma 19, paper printed p.33: "If `D` is a domain and `r ∘ r = r ⊒ id`, then `im(r)` is a **domain**." This declaration drops `[Domain α]` and concludes only `∃ _ : CompletePartialOrder ↥(Set.range ⇑r), True` — a *cpo*, not a domain. Full strength is `FinitaryProjectionPoset.IsClosure.domain_range:282`, which `Section6b.lean:91` names as "Lemma 19 at full strength". So the paper's conjunct is stated twice, once weakly here and once fully in agent2's area — a **cross-area pair the orchestrator should merge at tier 2** |
| 51 | `IsClosure.apply_sSup_of_directed` | `Skeleton/Section6.lean` | `S` | cited by `FinitaryProjectionPoset.lean`, `Projection.lean`, `UniversalDomain.lean` |
| 52 | `isClosure_sSup` | `Skeleton/Section6.lean` | `S` | cited by `FinitaryProjectionPoset.lean`, `PRep.lean`, `RecursiveDomain.lean`; named by `Section6b.lean:90` as `lem20`'s ingredient |

### `Skeleton/Section6b.lean` — 2

| # | Declaration | Module | Label | Evidence |
| -- | ----------- | ------ | ----- | -------- |
| 53 | `thm16` | `Skeleton/Section6b.lean` | `P` | §6.2 Theorem 16, **first conjunct only** ("`Fp(D)` is an algebraic lattice"). Paper printed p.32 verified: the sentence has 2 conjuncts. The second (the inclusion `i : Fp(D) ↪ (D → D)` is an embedding) is deliberately not stated because r0032 refuted it — `FinitaryProjectionEmbedding.lean`. Cited by `FinitaryProjectionEmbedding.lean`, `Section62.lean` |
| 54 | `lem20` | `Skeleton/Section6b.lean` | `P` | §7.1 Lemma 20, "If `D` is a domain, then `Fc(D)` is a cpo." Paper printed p.33 verified. Terminal by design — 0 external mentions |

### `Skeleton/Sum.lean` — 43

| # | Declaration | Module | Label | Evidence |
| -- | ----------- | ------ | ----- | -------- |
| 55 | `exists_inl_of_le_inl` | `Skeleton/Sum.lean` | `S` | cited in-file (144, 149, 379, 473), `PRepSum.lean` |
| 56 | `exists_inl_of_inl_le` | `Skeleton/Sum.lean` | `S` | cited in-file (302, 467), `PRepSum.lean` |
| 57 | `exists_inr_of_le_inr` | `Skeleton/Sum.lean` | `S` | cited in-file (156, 161, 413, 516), `PRepSum.lean` |
| 58 | `exists_inr_of_inr_le` | `Skeleton/Sum.lean` | `S` | cited in-file (330, 510), `PRepSum.lean` |
| 59 | `ne_bot_of_val_eq_inl` | `Skeleton/Sum.lean` | `S` | cited in-file (388, 545, 615, 667), `PRepSum.lean` |
| 60 | `ne_bot_of_val_eq_inr` | `Skeleton/Sum.lean` | `S` | cited in-file (422, 549, 643, 675), `PRepSum.lean` |
| 61 | `exists_coe_of_mem_upperBounds_sum` | `Skeleton/Sum.lean` | `S` | cited by `lem10_sum` (137); in-file only |
| 62 | `lem10_sum` | `Skeleton/Sum.lean` | `P` | §4.5 Lemma 10 conjunct 6, `D ⊕ E`. Cited by `ClosureProperties.lemma10`, `SeparatedSum.lem10_separated`, `CoalescedSum.lean`. See §5 row 5 |
| 63 | `isLUB_diff_bot` | `Skeleton/Sum.lean` | `S` | cited by `isCompactElement_coe_inl_iff` (448), `_inr_iff` (491), `_smash_iff` (848, 863), `PRepSum.lean` |
| 64 | `sumInl_of_ne_bot` | `Skeleton/Sum.lean` | `S` | 16 in-file mentions, `PRepSum.lean`. Re-declared as `Isomorphism.sumInlFun_of_ne` — §4 near-duplicate 3 |
| 65 | `sumInr_of_ne_bot` | `Skeleton/Sum.lean` | `S` | mirror of row 64; re-declared as `Isomorphism.sumInrFun_of_ne` |
| 66 | `sumInl_bot` | `Skeleton/Sum.lean` | `A` | `@[simp]`; 10 external mentions (`PRepSum.lean`). Re-declared as `Isomorphism.sumInlFun_bot` (untagged) — §4 near-duplicate 3 |
| 67 | `sumInr_bot` | `Skeleton/Sum.lean` | `A` | `@[simp]`; mirror of row 66 |
| 68 | `monotone_sumInl` | `Skeleton/Sum.lean` | `S` | cited in-file (275, 293), `PRepSum.lean`. Re-declared as `Isomorphism.sumInlFun_mono` |
| 69 | `monotone_sumInr` | `Skeleton/Sum.lean` | `S` | mirror of row 68 |
| 70 | `injective_sumInl` | `Skeleton/Sum.lean` | `S` | cited by `lem17_sum` (565) |
| 71 | `injective_sumInr` | `Skeleton/Sum.lean` | `S` | cited by `lem17_sum` (567) |
| 72 | `directedOn_image_sumInl` | `Skeleton/Sum.lean` | `S` | cited by `isCompactElement_coe_inl_iff` (456) |
| 73 | `directedOn_image_sumInr` | `Skeleton/Sum.lean` | `S` | cited by `isCompactElement_coe_inr_iff` (499) |
| 74 | `isLUB_image_sumInl` | `Skeleton/Sum.lean` | `S` | cited by `isCompactElement_coe_inl_iff` (457), `CombinatorRep.lean` |
| 75 | `isLUB_image_sumInr` | `Skeleton/Sum.lean` | `S` | cited by `isCompactElement_coe_inr_iff` (500), `CombinatorRep.lean` |
| 76 | `exists_coe_of_coe_le` | `Skeleton/Sum.lean` | `S` | cited in-file (464, 507, 598), `PRepSum.lean` |
| 77 | `sumBase_nonempty_of_isLUB_coe` | `Skeleton/Sum.lean` | **`D`** | same statement as `Isomorphism.sumBase_nonempty_of_isLUB_coe` (`Isomorphism/Copair.lean:236`); kernel-checked by `Audit/Skeleton.lean`'s `sumBase_nonempty_of_isLUB_coe_dup`. This copy cited in-file (373, 407, 469, 512) — **keep this one** |
| 78 | `isLUB_leftParts_of_isLUB` | `Skeleton/Sum.lean` | `S` | cited by `isCompactElement_coe_inl_iff` (477), `CombinatorRep.lean` |
| 79 | `isLUB_rightParts_of_isLUB` | `Skeleton/Sum.lean` | `S` | cited by `isCompactElement_coe_inr_iff` (520), `CombinatorRep.lean` |
| 80 | `isCompactElement_coe_inl_iff` | `Skeleton/Sum.lean` | `S` | `K(D⊕E)` characterization, elided by the paper. Cited by `lem17_sum` (575, 589), `PRepSum.lean` |
| 81 | `isCompactElement_coe_inr_iff` | `Skeleton/Sum.lean` | `S` | mirror of row 80. Cited by `lem17_sum` (583, 590), `PRepSum.lean` |
| 82 | `finite_sumNormal` | `Skeleton/Sum.lean` | `S` | cited by `lem17_sum` (586) |
| 83 | `lem17_sum` | `Skeleton/Sum.lean` | `P` | §6.2 Lemma 17 conjunct 6, `D ⊕ E`. Cited by `ClosureProperties.lemma17`, `SeparatedSum.lem17_separated`, `LemThirty.lean` |
| 84 | `smashPair_of_ne_bot` | `Skeleton/Sum.lean` | **`D`** | same statement as `Isomorphism.smashPair_of_ne` (`StrictCurry.lean:137`); kernel-checked by `smashPair_of_ne_bot_dup`. 16 in-file mentions — **keep this one** |
| 85 | `smashPair_of_bot` | `Skeleton/Sum.lean` | **`D`** | same **name** and statement as `Isomorphism.smashPair_of_bot` (`StrictCurry.lean:140`); kernel-checked by `smashPair_of_bot_dup`. The r0028 failure mode — **keep this one** |
| 86 | `monotone_smashPair_left` | `Skeleton/Sum.lean` | `S` | cited by `directedOn_image_smashPair_left` (730), `isLUB_image_smashPair_left` (748). Strictly weaker than `Isomorphism.smashPair_mono`, which proves joint monotonicity |
| 87 | `monotone_smashPair_right` | `Skeleton/Sum.lean` | `S` | mirror of row 86; same note |
| 88 | `directedOn_image_smashPair_left` | `Skeleton/Sum.lean` | `S` | cited by `isCompactElement_coe_smash_iff` (855) |
| 89 | `directedOn_image_smashPair_right` | `Skeleton/Sum.lean` | `S` | cited by `isCompactElement_coe_smash_iff` (870) |
| 90 | `isLUB_image_smashPair_left` | `Skeleton/Sum.lean` | `S` | cited by `isCompactElement_coe_smash_iff` (856) |
| 91 | `isLUB_image_smashPair_right` | `Skeleton/Sum.lean` | `S` | cited by `isCompactElement_coe_smash_iff` (871) |
| 92 | `exists_coe_of_coe_le_smash` | `Skeleton/Sum.lean` | `S` | cited in-file (877, 950) |
| 93 | `smashBase_nonempty_of_isLUB_coe` | `Skeleton/Sum.lean` | `S` | cited by `isLUB_val_smashBase_of_isLUB` (814), `isCompactElement_coe_smash_iff` (879). Re-derived inline at `Isomorphism/StrictCurry.lean:106` — §4 near-duplicate 1 |
| 94 | `isLUB_val_smashBase_of_isLUB` | `Skeleton/Sum.lean` | `S` | cited by `isCompactElement_coe_smash_iff` (884) |
| 95 | `isCompactElement_coe_smash_iff` | `Skeleton/Sum.lean` | `S` | `K(D⊗E)` characterization, elided by the paper. Cited by `lem17_smash` (928, 942, 953) |
| 96 | `finite_smashNormal` | `Skeleton/Sum.lean` | `S` | cited by `lem17_smash` (939) |
| 97 | `lem17_smash` | `Skeleton/Sum.lean` | `P` | §6.2 Lemma 17 conjunct 4, `D ⊗ E` — omitted from the r0026 skeleton by oversight. Cited by `ClosureProperties.lemma17`, `LemThirty.lean`, `PRepFun.lean` |

### `ClosureProperties/SeparatedSum.lean` — 5

| # | Declaration | Module | Label | Evidence |
| -- | ----------- | ------ | ----- | -------- |
| 98 | `compactsBelow_bot_withBot` | `ClosureProperties/SeparatedSum.lean` | `S` | cited by the `liftIsAlgebraic` instance (82, 97) |
| 99 | `compactsBelow_coe` | `ClosureProperties/SeparatedSum.lean` | `S` | cited by `liftIsAlgebraic` (86, 100) |
| 100 | `compacts_withBot_subset` | `ClosureProperties/SeparatedSum.lean` | `S` | cited by the `liftDomain` instance (129), `PRepSum.lean` |
| 101 | `lem10_separated` | `ClosureProperties/SeparatedSum.lean` | `P` | §4.5 Lemma 10 conjunct 5, `D + E`; §4.4 defines `D + E := D⊥ ⊕ E⊥`. Cited by `ClosureProperties.lemma10`, `PRepSum.lean`. See §5 row 6 |
| 102 | `lem17_separated` | `ClosureProperties/SeparatedSum.lean` | `P` | §6.2 Lemma 17 conjunct 5, `D + E`. Cited by `ClosureProperties.lemma17`, `LemThirty.lean` |

### `ClosureProperties/StrictFunction.lean` — 16

| # | Declaration | Module | Label | Evidence |
| -- | ----------- | ------ | ----- | -------- |
| 103 | `strictFun_bot` | `ClosureProperties/StrictFunction.lean` | `A` | `@[simp]`; 9 in-file mentions, 0 external |
| 104 | `strictFun_of_ne_bot` | `ClosureProperties/StrictFunction.lean` | `S` | 13 in-file mentions |
| 105 | `strictFun_le` | `ClosureProperties/StrictFunction.lean` | `S` | cited by `strictHom_val_le` (130) |
| 106 | `monotone_strictFun` | `ClosureProperties/StrictFunction.lean` | `S` | cited by `scottContinuous_strictFun` (105) |
| 107 | `scottContinuous_strictFun` | `ClosureProperties/StrictFunction.lean` | `S` | cited by the `strictHom` def (125) |
| 108 | `strictHom_apply` | `ClosureProperties/StrictFunction.lean` | `A` | `@[simp]`, `rfl`; cited in-file (149, 151) |
| 109 | `strictHom_val_le` | `ClosureProperties/StrictFunction.lean` | `S` | cited by `isCompactElement_val_of_isCompactElement` (225) |
| 110 | `monotone_strictHom` | `ClosureProperties/StrictFunction.lean` | `S` | cited by `isCompactElement_val_of_isCompactElement` (198, 202) |
| 111 | `strictHom_val_of_isStrict` | `ClosureProperties/StrictFunction.lean` | **`U`** | occurs once in the whole corpus — its own declaration. Not `@[simp]`. §6 |
| 112 | `isLUB_val_image_of_isLUB` | `ClosureProperties/StrictFunction.lean` | `S` | 22 external mentions: `CombinatorRep.lean`, `Powerdomain/Universal.lean`, `PRepFun.lean` |
| 113 | `isCompactElement_of_isCompactElement_val` | `ClosureProperties/StrictFunction.lean` | `S` | cited by `lem17_strictFun` (330), `PRepFun.lean` |
| 114 | `isCompactElement_val_of_isCompactElement` | `ClosureProperties/StrictFunction.lean` | `S` | cited by `lem17_strictFun` (323), `PRepFun.lean` |
| 115 | `normalHom_bot` | `ClosureProperties/StrictFunction.lean` | `S` | cited by `exists_finite_projection_fixing` (277) |
| 116 | `isStrict_compHom` | `ClosureProperties/StrictFunction.lean` | `S` | cited by `lem17_strictFun` (333, 336), `PRepFun.lean` |
| 117 | `exists_finite_projection_fixing` | `ClosureProperties/StrictFunction.lean` | `S` | cited by `lem17_strictFun` (325). Its docstring's claim that the factoring stops `lem17_fun` restating the script is **not met** — §4 near-duplicate 4 |
| 118 | `lem17_strictFun` | `ClosureProperties/StrictFunction.lean` | `P` | §6.2 Lemma 17 conjunct 2, `D →⊥ E`. Cited by `ClosureProperties.lemma17`, `LemThirty.lean`, `PRepFun.lean` |

### `ClosureProperties/Powerdomain.lean` — 16

| # | Declaration | Module | Label | Evidence |
| -- | ----------- | ------ | ----- | -------- |
| 119 | `isNormalIn_image_principal` | `ClosureProperties/Powerdomain.lean` | `S` | cited by `isBifinite_idealCompletion` (107) |
| 120 | `isBifinite_idealCompletion` | `ClosureProperties/Powerdomain.lean` | `S` | cited by all three conjuncts: `lem17_hoare` (209), `lem17_smyth` (267), `lem17_plotkin` (329) |
| 121 | `exists_greatest_mem_normal` | `ClosureProperties/Powerdomain.lean` | `S` | cited by the `normalGreatest` def (136) and its three `choose_spec` lemmas (140, 144, 148) |
| 122 | `normalGreatest_mem` | `ClosureProperties/Powerdomain.lean` | `S` | cited by all three `selectsGreatest_*` (192, 255, 313) |
| 123 | `normalGreatest_le` | `ClosureProperties/Powerdomain.lean` | `S` | cited by all three `selectsGreatest_*` (195, 258, 315, 317) |
| 124 | `le_normalGreatest` | `ClosureProperties/Powerdomain.lean` | `S` | cited by all three `selectsGreatest_*` (200, 262, 321, 324) |
| 125 | `finite_preimage_val` | `ClosureProperties/Powerdomain.lean` | `S` | cited by all three `finite_*BasisOf` (176, 240, 296) |
| 126 | `finite_hoareBasisOf` | `ClosureProperties/Powerdomain.lean` | `S` | cited by `lem17_hoare` (218) |
| 127 | `selectsGreatest_hoareBasisOf` | `ClosureProperties/Powerdomain.lean` | `S` | cited by `lem17_hoare` (218) |
| 128 | `lem17_hoare` | `ClosureProperties/Powerdomain.lean` | `P` | §6.2 Lemma 17 conjunct 10, `D♭`. Cited by `ClosureProperties.lemma17`, `LemThirty.lean` |
| 129 | `finite_smythBasisOf` | `ClosureProperties/Powerdomain.lean` | `S` | cited by `lem17_smyth` (276) |
| 130 | `selectsGreatest_smythBasisOf` | `ClosureProperties/Powerdomain.lean` | `S` | cited by `lem17_smyth` (276) |
| 131 | `lem17_smyth` | `ClosureProperties/Powerdomain.lean` | `P` | §6.2 Lemma 17 conjunct 9, `D♯`. Cited by `ClosureProperties.lemma17`, `LemThirty.lean` |
| 132 | `finite_plotkinBasisOf` | `ClosureProperties/Powerdomain.lean` | `S` | cited by `lem17_plotkin` (336) |
| 133 | `selectsGreatest_plotkinBasisOf` | `ClosureProperties/Powerdomain.lean` | `S` | cited by `lem17_plotkin` (337) |
| 134 | `lem17_plotkin` | `ClosureProperties/Powerdomain.lean` | `P` | §6.2 Lemma 17 conjunct 8, `D♮` — the case the paper writes out. Cited by `ClosureProperties.lemma17`, `LemThirty.lean` |

### `Isomorphism/Copair.lean` — 14

| # | Declaration | Module | Label | Evidence |
| -- | ----------- | ------ | ----- | -------- |
| 135 | `sumInlFun_bot` | `Isomorphism/Copair.lean` | `A` | not `@[simp]`; `dif_pos rfl`. Cited by the `sumInl` def (211), `restrictLeft` (417), `coalescedSumCopair` (454). Re-declares `Skeleton/Sum.lean`'s `sumInl_bot` — §4 near-duplicate 3 |
| 136 | `sumInrFun_bot` | `Isomorphism/Copair.lean` | `A` | mirror of row 135 |
| 137 | `sumInlFun_of_ne` | `Isomorphism/Copair.lean` | `S` | cited in-file (128, 146, 151, 443, 457, 480). Re-declares `sumInl_of_ne_bot` |
| 138 | `sumInrFun_of_ne` | `Isomorphism/Copair.lean` | `S` | mirror of row 137 |
| 139 | `sumInlFun_mono` | `Isomorphism/Copair.lean` | `S` | cited by `scottContinuous_sumInlFun` (119). Re-declares `monotone_sumInl` |
| 140 | `sumInrFun_mono` | `Isomorphism/Copair.lean` | `S` | mirror of row 139 |
| 141 | `scottContinuous_sumInlFun` | `Isomorphism/Copair.lean` | `S` | cited by the `sumInl` def (211), `restrictLeft` (415), `PRepSum.lean` |
| 142 | `scottContinuous_sumInrFun` | `Isomorphism/Copair.lean` | `S` | mirror of row 141 |
| 143 | `copairFun_bot` | `Isomorphism/Copair.lean` | `A` | `@[simp]`, `rfl`; cited in-file (454, 463) |
| 144 | `copairFun_coe` | `Isomorphism/Copair.lean` | `A` | `@[simp]`, `rfl`; 8 in-file mentions |
| 145 | `sumBase_nonempty_of_isLUB_coe` | `Isomorphism/Copair.lean` | **`D`** | same statement as `ScottDomains.sumBase_nonempty_of_isLUB_coe` (`Skeleton/Sum.lean:357`); kernel-checked. Cited in-file (267, 340) — **this is the copy to retire** |
| 146 | `isLUB_copairFun_left` | `Isomorphism/Copair.lean` | `S` | cited by `scottContinuous_copairFun` (406) |
| 147 | `isLUB_copairFun_right` | `Isomorphism/Copair.lean` | `S` | cited by `scottContinuous_copairFun` (407) |
| 148 | `scottContinuous_copairFun` | `Isomorphism/Copair.lean` | `S` | cited by the `copair` def (411), which is `lem9_3`'s witness |

### `Isomorphism/Counterexample.lean` — 8

| # | Declaration | Module | Label | Evidence |
| -- | ----------- | ------ | ----- | -------- |
| 149 | `subsingleton_withBot_of_isEmpty` | `Isomorphism/Counterexample.lean` | `S` | cited by `subsingleton_smash_punit` (123), `lem9_5_printed_false` (156) |
| 150 | `true_ne_bot` | `Isomorphism/Counterexample.lean` | `S` | cited by `lem9_5_printed_false` (159–160) |
| 151 | `subsingleton_strictHom_punit` | `Isomorphism/Counterexample.lean` | `S` | cited by `lem9_3_printed_false` (105) |
| 152 | `lem9_3_printed_false` | `Isomorphism/Counterexample.lean` | `P` | §4 Lemma 9 item 3 **as printed**, refuted: `¬ Nonempty ((E ⊕ F) ◦→ D ≃o (E ◦→ D) × (E ◦→ F))` on `D = PUnit`, `E = F = Prop`. The printed claim is false and its negation is the paper property. Cited in prose by `Isomorphism/Copair.lean:12` |
| 153 | `isEmpty_nonBotPair_punit` | `Isomorphism/Counterexample.lean` | `S` | cited by `subsingleton_smash_punit` (123) |
| 154 | `subsingleton_smash_punit` | `Isomorphism/Counterexample.lean` | `S` | cited by `isEmpty_nonBotSum_smash_punit` (135, 138) |
| 155 | `isEmpty_nonBotSum_smash_punit` | `Isomorphism/Counterexample.lean` | `S` | cited by `lem9_5_printed_false` (156) |
| 156 | `lem9_5_printed_false` | `Isomorphism/Counterexample.lean` | `P` | §4 Lemma 9 item 5 **as printed**, refuted: `¬ Nonempty (D ⊗ (E ⊕ F) ≃o (D ⊗ E) ⊕ (D ⊗ E))` on `D = Prop`, `E = PUnit`, `F = Prop`. Cited in prose by `Isomorphism/Distribute.lean:13` |

### `Isomorphism/Lift.lean` — 4

| # | Declaration | Module | Label | Evidence |
| -- | ----------- | ------ | ----- | -------- |
| 157 | `scottContinuous_coe` | `Isomorphism/Lift.lean` | `S` | cited by the `liftRestrict` def (125), which is half of `lem9_6`'s witness |
| 158 | `liftExtendFun_bot` | `Isomorphism/Lift.lean` | `A` | `@[simp]`, `rfl`. Uncited by name (on `unused-theorems.sh`'s list) |
| 159 | `liftExtendFun_coe` | `Isomorphism/Lift.lean` | `A` | `@[simp]`, `rfl`. Uncited by name (on `unused-theorems.sh`'s list) |
| 160 | `scottContinuous_liftExtendFun` | `Isomorphism/Lift.lean` | `S` | cited by the `liftExtend` def (121). Its proof re-derives `liftBase_nonempty_of_isLUB` inline — §4 near-duplicate 2 |

### `Isomorphism/StrictCurry.lean` — 10

| # | Declaration | Module | Label | Evidence |
| -- | ----------- | ------ | ----- | -------- |
| 161 | `isLUB_strictHom_of_isLUB_val` | `Isomorphism/StrictCurry.lean` | `S` | cited by `curryStrict` (256) |
| 162 | `scottContinuous_subtypeVal` | `Isomorphism/StrictCurry.lean` | `S` | cited by `strictToScottHom` (221) |
| 163 | `smashVal_bot` | `Isomorphism/StrictCurry.lean` | `A` | `@[simp]`, `rfl`. Uncited by name (on `unused-theorems.sh`'s list) |
| 164 | `smashVal_coe` | `Isomorphism/StrictCurry.lean` | `A` | `@[simp]`, `rfl`. Uncited by name (on `unused-theorems.sh`'s list) |
| 165 | `scottContinuous_smashVal` | `Isomorphism/StrictCurry.lean` | `S` | cited by `uncurryStrict` (233). Its proof re-derives `smashBase_nonempty_of_isLUB_coe` inline — §4 near-duplicate 1 |
| 166 | `smashPair_of_ne` | `Isomorphism/StrictCurry.lean` | **`D`** | same statement as `ScottDomains.smashPair_of_ne_bot` (`Skeleton/Sum.lean:692`); kernel-checked. 7 in-file mentions — **this is the copy to retire** |
| 167 | `smashPair_of_bot` | `Isomorphism/StrictCurry.lean` | **`D`** | same **name** and statement as `ScottDomains.smashPair_of_bot` (`Skeleton/Sum.lean:696`); kernel-checked. 6 in-file mentions — **this is the copy to retire** |
| 168 | `smashPair_mono` | `Isomorphism/StrictCurry.lean` | `S` | cited by `scottContinuous_smashPair` (185). Joint monotonicity — subsumes `Skeleton/Sum.lean`'s `monotone_smashPair_left`/`_right` (rows 86, 87), which should be derived from it rather than proved separately |
| 169 | `scottContinuous_smashPair` | `Isomorphism/StrictCurry.lean` | `S` | cited by `curryStrictInner` (242); the one argument in the file with content |
| 170 | `strictHom_apply_bot_left` | `Isomorphism/StrictCurry.lean` | `S` | cited by `smashCurry`'s `map_rel_iff'` (314) |

## 8. Paper claims checked against the PDF, not the docstring

The plan warns that a docstring saying "**Lemma 17**" is a claim to check. Seven
were checked against rendered text from
`ScottDomains/papers/Gunter Scott 1990.pdf`:

| # | Claim | Physical page | Result |
| -- | ----- | ------------- | ------ |
| 1 | Lemma 10 has 7 conjuncts | 23 (printed 22) | **confirmed** — seven comma-separated operator slots |
| 2 | Lemma 17 has 10 conjuncts | 33 (printed 32) | **confirmed** — ten slots, the last three `D♮ D♯ D♭` |
| 3 | Theorem 16 has 2 conjuncts | 33 (printed 32) | **confirmed** — "algebraic lattice **and** the inclusion … is an embedding" |
| 4 | Theorem 18 is stated without proof | 33 (printed 32) | **confirmed** — "The theorem is due to Smyth and its proof may be found in [Smy83a]" |
| 5 | Proposition 15 is one claim | 32 (printed 31) | **confirmed** — "A bounded complete domain is bifinite" |
| 6 | Lemma 19 concludes `im(r)` is a **domain** | 34 (printed 33) | **confirmed, and the Lean statement is weaker** — row 50 |
| 7 | Lemma 20 is one claim | 34 (printed 33) | **confirmed** — "If `D` is a domain, then `Fc(D)` is a cpo" |

Two docstring defects found by the check, neither affecting a proof:

1. **`Skeleton/Lemma10.lean:12–13` quotes Lemma 10 with six operators**, omitting
   `D ⊕ E`. The file predates r0028, which added the coalesced sum; the quotation
   was never updated. `ClosureProperties.lean:12–13` quotes all seven and is
   correct. A reader taking `Skeleton/Lemma10.lean` as the statement of record
   would count the conjuncts wrong — exactly the failure the conjunction theorems
   were added to prevent.
2. **`Skeleton/Sum.lean` labels its `⊕` sections "`D + E`"** (lines 8, 108, 527).
   The theorems in them are `lem10_sum`/`lem17_sum` over `CoalescedSum`, which is
   `⊕`, row 6 of both lemma lists; `D + E` is row 5 and lives in
   `ClosureProperties/SeparatedSum.lean`. Same cause: the file predates r0034's
   separation of `+` from `⊕`. Its "taking Lemma 10 to 6 of 6 conjuncts and
   Lemma 17 to 5 of 5" (line 24) is now 7 and 10.

## 9. What this area contributes, as a ratio

| # | Measure | Value |
| -- | ------- | ----- |
| 1 | declarations | 170 |
| 2 | paper conjuncts stated | 32 of the paper's 87 numbered conjuncts (36.8%) |
| 3 | declarations per paper conjunct | 5.3 |
| 4 | serving nothing (`U`) | 1 (0.6%) |
| 5 | duplicated (`D`) | 6 in 3 pairs (3.5%) |
| 6 | surplus hypotheses (§5) | 6 declarations |

5.3 declarations per conjunct is well under the development-wide 13.2 in
`docs/PropertiesVsTheorems.md` §2, and the reason is visible in the table: this
area is where the paper's conjunct lists are, and a conjunct list is cheap per
conjunct once its operator's basis characterization exists. The support mass
(114 `S` rows) is concentrated in exactly four places the paper elides — the
bases `K(D×E)`, `K(D⊥)`, `K(D⊕E)`, `K(D⊗E)`, each an `iff` whose two directions
are both spent.

## 10. Recommendations, none acted on

| # | Action | Target | Cost |
| -- | ------ | ------ | ---- |
| 1 | Retire the three duplicate copies in `Isomorphism/` (rows 145, 166, 167) plus the `smashPair` def they rest on; import `ScottDomains.Skeleton.Sum` instead | `Isomorphism/Copair.lean`, `Isomorphism/StrictCurry.lean` | 2 import lines, 5 deletions; import is acyclic |
| 2 | Comment out `strictHom_val_of_isStrict` in place with a note, r0020-style; rebuild and confirm unchanged | `ClosureProperties/StrictFunction.lean:144` | 1 declaration |
| 3 | Test the six surplus-hypothesis claims of §5 by deleting the hypotheses and rebuilding | `Skeleton/Lemma10.lean`, `Skeleton/Sum.lean` | one build |
| 4 | Make `lem17_fun` call `exists_finite_projection_fixing`, or correct that docstring's claim | `Skeleton/Lemma17.lean:403` | ~45 duplicated lines |
| 5 | Derive `monotone_smashPair_left`/`_right` from `smashPair_mono` | `Skeleton/Sum.lean:700, 713` | 2 declarations |
| 6 | Fix the two docstring defects of §8 | `Skeleton/Lemma10.lean`, `Skeleton/Sum.lean` | prose only |
| 7 | **Cross-area, for the orchestrator at tier 2**: `lem19` (row 50) and `FinitaryProjectionPoset.IsClosure.domain_range` state the same paper conjunct at two strengths, in two agents' areas | `Skeleton/Section6.lean:253`, `FinitaryProjectionPoset.lean:282` | — |
| 8 | **Cross-area, for the orchestrator at tier 2**: unifying `sumInl`/`sumInlFun` (§4 near-duplicate 3) retires `PRepSum.lean`'s two bridge theorems as well, which are in agent5's area | `Isomorphism/Copair.lean:65–103`, `PRepSum.lean:472,477` | 8 declarations |
| 9 | Subtract 2 from the development's theorem count, or tighten the counting rule to exclude docstring lines | `scripts/counts.sh`, `scripts/module-counts.sh` | §0 |

## 11. Artifacts

| # | Path | What |
| -- | ---- | ---- |
| 1 | `ScottDomains/ScottDomains/Audit/Skeleton.lean` | 4 `rfl` theorems making the three `D` pairs build-checked. New; builds clean |
| 2 | `scripts/skeleton-audit-cites.sh` | per-declaration citation measurement (module, name, `simp`, total mentions, mentions outside the declaring file, up to three citers) — the table's raw data |
| 3 | `ScottDomains/logs/compile-20260808-094723.agent3.log` | `Audit.Skeleton` build: 844 jobs, 0 errors, 0 warnings, 0 `sorry` |
| 4 | `ScottDomains/logs/compile-20260808-094734.agent3.log` | full build: 1224 jobs, 0 errors, 0 warnings, 1 `sorry` |

Committed on branch `agent3` at `89fe59f`; not pushed, per the agents-commit /
orchestrator-pushes rule.
