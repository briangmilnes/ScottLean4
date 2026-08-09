---
round: r0044
from: agent1
to: orchestrator
subject: sneq-s2-s4
date: 2026-0808-17:17
started: 2026-0808-16:45
finished: 2026-0808-17:17
related:
  - plans/r0044-plan-from-orchestrator-to-orchestrator-specification-defects.md
  - analyses/property-coverage.2026-0808-11:59.orchestrator.md
  - analyses/property-coverage-remeasure.2026-0808-16:55.orchestrator.md
---

# r0044, Class 1 — the `S≠` rows of §2, §3 and §4, split three ways

## 1. Headline

**My area holds 5 `S≠` rows, not the 9 the plan assigns it.** Split:

| # | Kind | Definition | Count |
| -- | ---- | ---------- | ----: |
| 1 | under-specified | strict weakening — a conjunct missing, or stated at a special case | **3** |
| 2 | incorrectly specified | not a weakening; asserts what the paper does not | **0** |
| 3 | deliberately divergent | the printed statement is false, ours is the repair — correct work | **2** |
| — | **total** | | **5** |

**Defects attributable to this development: 3.** The other 2 are repairs of two of
the paper's nine known printed defects and are not defects of ours.

The round's sharpest single result is not one of the five labels. It is that
**row 45's extra hypothesis is provably unnecessary**, and the source docstring
asserting it is necessary is false — see §4.

## 2. The plan's 9-and-9 split is wrong; the real split is 5 and 13

The plan (line 69–74) assigns 9 `S≠` rows to §2/§3/§4 and 9 to §5/§6/§7. Both
numbers are wrong. Re-derived from the per-agent reports rather than from the
plan, with `scripts/a1-sneq-s2-s4.sh` §1:

| # | Source | Area | r0040 `S≠` | r0043 added | total |
| -- | ------ | ---- | ---------: | ----------: | ----: |
| 1 | r0040/r0043 agent1 | §2, §3 | 3 | 0 | **3** |
| 2 | r0040/r0043 agent2 | §4 → Lemma 10 | 2 | 0 | **2** |
| 3 | r0040/r0043 agent3 | Thm 11 → §5 | 0 | 1 (row 18) | 1 |
| 4 | r0040/r0043 agent4 | §6 | 4 | 1 (p16) | 5 |
| 5 | r0040/r0043 agent5 | §7 | 7 | 0 | 7 |
| — | **total** | | **16** | **2** | **18** |

16 and 18 both reconcile: 16 is the merged r0040 analysis's row 3, and 18 is the
plan's figure. Only the *split* was never computed. **§2+§3+§4 = 5; §5+§6+§7 =
13.** The other Class 1 stream should expect 13 rows, and should not stop at 9.

The area boundary is exact, not approximate: r0040's agent2 covered "§4 → Lemma
10", which is the whole of §4, and agent3 began at Theorem 11 (§5.2). No §4 row
falls to another stream, and Theorem 14 — which both docs mis-section as §4.5 —
is §6.1 and belongs to the other stream.

## 3. The five rows

Every Lean statement below is quoted **as elaborated**, from `#check @d` against
the built `.olean` (`scripts/a1-elab.sh`), never read off a source line. Axiom
footprints are from `#print axioms` in the same run.

| # | Row | Paper, printed page | Declaration | Kind |
| -- | --: | ------------------- | ----------- | ---- |
| 1 | 45 | p. 9, §3 opening | `ScottDomains.Kleene.sSup_recoverAt` | **1** under-specified |
| 2 | 53 | p. 11, §3.2 | `ScottDomains.JungSFP.lemma213` | **1** under-specified |
| 3 | 59 | p. 12, Thm 7 proof | `ScottDomains.PRepFun.strictHomIsAlgebraic` | **1** under-specified |
| 4 | Lem 9.3 | p. 21 | `ScottDomains.Recovered.lem9_3` | **3** deliberately divergent |
| 5 | Lem 9.5 | p. 21 | `ScottDomains.Recovered.lem9_5` | **3** deliberately divergent |

### Row 45 — the recovery formula. Kind 1: stated at bounded-complete `E`.

**Paper, printed p. 9** (`pdftotext -layout` lines 335–339; the extraction drops
the `fi` ligature and renders `⊔` as `F`):

> One thing which makes domains particularly nice to work with is the way one may
> describe a continuous function `f : D → E` between domains `D` and `E` using the
> compact elements. Let `G_f` be the set of pairs `(x′, y′)` such that `x′ ∈ K(D)`
> and `y′ ∈ K(E)` and `y′ ⊑ f(x′)`. If `x ∈ D`, then one may recover from `G_f`
> the value of `f` on `x` as `f(x) = ⊔{y′ | (x′,y′) ∈ G_f and x′ ⊑ x}`.

**Lean, elaborated:**

    @ScottDomains.Kleene.sSup_recoverAt :
      ∀ {α : Type u_1} {β : Type u_2} [inst : CompletePartialOrder α]
        [inst_1 : CompletePartialOrder β] [ScottDomains.IsAlgebraic α]
        [ScottDomains.IsAlgebraic β] [ScottDomains.BoundedComplete β] {f : α → β},
        ScottContinuous f → ∀ (x : α), sSup (ScottDomains.Kleene.recoverAt f x) = f x

    depends on axioms: [propext, Quot.sound]

`recoverAt` and `graphPairs` (`Kleene/Graph.lean:53,57`) are the paper's `G_f` and
its section verbatim — both coordinates restricted to compacts, downward closed in
the second. The equation is the paper's equation.

**The deviation is one instance binder: `[BoundedComplete β]`.** The paper's
sentence quantifies over all domains `D` and `E`; the Lean statement covers only
those where `E` is bounded complete. A domain that is not bounded complete — and
§6 exists precisely because such domains matter — is outside the statement. That
is a strict weakening by restriction to a special case: **kind 1**.

In the opposite direction the Lean statement is *more* general than the paper's:
the paper's "domain" is `IsAlgebraic` **plus** countable `K(D)` (`Domain.lean:128`),
and the Lean version asks only `IsAlgebraic` on both sides. Dropping countability
is a generalization, not a defect, and it is not what makes the row `S≠`.

**This corrects r0043's agent1**, which moved row 45 to `S+P`. The move was right
about the family — `graphPairs` really is `G_f`, where r0040's subject
`ContinuousConstruction.coe_eq_basisExtension_self` was not; its elaborated type,

    @ScottDomains.ContinuousConstruction.coe_eq_basisExtension_self :
      ∀ {α β} [CompletePartialOrder α] [IsAlgebraic α] [CompletePartialOrder β]
        (f : ScottHom α β), ⇑f = ⇑(ContinuousConstruction.basisExtension ⇑f ⋯)

says nothing about `G_f` at all. But `sSup_recoverAt` carries a hypothesis the
paper does not, so the row is `S≠`, kind 1, and not `S+P`. §4 shows the fix is a
deletion.

### Row 53 — "there are domains `D, E` with `D → E` not a domain." Kind 1: the criterion without its witness.

**Paper, printed p. 11** (extraction line 420–421; `!` is the extractor's
rendering of `→`):

> Unfortunately, the full class of domains has a serious problem. It is this:
> there are domains `D, E` such that the cpo `D → E` is not a domain (we will
> return to this topic in Section 6).

**Lean, elaborated:**

    @ScottDomains.JungSFP.lemma213 :
      ∀ {D : Type u_1} {E : Type u_2} [inst : CompletePartialOrder D]
        [inst_1 : CompletePartialOrder E] [ScottDomains.IsAlgebraic D] {x₁ x₂ : D},
        IsCompactElement x₁ → IsCompactElement x₂ →
        (minimalUpperBounds (compacts D) {x₁, x₂}).Infinite →
        ∀ [ScottDomains.IsAlgebraic E] {a₁ a₂ b₁ b₂ c : E},
          IsCompactElement a₁ → IsCompactElement a₂ →
          b₁ ∈ minimalUpperBounds (compacts E) {a₁, a₂} →
          b₂ ∈ minimalUpperBounds (compacts E) {a₁, a₂} →
          b₁ ≠ b₂ → b₁ ≤ c → b₂ ≤ c → ¬ScottDomains.IsAlgebraic (ScottHom D E)

    depends on axioms: [propext, Classical.choice, Quot.sound]

The paper asserts an **existential**: `∃ D E, Domain D ∧ Domain E ∧ ¬ Domain (D → E)`.
The Lean statement is a **sufficient criterion** for the failure, universally
quantified. **Missing conjunct: the witness** — `∃ D E` satisfying the criterion's
seven hypotheses.

Three probes establish that no witness exists in the package:

1. `JungSFP.lean:481` is the **only** occurrence of `¬ IsAlgebraic (ScottHom …)`
   in all 100 modules — it is `lemma213`'s own conclusion.
2. `lemma213` has exactly two call sites, `JungSFP.lean:703` (inside `thm214`) and
   `:785` (inside `lemma217`). Both apply it contrapositively at abstract `D`, `E`
   under a hypothesis `hAlg : IsAlgebraic (ScottHom D D)`. Neither instantiates
   `D` or `E` at a concrete poset.
3. r0043's agent4 recorded the Figure 3c poset as still unbuilt, and it is the
   paper's own route to the witness in §6.

**Honest qualification on the taxonomy.** Read strictly, `lemma213` neither implies
the paper's sentence nor is implied by it: it is Jung 1989's Lemma 2.13, a
different and stronger theorem imported from another source. So "strict weakening"
is a loose fit. It is placed at kind 1 because what separates it from the paper is
something **missing** — the existential witness — and not something asserted that
the paper denies, which is what kind 2 is for. It is certainly not kind 3: the
paper's sentence is true, and the development does not repair it.

### Row 59 — "the strict step functions form a basis." Kind 1: the basis is not identified.

**Paper, printed p. 12**, closing the proof sketch of Theorem 7 (extraction lines
444–447):

> The proof that the poset of step functions has decidable ordering and finite
> normal subposets is tedious, but not difficult, using the effective
> presentations of `D` and `E`. **The proof of these facts for `D ⊸ E` is
> essentially the same since the strict step functions form a basis.**

**Lean, elaborated:**

    @ScottDomains.PRepFun.strictHomIsAlgebraic :
      ∀ {α : Type u_1} {β : Type u_2} [inst : CompletePartialOrder α]
        [inst_1 : CompletePartialOrder β] [ScottDomains.Domain α]
        [ScottDomains.Domain β] [ScottDomains.BoundedComplete β],
        ScottDomains.IsAlgebraic (ScottDomains.StrictHom α β)

    depends on axioms: [propext, Classical.choice, Quot.sound]

**Missing conjunct: the identity of the basis.** The paper names a specific set —
the strict step functions — and asserts it is a basis for `D ⊸ E`. Lean asserts
only that *some* basis exists, which is what `IsAlgebraic` unfolds to
(`Domain.lean:119`: `compactsBelow x` directed with `x` as its least upper bound,
for every `x`). "`K(D ⊸ E)` is the strict step functions" implies `IsAlgebraic
(StrictHom α β)`; the converse does not hold, so this is a strict weakening.

The package contains no strict step function at all. `grep -riE
'strictStep|stepStrict|strict step'` over all 100 modules returns exactly one hit,
and it is the development conceding the point in its own docstring —
`Effective/FunctionSpace.lean:256–264`:

> The paper's reason is that "the strict step functions form a basis" for `D ⊸ E`.
> **This development has no strict-step-function basis**; what it has is
> `PRepFun.strictHomDomain`, which makes `D ⊸ E` a domain by injecting
> `K(D ⊸ E)` into `K(D → E)`. […] The statement is the paper's; the proof is
> weaker than the paper's.

**Hypothesis direction, recorded for completeness.** The paper's Theorem 7 assumes
`D` and `E` are *bounded complete* domains; `strictHomIsAlgebraic` asks
`[Domain α] [Domain β] [BoundedComplete β]` and omits `[BoundedComplete α]`. On
hypotheses the Lean statement is therefore more general than the paper's. The
weakening is entirely in the conclusion, and the row's kind is decided by that.

### Rows 4 and 5 — Lemma 9 items 3 and 5. Kind 3: two of the paper's nine printed defects.

**Paper, printed p. 21** ("Let `D`, `E` and `F` be cpo's"), decoded from the
`cmsy10` glyph codes because `pdftotext` drops every `⊗` and every `⊥` —
`StatementRecovery.md` §2.3 carries the character-for-character decode and the
300 dpi page render that confirms it:

> 3. `(E ⊕ F) ◦→ D ≅ (E ◦→ D) × (E ◦→ F)`
> 5. `D ⊗ (E ⊕ F) ≅ (D ⊗ E) ⊕ (D ⊗ E)`

**Both printed statements are false, and both are among the paper's nine known
printed defects** — `StatementRecovery.md` §2.5 and `PaperInventory.md` row 2c.
Neither is a new discovery of this round.

The **named printed defect** in each:

* **Item 3** — the second factor is printed `E ◦→ F` and should be `F ◦→ D`. The
  printed right-hand side does not mention `D` at all, which is already the tell.
  The correction is the paper's own universal property of `⊕`, three pages
  earlier (decoded p. 20, printed p. 19, §4.4): `f : D ◦→ F` and `g : E ◦→ F`
  induce a unique strict `[f, g]`, i.e. `⊕` is the coproduct for strict maps, so
  the strict hom-functor carries it to a product.
* **Item 5** — the second summand is printed `D ⊗ E` and should be `D ⊗ F`. `F`
  occurs on the left-hand side and nowhere on the printed right; the second `E`
  is the only position it can occupy.

**Lean, elaborated — the repairs:**

    @ScottDomains.Recovered.lem9_3 :
      ∀ {α β γ} [CompletePartialOrder α] [CompletePartialOrder β] [CompletePartialOrder γ],
        Nonempty (StrictHom (CoalescedSum β γ) α ≃o StrictHom β α × StrictHom γ α)

    @ScottDomains.Recovered.lem9_5 :
      ∀ {α β γ} [CompletePartialOrder α] [CompletePartialOrder β] [CompletePartialOrder γ],
        Nonempty (Smash α (CoalescedSum β γ) ≃o CoalescedSum (Smash α β) (Smash α γ))

    both depend on axioms: [propext, Classical.choice, Quot.sound]

Under Lemma 9's naming (`α = D`, `β = E`, `γ = F`) these read `(E ⊕ F) ◦→ D ≅
(E ◦→ D) × (F ◦→ D)` and `D ⊗ (E ⊕ F) ≅ (D ⊗ E) ⊕ (D ⊗ F)` — the corrected forms
exactly. **The hypotheses are the paper's, unweakened**: only
`[CompletePartialOrder]` on each of the three, matching "Let `D`, `E` and `F` be
cpo's". No algebraicity, no countability, no bounded completeness has crept in.
That matters for the classification: these two rows deviate from the printed page
in the conclusion *and nowhere else*, so the divergence is entirely the repair.

**Lean, elaborated — the kernel-checked refutations of the printed forms:**

    ScottDomains.Isomorphism.lem9_3_printed_false :
      ¬Nonempty (StrictHom (CoalescedSum Prop Prop) PUnit ≃o
                 StrictHom Prop PUnit × StrictHom Prop Prop)

    ScottDomains.Isomorphism.lem9_5_printed_false :
      ¬Nonempty (Smash Prop (CoalescedSum PUnit Prop) ≃o
                 CoalescedSum (Smash Prop PUnit) (Smash Prop PUnit))

Reading `lem9_3_printed_false` against the printed item 3 with `D = PUnit`,
`E = F = Prop`: left `(E ⊕ F) ◦→ D`, right `(E ◦→ D) × (E ◦→ F)` — the second
factor is `StrictHom Prop Prop`, i.e. `E ◦→ F`, the printed term and not the
repair. Likewise `lem9_5_printed_false`'s right side is `Smash Prop PUnit`
repeated, i.e. `(D ⊗ E) ⊕ (D ⊗ E)` at `D = Prop`, `E = PUnit`, `F = Prop`. The
elaborated types confirm the refutations attack the printed forms and not
strawmen.

**Kind 3. Not defects, and not to be counted as such.**

## 4. The round's most significant finding: row 45's extra hypothesis is provably unnecessary, and the docstring saying otherwise is false

`Kleene/Graph.lean:36–45` states, as the file's justification for the binder:

> **bounded completeness of `E`** — which the paper does not mention here but
> which the argument cannot do without. `sSup` in a cpo is pinned down only on
> directed sets, and `{y₀ | (x₀,y₀) ∈ G_f, x₀ ⊑ x}` is directed only because two
> of its members are bounded by `f(x₃)` for a common compact `x₃ ⊑ x`, so their
> join exists and is compact by `isCompactElement_of_isLUB_pair`.

**This is false, and the kernel says so.** The argument needs an upper bound for
`y₁` and `y₂` *inside the set*, not their join. `IsAlgebraic β` already carries
`directedOn_compactsBelow` (`Domain.lean:121`), so `y₁, y₂ ∈ compactsBelow (f x₃)`
yields a compact `y₃` with `y₁, y₂ ⊑ y₃ ⊑ f x₃` directly, and `y₃ ∈ recoverAt f x`
via the same `x₃`. Bounded completeness is never needed.

`scripts/a1-probe45.lean`, run by `scripts/a1-probe.sh`, reproves both lemmas with
the binder deleted:

    'A1Probe45.sSup_recoverAt_bcFree' depends on axioms: [propext, Quot.sound]
    @sSup_recoverAt_bcFree : ∀ {α β} [CompletePartialOrder α] [CompletePartialOrder β]
      [IsAlgebraic α] [IsAlgebraic β] {f : α → β},
      ScottContinuous f → ∀ (x : α), sSup (recoverAt f x) = f x

Same axiom footprint as the original — `[propext, Quot.sound]`, no
`Classical.choice`. The probe lives in `scripts/`, outside
`ScottDomains/ScottDomains/`, so `lake build` never sees it and `scripts/counts.sh`
never counts it. No `.lean` file in the package was edited.

Three consequences:

1. **Row 45 is one hypothesis deletion away from `S+P`** — a strictly local edit
   to `directedOn_recoverAt`, whose downstream callers (`sSup_recoverAt`,
   `eq_of_graphPairs_eq`, `characterization_powersetNat`) all keep their proofs —
   `P N` is bounded complete, so the paper's own example is unaffected either way.
   It is the cheapest item any Class 1 stream will report.
2. **It is also a Class 4 hit found in a Class 1 stream.** `Kleene/Graph.lean`'s
   docstring asserts something false about its own module. That is the same defect
   shape as `FlatPowerdomain.lean:34` and `PRepFun.lean:98`, and it was invisible
   to r0043's citation checker because every *name* in the sentence resolves — the
   false thing is the claim, not a name. Agent 8's reading half should have this
   one.
3. It is a caution about the "vacuity" instrument agents 3–5 are building. Here an
   unused-strength hypothesis is not vacuous in the `#lint unusedArguments` sense —
   `BoundedComplete β` *is* used, by `isLUB_sSup_of_bddAbove` inside
   `directedOn_recoverAt`. A hypothesis can be genuinely consumed by the proof and
   still be removable, because a different proof does not need it. Deletion probes
   catch this; argument-usage linters do not.

## 5. Negative results, stated as results

* **Zero rows of kind 2 in §2, §3 and §4.** Not one of the five `S≠` rows asserts
  something the paper does not say. Three are honest weakenings that the
  development documents in its own docstrings, and two are repairs of printed
  defects. Whatever the other stream finds in §5–§7, the mis-specification rate in
  §2–§4 is 0 of 5.
* **No new printed defect found.** Every printed-page deviation in my five rows
  was already among the nine on record (`StatementRecovery.md` §2.5,
  `PaperInventory.md` row 2c). I checked before declaring, as the brief required,
  and declare none.
* **`PaperInventory.md` row 2c is not wrong, only silent about row 45.** Row 2c
  lists three qualifications on the 24 numbered results, two of which are the same
  shape as row 45's — Lemma 17's `[BoundedComplete β]` and Theorem 26's
  `hs : ∀ i, 0 < s i`. Row 45 is a prose claim, not one of the 24, so row 2c does
  not cover it. Once §4's deletion is applied, row 45 needs no entry there at all.

## 6. Instrument

Three scripts, all read-only over the package, all prefixed `a1-` per the plan:

| # | Script | What it does |
| -- | ------ | ------------ |
| 1 | `scripts/a1-sneq-s2-s4.sh` | **the reproduction.** Runs the whole report end to end: re-derives the row population from the r0040/r0043 reports, extracts and greps the paper's three sentences, elaborates all eight declarations, runs the three negative-half greps, and runs the row-45 probe |
| 2 | `scripts/a1-elab.sh` | `#check @d` + `#print axioms d` against the built `.olean`, for declarations whose **module path differs from their namespace** (`ScottDomains.Recovered.lem9_3` lives in `ScottDomains/Skeleton/Recovered.lean`). `scripts/axioms.sh` guesses the module from the namespace and gets exactly these wrong, which is why this exists rather than reusing it |
| 3 | `scripts/a1-probe.sh` + `scripts/a1-probe45.lean` | elaborates a probe file from outside the package, to decide whether a hypothesis is deletable. §4's finding |

Each is one allowlisted command: no chaining, no pipe, no heredoc, no `cd` by the
caller.

## 7. Measurement invariance

No `.lean` file in `ScottDomains/ScottDomains/` was opened read-write.

`scripts/counts.sh`, identical at start and end of the round:

    modules:  100
    lines:    37300
    theorems: 1773
    sorry:    0 in 0 file(s)

`scripts/compile.sh -r r0044` →
`ScottDomains/logs/compile-20260808-171657.agent1.log`:

    jobs:             1339
    lean diagnostics: 0
    lake errors:      0
    sorry decls:      0
    other warnings:   0

Five files were written, none of them in the package: `scripts/a1-sneq-s2-s4.sh`,
`scripts/a1-elab.sh`, `scripts/a1-probe.sh`, `scripts/a1-probe45.lean`, and this
report.
