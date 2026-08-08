---
round: r0038
from: agent2
to: orchestrator
subject: audit-projections
date: 2026-0808-10:05
started: 2026-0808-09:40
finished: 2026-0808-10:05
related:
  - plans/r0038-plan-from-orchestrator-to-orchestrator-theorem-audit.md
  - docs/PropertiesVsTheorems.md
---

# r0038 — `Audit.Projections`: 184 theorems classified

## 1. What was measured, and the one count that moved

`scripts/module-counts.sh` reports **185** theorem-ish lines across the eleven
modules of this area. One of them is not a declaration:
`IsEmbeddingProjectionPair.isProjection_comp` sits inside the `/- UNUSED …
-/` block comment at `Projection.lean:77–95`, commented out in place in the r0020
style. Both `counts.sh` and `module-counts.sh` match on `^theorem `, so both
count it. **The area holds 184 live theorems**, and the project-wide 1308 is
therefore an over-count by at least this one.

| # | Module | Counted | Live | `@[simp]` |
| -- | ------ | ------- | ---- | --------- |
| 1 | `Projection.lean` | 11 | 10 | 0 |
| 2 | `FinitaryProjection.lean` | 4 | 4 | 0 |
| 3 | `NormalSubposet.lean` | 13 | 13 | 0 |
| 4 | `NormalProjection.lean` | 12 | 12 | 1 |
| 5 | `Theorem6.lean` | 8 | 8 | 0 |
| 6 | `FinitaryProjectionPoset.lean` | 42 | 42 | 4 |
| 7 | `FinitaryProjectionEmbedding.lean` | 28 | 28 | 0 |
| 8 | `Bifinite.lean` | 3 | 3 | 0 |
| 9 | `MinimalUpperBounds.lean` | 30 | 30 | 1 |
| 10 | `Section62.lean` | 13 | 13 | 1 |
| 11 | `SFP.lean` | 21 | 21 | 0 |
| — | **total** | **185** | **184** | **7** |

### Method

`scripts/unused-theorems.sh` answers a global yes/no and under-reports, as its
header says. Two scripts were written for this round:

- `scripts/agent2-citations.sh` — per declared name, every file that mentions it
  and how many times, splitting same-file from cross-file mentions.
- `scripts/agent2-uses.sh` — the same, with `--` line comments, `/- … -/` blocks
  and `/-- … -/` / `/-! … -/` docstrings stripped first, and with a `dup` column
  counting how many declarations in the package share the final name component.

The second script is the one the labels rest on, and the difference between the
two is large. **Twenty-two declarations in this area are named in docstrings and
applied by no proof.** `Fp.le_iff_fpBasis_subset_stableCompacts` is named in
three modules' prose and used in none; `mubStep_eq_of_subset` is named twice in
`MinimalUpperBounds.lean`'s own docstrings and used nowhere. A citation count
that does not strip comments cannot see this, which is why
`docs/PropertiesVsTheorems.md` §4's 130 is an under-count of the uncited
population rather than an over-count.

Logs: `ScottDomains/logs/agent2-citations-20260808-100000.agent2.log`,
`ScottDomains/logs/agent2-uses-20260808-101500.agent2.log`.

### Paper verification

`P` was not taken from docstrings. `pdftotext -layout` over
`papers/Gunter Scott 1990.pdf` pages 10–11, 30–31 and 32–34 was read directly and
every quoted block in this area's docstrings matches the source: Lemma 4's four
parts and Lemma 5's two sentences (p. 10), the §3.1 prose "a projection is a
surjection (i.e. onto) and an embedding is an injection (i.e. one-to-one)"
(p. 10), Theorem 14's two clauses and §6.1's three facts about Plotkin orders
(pp. 30–31), Theorem 16's two conjuncts and Lemma 19 (pp. 32–33). No docstring
claim in this area was found to overstate the paper.

### Label precedence

The six labels are exhaustive and one applies, so a precedence is needed where a
declaration fits two. This report uses **`D` > `W` > `P` > `A` > `S` > `U`** —
defects surface first, then paper content, then the reason a support theorem
exists. Citation counts appear in the evidence column regardless of label, so
nothing is lost by the ordering. In particular a heavily-cited accessor such as
`IsProjection.le` is labelled `A`, not `S`: it is the projection API for the
`IsProjection` definition, and definitions are outside the 99 properties.

## 2. Totals

| # | Label | Count | Share |
| -- | ----- | ----- | ----- |
| 1 | `P` — states a paper property | 28 | 15.2% |
| 2 | `S` — support, something cites it | 119 | 64.7% |
| 3 | `A` — projection / `simp` API | 22 | 12.0% |
| 4 | `U` — uncited, not a property, not API | 9 | 4.9% |
| 5 | `D` — duplicate | 4 | 2.2% |
| 6 | `W` — over-strength | 2 | 1.1% |
| — | **total** | **184** | |

`U + D + W = 15 of 184, 8.2%`. r0020's rate was 6 of ~199, about 3%.

Per module:

| # | Module | P | S | A | U | D | W |
| -- | ------ | - | - | - | - | - | - |
| 1 | `Projection` | 2 | 5 | 3 | 0 | 0 | 0 |
| 2 | `FinitaryProjection` | 2 | 1 | 1 | 0 | 0 | 0 |
| 3 | `NormalSubposet` | 8 | 2 | 3 | 0 | 0 | 0 |
| 4 | `NormalProjection` | 0 | 11 | 1 | 0 | 0 | 0 |
| 5 | `Theorem6` | 1 | 7 | 0 | 0 | 0 | 0 |
| 6 | `FinitaryProjectionPoset` | 2 | 33 | 7 | 0 | 0 | 0 |
| 7 | `FinitaryProjectionEmbedding` | 6 | 21 | 0 | 1 | 0 | 0 |
| 8 | `Bifinite` | 0 | 0 | 1 | 2 | 0 | 0 |
| 9 | `MinimalUpperBounds` | 3 | 18 | 5 | 3 | 1 | 0 |
| 10 | `Section62` | 2 | 7 | 1 | 1 | 0 | 2 |
| 11 | `SFP` | 2 | 14 | 0 | 2 | 3 | 0 |

## 3. The `D` rows — four duplicate pairs, kernel-checked

`ScottDomains/Audit/Projections.lean` (new, this round, 9 theorems, builds
clean) proves each pair by applying its partner. The elaborator accepts such a
proof only if the two statements coincide up to argument order and definitional
unfolding, so "looks the same" is now a kernel check.

| # | Pair | Later declaration (`D`) | Earlier partner | Difference |
| -- | ---- | ----------------------- | --------------- | ---------- |
| 1 | general | `exists_mem_upperBounds_of_directedOn` (`MinimalUpperBounds`, r0028) | `exists_upperBound_mem_of_finite` (`Skeleton/Section6`, r0027) | **none** — same statement, same proof script, same namespace |
| 2 | `t ⊆ s` case | `SFP.exists_upperBound_of_finite_subset` (r0034) | `FpEmbedding.exists_upperBound_mem_of_finite` (r0032) | argument order only |
| 3 | attained lub | `SFP.exists_mem_isLUB_of_finite` (r0034) | `FpEmbedding.isLUB_of_finite_directed` (r0032) | binder name only |
| 4 | finite image | `SFP.range_toFp_eq` (r0034) | `SFP.range_normalHom_of_finite` (r0034, same file) | `(toFp hN).val` unfolds to `normalHom hN` by `rfl`; also declared at `[Domain α]` where the partner needs only `[IsAlgebraic α]` |

Pairs 1–3 are **one lemma declared four times in three modules**: two copies at
the general hypothesis ("every `y ∈ t` is dominated by some `z ∈ s`") and two at
the special case `t ⊆ s`, which implies it in one step
(`Audit.Projections.subset_of_dominated`).

**Pair 1 was found by the elaborator, not by grep, and it straddles this area and
agent3's.** `MinimalUpperBounds.lean` imports `Bifinite.lean`, which imports
`NormalSubposet` and `Domain` and not `Skeleton/Section6`, so the second copy
could not see the first when it was written. `Section62.lean` imports both and is
the first module where the two names are in scope together. The first draft of
the audit file wrote the unqualified name and the elaborator resolved it to the
wrong one; the type mismatch is what exposed the duplicate. This is precisely the
masking `scripts/unused-theorems.sh`'s header warns about — two declarations
sharing a final name component in different namespaces hide each other from a
name-based count. It is also the r0028 failure mode again: both copies are
correct proofs of the same proposition, so `lake build` reports nothing.

`Skeleton/Section6.lean` is agent3's area, so the retirement decision for pair 1
is a tier-2 call.

## 4. The `W` rows — over-strength that a consumer had to work around

Two rows, both in `Section62.lean`, and the evidence is `JungFinite.lean`'s own
docstring rather than an inference.

| # | Declaration | Consumer | Weaker statement that serves |
| -- | ----------- | -------- | ---------------------------- |
| 1 | `Section62.apply_eq_self_of_mem_mubIter` | `JungFinite`'s Lemma 2.2 assembly | `JungFinite.apply_eq_self_of_mem_mubIter_compacts` |
| 2 | `Section62.apply_eq_self_of_mem_mubClosure` | `JungFinite.thm18` step 4, line 652 | `JungFinite.apply_eq_self_of_mem_mubClosure_compacts` |

Both carry the hypothesis `hgA : ∀ z ∈ A, g z ∈ A`. `JungFinite.lean:533–541`
states the problem in the first person:

> This is `Section62.apply_eq_self_of_mem_mubIter` with its hypothesis `hgA` —
> that `g` maps `A` into `A` — removed. `hgA` at `A = K(D)` is "a compact
> function has compact values", Jung's Proposition 1.41, which is itself a
> consequence of Corollary 1.36 and so is exactly as expensive as the step this
> file cannot discharge.

So the live Theorem 18 route could not supply `hgA`, declared its own copies
without it, and `Section62`'s pair is now consumed by nothing:
`apply_eq_self_of_mem_mubClosure` has **zero** uses, and
`apply_eq_self_of_mem_mubIter` has one — the other `W` row. The recommendation is
to reduce the pair to the `JungFinite` form, or to retire it and note in
`Section62.lean`'s §"Theorem 18, step 4" prose that the discharged form lives in
`JungFinite`.

## 5. The `U` rows — nine, in two populations

Five are **recorded evidence**: they carry no proof load but they are what an
earlier round established, and deleting them deletes the finding. Four are
**speculative API** in r0020's population-3 sense — written for a caller that
never appeared, or for a route the project has since abandoned.

| # | Declaration | Module | Population | Why it is uncited |
| -- | ----------- | ------ | ---------- | ----------------- |
| 1 | `Fp.le_iff_fpBasis_subset_stableCompacts` | `FinitaryProjectionEmbedding` | evidence | The criterion `p ⊑ f ↔ N ⊆ S_f` that diagnoses the paper's sketch. Named in three modules' docstrings, applied nowhere. It is `⟨fpBasis_subset_stableCompacts, le_of_fpBasis_subset_stableCompacts⟩` and **both halves are cited** by `Section62`, so it carries no content beyond them. Keep as the statement of the diagnosis |
| 2 | `IsBifinite.bot_mem_of_normal` | `Bifinite` | speculative | Zero uses, **and its `IsBifinite α` hypothesis is unused** — the binder is literally `_h`. The body is `hN.bot_mem isCompactElement_bot`, so the theorem is `IsNormalIn.bot_mem` with a vacuous premise attached |
| 3 | `IsPlotkinOrder.exists_finite_normal_empty` | `Bifinite` | speculative | The `u := ∅` instance, documented as "the base case §6's inductions start from". No induction in the development starts from it |
| 4 | `mubStep_eq_of_subset` | `MinimalUpperBounds` | evidence | Definitional adequacy: it identifies `mubStep` with the paper's `U`. Its own only consumer would be a reader. Its sole in-file consumer `mem_minimalUpperBounds_singleton` therefore also serves nothing else |
| 5 | `isPlotkinOrder_iff` | `MinimalUpperBounds` | speculative | Its docstring claims "it is the shape … §6.2's later results consume". Measured: nothing consumes it |
| 6 | `exists_of_not_isPlotkinOrder` | `MinimalUpperBounds` | speculative | Its docstring says "this is the case split Smyth's proof of Theorem 18 runs". r0034 established that [Smy83a] was not obtained and that the live route is Jung's, which does not run this case split |
| 7 | `hasGreatestStableNormal_of_boundedComplete` | `Section62` | evidence | The non-vacuity witness for `HasGreatestStableNormal` — without it the hypothesis of `thm16_positive` could be empty. `thm16_positive_isEmbeddingProjectionPair` builds `fpSection` directly and does not route through it |
| 8 | `range_inter_compacts_of_finite` | `SFP` | speculative | Its docstring says it "makes the `FpLattice` machinery unnecessary for the forward direction", but `thm14_forward` writes `Set.range ⇑p ∩ compacts α` directly at line 325 and never applies it |
| 9 | `range_eq_fpBasis_of_finite` | `SFP` | evidence | Records that `(fpBasis p).Finite` and `(Set.range ⇑p).Finite` cut out the same subset of `Fp(D)` — the answer to gap 2 of r0034's docstring. Nothing consumes the answer |

**Recommended for r0020-style commenting-out: rows 2, 3, 5, 6, 8 — five of 184,
2.7%.** That is the rate r0020 measured, not above it.

## 6. Uncited rows that are *not* defects

Fourteen `P` rows have zero uses. Every one is terminal by design and must stay.

| # | Declaration | Module | Paper property |
| -- | ----------- | ------ | -------------- |
| 1 | `injective_embedding` | `Projection` | §3.1 prose, p. 10: "an embedding is an injection (i.e. one-to-one)" |
| 2 | `surjective_projection` | `Projection` | §3.1 prose, p. 10: "a projection is a surjection (i.e. onto)" |
| 3 | `IsNormalIn.antisymm` | `NormalSubposet` | Lemma 4.4, `◁` antisymmetry |
| 4 | `singleton_bot_isNormalIn_of_isNormalIn` | `NormalSubposet` | Lemma 4.4, `{⊥}` is least |
| 5 | `isNormalIn_sUnion_of_mem` | `NormalSubposet` | Lemma 4.4, the union is an upper bound |
| 6 | `isNormalIn_sUnion_le` | `NormalSubposet` | Lemma 4.4, the union is least |
| 7 | `theorem6` | `Theorem6` | Theorem 6 |
| 8 | `TwoMub.shape` | `FinitaryProjectionEmbedding` | Theorem 16 refutation, witness datum |
| 9 | `thm16_first_conjunct` | `FinitaryProjectionEmbedding` | Theorem 16 first conjunct at the witness — the scope guard |
| 10 | `stableCompacts_fConst` | `FinitaryProjectionEmbedding` | Theorem 16 refutation, witness datum: `S_{λx.m₁}` omits `m₂` |
| 11 | `p₁_incomparable_p₂` | `FinitaryProjectionEmbedding` | Theorem 16 refutation, witness datum |
| 12 | `IsPlotkinOrder.minimalUpperBounds_finite` | `MinimalUpperBounds` | §6.1, fact 2, p. 31 |
| 13 | `thm16_positive` | `Section62` | Theorem 16 second conjunct, positively |
| 14 | `thm16_positive_isEmbeddingProjectionPair` | `Section62` | Theorem 16 second conjunct in full over a bounded complete domain |

Rows 8, 10 and 11 are the refutation's witness data. They are uncited because
`not_isGreatest_below_fConst` argues by `decide` on `TwoMub` directly rather than
routing through them, but they are the machine-checked statement of *why* the
refutation holds, and `docs/PropertiesVsTheorems.md` §5 row 3's warning applies:
a superseded module reduced to nothing is a lost finding.

Rows 3–6 are one paper property carried by five declarations. Lemma 4.4 —
"`⟨P(C), ◁⟩` is a cpo with `{⊥}` as its least element" — is recorded as the facts
that constitute it rather than as a subtype instance, which
`NormalSubposet.lean`'s docstring explains and which this audit confirms costs
four uncited declarations and one cited (`IsNormalIn.refl`).

## 7. Two findings that are not labels

**Typeclass over-strength, unmeasured.** Three declarations are stated at a
stronger typeclass context than their statement and proof text uses. Every
consumer supplies the stronger context, so none is a `W` in the round's sense,
and none was confirmed by a build:

| # | Declaration | Declared at | Text uses only |
| -- | ----------- | ----------- | -------------- |
| 1 | `IsProjection.isLUB_val_image` | `[CompletePartialOrder α]` | `≤`, `IsLUB`, `p.monotone`, `apply_of_mem_range`, `le` — all at `[Preorder α]`, where `ScottHom` and `IsProjection` live |
| 2 | `isLUB_of_isLUB_val_image` | `[CompletePartialOrder α]` | `IsLUB` reindexing along `Subtype.val` |
| 3 | `directedOn_range_of_monotone` | `[PartialOrder α]` | `DirectedOn`, `hx.monotone`, `max` on `ℕ` |

**Mathlib is reimplemented once.** `FinitaryProjectionPoset.exists_minimal_mem_of_finite`
hand-rolls "a finite nonempty set has a minimal member", while
`MinimalUpperBounds.hasCompleteMub_of_isNormalIn` calls Mathlib's
`Set.Finite.exists_le_minimal` for the same purpose, four modules away.

## 8. Full table — 184 rows

`self` counts code uses in the declaring module outside its own signature;
`other` counts code uses elsewhere. Both exclude comments and docstrings. Where
a final name component is shared across namespaces the counts are a union and the
cell says so.

### `Projection.lean`

| # | Declaration | Label | Evidence |
| -- | ----------- | ----- | -------- |
| 1 | `IsProjection.idem` | A | accessor `h.1 x`; not `@[simp]`; 21 cross-module uses (PRep, PRepFun, UniversalDomain, Skeleton/Section6) |
| 2 | `IsProjection.le` | A | accessor `h.2 x`; not `@[simp]`; 78 cross-module uses — the most-applied lemma in the area |
| 3 | `IsProjection.apply_of_mem_range` | S | 52 cross-module uses; `FinitaryProjection`, `Theorem6`, `PRepFun` ×9, `PRep` ×7 |
| 4 | `IsEmbeddingProjectionPair.injective_embedding` | P | §3.1 prose, p. 10 verified; 0 uses, terminal by design |
| 5 | `IsEmbeddingProjectionPair.surjective_projection` | P | §3.1 prose, p. 10 verified; 0 uses, terminal by design |
| 6 | `IsEmbeddingProjectionPair.isProjection_comp` | — | **not a live declaration**: inside the `/- UNUSED … -/` block comment, lines 77–95. Counted by `counts.sh` and `module-counts.sh` |
| 7 | `IsProjection.map_bot` | S | 18 cross-module uses (`PRepSum` ×11, `PRepFun` ×5); self 2 |
| 8 | `IsProjection.bot_mem_range` | S | `FinitaryProjection`, `PRepFun`; self 1 |
| 9 | `directedOn_val_image` | S | 9 cross-module (`FinitaryProjectionPoset` ×3, `IdealCompletion` ×3); self 3 |
| 10 | `IsProjection.apply_sSup_of_directed` | S | `Skeleton/Section6`, `UniversalDomain`; self 2 |
| 11 | `IsFinitaryProjection.isProjection` | A | accessor `h.choose`; 51 cross-module uses (`PRepFun` ×18, `SFP` ×11) |

### `FinitaryProjection.lean`

| # | Declaration | Label | Evidence |
| -- | ----------- | ----- | -------- |
| 12 | `IsProjection.isLUB_val_image` | S | `Theorem6`, `FinitaryProjectionPoset` ×2, `PRepFun`, `PRep`; final-name collision with `IsClosure.isLUB_val_image`. Over-strength, §7 row 1 |
| 13 | `IsProjection.isCompactElement_iff` | P | **Lemma 5, first sentence**, p. 10 verified; 15 cross-module uses (`PRep` ×8, `Theorem6` ×4) |
| 14 | `IsFinitaryProjection.domain` | A | accessor `h.choose_spec`; 13 cross-module uses |
| 15 | `IsFinitaryProjection.isNormalIn_compacts` | P | **Lemma 5, second sentence**, p. 10 verified; `Theorem6` ×2, `FinitaryProjectionPoset`, `SFP` |

### `NormalSubposet.lean`

| # | Declaration | Label | Evidence |
| -- | ----------- | ----- | -------- |
| 16 | `IsNormalIn.subset` | A | accessor `h.1`; 63 cross-module uses (`JungFinite` ×10, `FinitaryProjectionPoset` ×9); self 8 |
| 17 | `IsNormalIn.nonempty` | A | accessor `(h.2 x hx).1`; 31 cross-module uses; self 6 |
| 18 | `IsNormalIn.directedOn` | A | accessor `(h.2 x hx).2`; 20 cross-module uses; self 5 |
| 19 | `IsNormalIn.refl` | S | `Colimit:575`, `FpEmbedding:346`, `FinitaryProjectionPoset:521,599` — grep-confirmed on the qualified name. Also Lemma 4.4's reflexivity |
| 20 | `IsNormalIn.trans` | P | **Lemma 4.1**, p. 10 verified. Use count not measurable by final-name matching (`trans` collides with dot-notation `≤`-transitivity throughout) |
| 21 | `IsNormalIn.mono_right` | P | **Lemma 4.2**, p. 10 verified; `FinitaryProjectionPoset:645,647` |
| 22 | `IsNormalIn.antisymm` | P | **Lemma 4.4**, `◁` antisymmetry; **0 uses anywhere**, grep-confirmed on the qualified name |
| 23 | `IsNormalIn.bot_mem` | P | **Lemma 4.3**, p. 10 verified; `Bifinite`, `IdealCompletion` ×4, `BifiniteUniversal` ×2 |
| 24 | `singleton_bot_isNormalIn` | S | `Colimit:509` |
| 25 | `singleton_bot_isNormalIn_of_isNormalIn` | P | **Lemma 4.4**, `{⊥}` is least; 0 uses |
| 26 | `isNormalIn_sUnion` | P | **Lemma 4.4**, suprema exist; `FinitaryProjectionPoset:650` |
| 27 | `isNormalIn_sUnion_of_mem` | P | **Lemma 4.4**, the union is an upper bound; 0 uses |
| 28 | `isNormalIn_sUnion_le` | P | **Lemma 4.4**, the union is least; 0 uses |

### `NormalProjection.lean`

| # | Declaration | Label | Evidence |
| -- | ----------- | ----- | -------- |
| 29 | `IsNormalIn.nonempty_inter_Iic` | S | `SFP:352`; self 1 |
| 30 | `IsNormalIn.directedOn_inter_Iic` | S | `Theorem6` ×4, `SFP` ×2, `FpEmbedding`; self 8 |
| 31 | `normalFun_le` | S | self 3 (`monotone_normalFun`, `isProjection_normalHom`, `normalFun_of_mem`) |
| 32 | `le_normalFun` | S | `SFP` ×2, `Skeleton/Lemma17`, `ClosureProperties/StrictFunction`; self 5 |
| 33 | `monotone_normalFun` | S | `ClosureProperties/StrictFunction`, `Skeleton/Lemma17`; self 2 |
| 34 | `scottContinuous_normalFun` | S | self 1 — the `normalHom` definition |
| 35 | `coe_normalHom` | A | `@[simp]`; named in `Theorem6`'s `simpa [coe_normalHom]` and once in-file |
| 36 | `isProjection_normalHom` | S | `Theorem6` ×7, `Skeleton/Lemma17` ×2, `ClosureProperties/StrictFunction` ×2 |
| 37 | `normalFun_of_mem` | S | `ClosureProperties/StrictFunction` ×2, `SFP`, `Skeleton/Lemma17`; self 1 |
| 38 | `range_normalHom_inter_compacts` | S | `Theorem6` ×4, `FinitaryProjectionPoset` — one half of Theorem 6's correspondence |
| 39 | `normalHom_mono` | S | `Theorem6`, `FinitaryProjectionPoset` |
| 40 | `IsProjection.range_mono` | S | `Theorem6`, `FinitaryProjectionPoset` |

### `Theorem6.lean`

| # | Declaration | Label | Evidence |
| -- | ----------- | ----- | -------- |
| 41 | `isLUB_of_isLUB_val_image` | S | `FinitaryProjectionPoset:221`; self 1. Over-strength, §7 row 2 |
| 42 | `val_image_compactsBelow` | S | `PRepFun` ×4; self 4 |
| 43 | `isAlgebraic_range_normalHom` | S | self 1 — `isFinitaryProjection_normalHom` |
| 44 | `val_mem_of_isCompactElement` | S | self 1 — `countable_compacts_range_normalHom` |
| 45 | `countable_compacts_range_normalHom` | S | self 1 — `isFinitaryProjection_normalHom` |
| 46 | `isFinitaryProjection_normalHom` | S | `FinitaryProjectionPoset`, `SFP`; self 1 |
| 47 | `normalFun_range_inter_compacts` | S | `FinitaryProjectionPoset:568`; self 1 |
| 48 | `theorem6` | P | **Theorem 6**, pp. 10–11 verified; **0 uses, terminal by design** |

### `FinitaryProjectionPoset.lean`

| # | Declaration | Label | Evidence |
| -- | ----------- | ----- | -------- |
| 49 | `ScottHom.id_apply` | A | `@[simp]`; `SFP:460` (`rw [ScottHom.id_apply]`) |
| 50 | `mem_Fp` | A | `@[simp]`; 38 cross-module uses (`PRepFun` ×23, `PRepSum` ×8) |
| 51 | `IsFinitaryClosure.isClosure` | A | accessor `h.choose`; `PRepresentable`; self 1 |
| 52 | `mem_Fc` | A | `@[simp]`; `PRepresentable` |
| 53 | `Fp.le_def` | A | `Iff.rfl`, records that `Fp(D)`'s order is pointwise; **0 code uses**, 3 docstring mentions |
| 54 | `Fc.le_def` | A | `Iff.rfl`, records that `Fc(D)`'s order is pointwise; **0 code uses**, 1 docstring mention |
| 55 | `IsClosure.apply_sSup_val_image_of_directed` | S | self 1 — `IsClosure.isLUB_val_image` |
| 56 | `IsClosure.isLUB_val_image` | S | self 1 — `isCompactElement_apply`; final-name collision with row 12 |
| 57 | `IsClosure.isCompactElement_apply` | S | self 1 — `closureApprox_subset` |
| 58 | `closureApprox_nonempty` | S | self 3 |
| 59 | `directedOn_closureApprox` | S | self 4 |
| 60 | `closureApprox_subset` | S | self 3 |
| 61 | `isLUB_closureApprox` | S | self 4 |
| 62 | `IsClosure.isAlgebraic_range` | S | self 1 — `domain_range` |
| 63 | `IsClosure.compacts_range_subset` | S | self 1 — `countable_compacts_range` |
| 64 | `IsClosure.countable_compacts_range` | S | `PRep` ×2; self 1 |
| 65 | `IsClosure.domain_range` | P | **Lemma 19**, p. 33 verified: "If `D` is a domain and `r : D → D` satisfies `r∘r = r ⊒ id`, then `im(r)` is a domain". `Skeleton/Section6`'s `lem19` records only the cpo half — a cross-area comparison for tier 2. self 1 |
| 66 | `isClosure_id` | S | `RecursiveDomain` ×2; self 2 |
| 67 | `mem_Fc_iff` | S | self 4. Formalizes §7.1's sentence before Lemma 19 ("the requirement that `im(r)` be a domain is unnecessary"), which is Lemma 19's corollary rather than a separate property |
| 68 | `id_mem_Fc` | S | self 2 — `Fc.completePartialOrder` |
| 69 | `id_le_of_mem_Fc` | S | self 3 |
| 70 | `directedOn_insert_id_val_image` | S | self 1 — `Fc.completePartialOrder` |
| 71 | `exists_minimal_mem_of_finite` | S | self 1 — `exists_isMinimalUpperBound`. Reimplements Mathlib `Set.Finite.exists_le_minimal`, §7 |
| 72 | `IsPlotkinOrder.exists_isMinimalUpperBound` | S | self 1 — `isNormalIn_sInter` |
| 73 | `IsNormalIn.mem_of_isMinimalUpperBound` | S | self 1 — `isNormalIn_sInter` |
| 74 | `isNormalIn_sInter` | S | self 2 — `normalClosure_isNormalIn`, `fpMeet_isNormalIn` |
| 75 | `subset_normalClosure` | S | `SFP` ×3; self 1 |
| 76 | `normalClosure_subset` | S | self 2 |
| 77 | `normalClosure_isNormalIn` | S | `SFP` ×2; self 1 |
| 78 | `normalClosure_finite` | S | `SFP` ×2; self 1 |
| 79 | `exists_mem_of_finite_subset_sUnion` | S | self 1 — `isCompactElement_toFp_of_finite` |
| 80 | `fpBasis_isNormalIn` | S | `FpEmbedding`, `Section62`, `SFP`; self 11 |
| 81 | `normalHom_fpBasis` | S | `FpEmbedding`, `SFP`; self 2 |
| 82 | `fpBasis_toFp` | A | `@[simp]`; `Section62` ×3; self 9 |
| 83 | `Fp.le_iff_fpBasis_subset` | S | `Section62` ×6; self 14. Theorem 6 as an order isomorphism — the `P` for Theorem 6 is row 48 |
| 84 | `fpMeetFamily_isNormalIn` | S | self 1 — `fpMeet_isNormalIn` |
| 85 | `fpMeet_isNormalIn` | S | self 2 — `isGLB_fpMeet`, `Fp.completeLattice` |
| 86 | `isGLB_fpMeet` | S | self 1 — `Fp.completeLattice` |
| 87 | `fpBasis_subset_sUnion_of_isLUB` | S | self 1 — `isCompactElement_toFp_of_finite` |
| 88 | `isCompactElement_toFp_of_finite` | S | self 1 — `Fp.isCompactlyGenerated` |
| 89 | `isLUB_compactsBelow_fp` | S | self 1 — `Fp.isCompactlyGenerated` |
| 90 | `Fp.isCompactlyGenerated` | P | **Theorem 16, first conjunct**, p. 33 verified: "`Fp(D)` … is an algebraic lattice"; `Skeleton/Section6b:1` (`thm16`) |

### `FinitaryProjectionEmbedding.lean`

| # | Declaration | Label | Evidence |
| -- | ----------- | ----- | -------- |
| 91 | `exists_upperBound_mem_of_finite` | S | `Skeleton/Section6` ×2; self 1. **Earlier partner of `D`-pair 2** |
| 92 | `isLUB_of_finite_directed` | S | self 3. **Earlier partner of `D`-pair 3** |
| 93 | `isCompactElement_of_finite` | S | self 2 — `domain_of_finite`, `stableCompacts_fConst` |
| 94 | `domain_of_finite` | S | self 2 — `isFinitaryProjection_of_finite`, `TwoMub.instDomain` |
| 95 | `scottContinuous_of_monotone_of_finite` | S | self 2 — `p₁`, `p₂` |
| 96 | `isFinitaryProjection_of_finite` | S | self 2 — `P₁`, `P₂` |
| 97 | `isGreatest_of_section` | S | self 1 — `not_exists_monotone_projection`. The obstruction, stated for a merely monotone `s` so it rules out continuous `s` a fortiori |
| 98 | `fpBasis_subset_stableCompacts` | S | `Section62:272`; self 1 |
| 99 | `le_of_fpBasis_subset_stableCompacts` | S | `Section62` ×2; self 1 |
| 100 | `Fp.le_iff_fpBasis_subset_stableCompacts` | U | **0 code uses**; named in three modules' docstrings as "the exact criterion". Both halves (rows 98, 99) are cited. §5 row 1 |
| 101 | `stableCompacts_val` | S | `Section62:426` |
| 102 | `TwoMub.bot_le'` | S | self 2 — `exists_isLUB`, `instCompletePartialOrder` |
| 103 | `TwoMub.exists_isLUB` | S | self 1 — `isLUB_sSupAux` |
| 104 | `TwoMub.isLUB_sSupAux` | S | self 1 — `instCompletePartialOrder` |
| 105 | `TwoMub.isBifinite` | S | self 1 — `thm16_first_conjunct` |
| 106 | `TwoMub.shape` | P | **Theorem 16 refutation, witness datum**: `TwoMub` is bifinite and not bounded complete, by `decide`; 0 uses |
| 107 | `TwoMub.thm16_first_conjunct` | P | **Theorem 16, first conjunct at `TwoMub`** — the scope guard that makes the refutation one of the second conjunct alone; 0 uses |
| 108 | `TwoMub.monotone_p₁Fun` | S | self 1 — `p₁` |
| 109 | `TwoMub.monotone_p₂Fun` | S | self 1 — `p₂` |
| 110 | `TwoMub.isProjection_p₁` | S | self 1 — `P₁` |
| 111 | `TwoMub.isProjection_p₂` | S | self 1 — `P₂` |
| 112 | `TwoMub.p₁_le_fConst` | S | self 1 — `not_isGreatest_below_fConst` |
| 113 | `TwoMub.p₂_le_fConst` | S | self 1 — `not_isGreatest_below_fConst` |
| 114 | `TwoMub.stableCompacts_fConst` | P | **Theorem 16 refutation, witness datum**: `S_{λx.m₁} = {⊥,a,b,m₁}` omits `m₂`; 0 uses |
| 115 | `TwoMub.p₁_incomparable_p₂` | P | **Theorem 16 refutation, witness datum**: two incomparable finitary projections below `f`; 0 uses |
| 116 | `TwoMub.not_isGreatest_below_fConst` | S | self 1 — `not_exists_monotone_projection` |
| 117 | `TwoMub.not_exists_monotone_projection` | P | **Theorem 16, second conjunct — refuted**, §6.2 p. 33 verified; self 1 |
| 118 | `TwoMub.not_isEmbeddingProjectionPair` | P | The same refutation in the paper's own §3.1 vocabulary; 0 uses, terminal |

### `Bifinite.lean`

| # | Declaration | Label | Evidence |
| -- | ----------- | ----- | -------- |
| 119 | `IsPlotkinOrder.exists_finite_normal` | A | accessor: the body is `h u hu hsub`, the `def IsPlotkinOrder` eta-expanded. Not `@[simp]`; 0 uses |
| 120 | `IsPlotkinOrder.exists_finite_normal_empty` | U | 0 uses; §5 row 3 |
| 121 | `IsBifinite.bot_mem_of_normal` | U | 0 uses **and** a vacuous `_h : IsBifinite α`; §5 row 2 |

### `MinimalUpperBounds.lean`

| # | Declaration | Label | Evidence |
| -- | ----------- | ----- | -------- |
| 122 | `mem_upperBoundsIn` | A | `Iff.rfl` accessor; not `@[simp]`; 0 uses |
| 123 | `upperBoundsIn_subset` | A | accessor `Set.inter_subset_left`; `JungFinite` ×2; self 1 |
| 124 | `upperBoundsIn_empty` | A | `@[simp]`, **never named**. Fires in `isNormalIn_of_isMubClosed:190`'s `by simpa using hx`, whose goal is `x ∈ upperBoundsIn A ∅` with `upperBoundsIn` a non-reducible `def`. Argument, not measurement — removing the tag was not tested |
| 125 | `minimalUpperBounds_subset` | A | accessor `hm.1`; `JungFinite` ×3; self 1 |
| 126 | `mem_upperBounds_of_mem_minimalUpperBounds` | A | accessor `hm.1.2`; self 1 |
| 127 | `exists_mem_upperBounds_of_directedOn` | D | **`D`-pair 1**: same statement and same proof script as `ScottDomains.exists_upperBound_mem_of_finite` (`Skeleton/Section6.lean`), same namespace. `ContinuousConstruction` ×2, `JungSFP` ×3; self 1 |
| 128 | `IsNormalIn.exists_mem_le_of_finite` | S | self 3. The paper's "(why?)" step, §6.1 p. 31 |
| 129 | `isNormalIn_of_isMubClosed` | S | self 2, `ContinuousConstruction` ×1 |
| 130 | `subset_mubStep` | S | self 1 — `mubIter_subset_succ` |
| 131 | `mubStep_mono` | S | `JungFinite` ×1 |
| 132 | `mubIter_subset_succ` | S | self 1 — `mubIter_mono` |
| 133 | `mubIter_mono` | S | `JungFinite` ×1; self 2 |
| 134 | `mubIter_subset_mubClosure` | S | `JungFinite` ×1; self 2 |
| 135 | `subset_mubClosure` | S | self 1 — `isPlotkinOrder_iff_mubClosure` |
| 136 | `exists_mubIter_of_finite_subset` | S | self 1 — `isMubClosed_mubClosure` |
| 137 | `isMubClosed_mubClosure` | S | self 1 — `isPlotkinOrder_iff_mubClosure` |
| 138 | `mubStep_subset` | S | self 1 — `mubIter_subset` |
| 139 | `mubIter_subset` | S | `JungFinite` ×2; self 2 |
| 140 | `mubClosure_subset` | S | self 2 — `isPlotkinOrder_iff_mubClosure` |
| 141 | `mem_minimalUpperBounds_singleton` | S | self 1 — but its only consumer is row 142, itself a `U` |
| 142 | `mubStep_eq_of_subset` | U | 0 uses; definitional adequacy for the paper's `U`. §5 row 4 |
| 143 | `minimalUpperBounds_subset_of_isNormalIn` | S | self 3 |
| 144 | `minimalUpperBounds_finite_of_isNormalIn` | S | self 1 — row 150 |
| 145 | `hasCompleteMub_of_isNormalIn` | P | **§6.1, fact 1**, p. 31 verified; self 2 |
| 146 | `mubClosure_subset_of_isNormalIn` | P | **§6.1, fact 3**, p. 32 verified; self 1 |
| 147 | `isPlotkinOrder_iff_mubClosure` | S | self 2, plus row 152. The `⟸` direction is the development's own, not the paper's |
| 148 | `isPlotkinOrder_iff` | U | 0 uses; docstring claim measured false. §5 row 5 |
| 149 | `exists_of_not_isPlotkinOrder` | U | 0 uses; serves Smyth's abandoned case split. §5 row 6 |
| 150 | `IsPlotkinOrder.minimalUpperBounds_finite` | P | **§6.1, fact 2**, p. 31 verified; 0 uses |
| 151 | `isBifinite_iff_mubClosure` | S | `JungFinite:709` — **step 5 of the live Theorem 18 route** (Plotkin's Theorem 1.32) |

### `Section62.lean`

| # | Declaration | Label | Evidence |
| -- | ----------- | ----- | -------- |
| 152 | `isGreatest_fp_le_of_hasGreatestStableNormal` | S | self 1 — `thm16_positive` |
| 153 | `thm16_positive` | P | **Theorem 16, second conjunct, positively** under `HasGreatestStableNormal`; the literal negation of row 117; 0 uses, terminal |
| 154 | `stableCompacts_isNormalIn` | S | self 2 — row 155, `fpOfStable` |
| 155 | `hasGreatestStableNormal_of_boundedComplete` | U | 0 uses; the non-vacuity witness. §5 row 7 |
| 156 | `fpBasis_fpOfStable` | A | `@[simp]`; self 5 |
| 157 | `fpOfStable_le` | S | self 1 — row 160 |
| 158 | `monotone_fpOfStable` | S | self 1 — `scottContinuous_fpOfStable` |
| 159 | `scottContinuous_fpOfStable` | S | self 1 — the `fpSection` definition |
| 160 | `thm16_positive_isEmbeddingProjectionPair` | P | Theorem 16's second conjunct in full over a bounded complete domain, in §3.1's embedding–projection vocabulary; 0 uses, terminal |
| 161 | `apply_eq_self_of_mem_mubIter` | W | §4 row 1: the `hgA` hypothesis the live route cannot supply; consumer `JungFinite` declared `apply_eq_self_of_mem_mubIter_compacts` without it. self 1 |
| 162 | `apply_eq_self_of_mem_mubClosure` | W | §4 row 2: **0 uses**; `JungFinite:652` uses its own `apply_eq_self_of_mem_mubClosure_compacts` |
| 163 | `directedOn_range_of_monotone` | S | `JungFinite:654`. Over-strength, §7 row 3 |
| 164 | `not_isCompactElement_of_isLUB_strictMono` | S | `JungFinite:664` — the terminal contradiction of Jung's Lemma 2.2 |

### `SFP.lean`

| # | Declaration | Label | Evidence |
| -- | ----------- | ----- | -------- |
| 165 | `exists_upperBound_of_finite_subset` | D | **`D`-pair 2**: `FpEmbedding.exists_upperBound_mem_of_finite` with the first two arguments swapped. self 2 |
| 166 | `exists_greatest_of_finite` | S | self 1 — `exists_mem_isLUB_of_finite` |
| 167 | `exists_mem_isLUB_of_finite` | D | **`D`-pair 3**: `FpEmbedding.isLUB_of_finite_directed`, same argument order, binder name only. self 2 |
| 168 | `isCompactElement_of_mem_range_of_finite` | S | `ClosureProperties/StrictFunction`, `Skeleton/Lemma17` ×2; self 2 |
| 169 | `range_subset_compacts_of_finite` | S | self 4. The paper's "whenever `im(p)` is finite, `im(p) ⊆ K(D)`", §6.1 p. 30 |
| 170 | `range_inter_compacts_of_finite` | U | 0 uses; `thm14_forward:325` writes the intersection directly. §5 row 8 |
| 171 | `eq_of_range_eq` | S | self 1 — `countable_of_subset_finiteImage` |
| 172 | `isProjection_const_bot` | S | self 2 |
| 173 | `eq_bot_of_mem_range_const_bot` | S | self 2 |
| 174 | `range_const_bot_finite` | S | self 1 — `thm14_forward` |
| 175 | `isFinitaryProjection_const_bot` | S | self 1 — `thm14_forward` |
| 176 | `thm14_forward` | P | **Theorem 14, 1 → 2**, p. 30 verified; `Skeleton/Recovered` |
| 177 | `range_normalHom_of_finite` | S | self 3. **Earlier partner of `D`-pair 4** |
| 178 | `le_normalHom_of_range_subset` | S | self 2 — `directedOn_of_normalHom_mem` |
| 179 | `range_toFp_eq` | D | **`D`-pair 4**: equal to row 177 by `rfl`, and declared at `[Domain α]` where row 177 needs only `[IsAlgebraic α]`. 0 uses |
| 180 | `range_eq_fpBasis_of_finite` | U | 0 uses. §5 row 9 |
| 181 | `isFinitaryProjection_and_finite_normalHom` | S | self 1 — `thm14_converse` |
| 182 | `countable_of_subset_finiteImage` | S | self 1 — `thm14_converse` |
| 183 | `directedOn_of_normalHom_mem` | S | self 1 — `thm14_converse` |
| 184 | `isLUB_id_of_normalHom_mem` | S | self 1 — `thm14_converse` |
| 185 | `thm14_converse` | P | **Theorem 14, 2 → 1**, p. 30 verified; `Skeleton/Recovered` |

## 9. Build state

`scripts/compile.sh -r r0038` on branch `agent2`:

    exit 0 · wall 0:02.91 · mem 1655 MiB single · jobs 1224 · lake errors 0 · sorry 1 · other warnings 0

Log: `ScottDomains/logs/compile-20260808-095322.agent2.log`.

`git diff --stat HEAD` over the tracked tree is empty: **no existing `.lean` file
was touched, and no existing proof changed.** `scripts/counts.sh` reports 73
modules / 28037 lines / 1317 theorems / 1 `sorry`. The deltas against the
round's start are entirely the new audit module:

| # | Measure | Before | After | Delta |
| -- | ------- | ------ | ----- | ----- |
| 1 | modules | 72 | 73 | +1 (`Audit/Projections.lean`) |
| 2 | theorems | 1308 | 1317 | +9 (the four kernel-checked pairs) |
| 3 | `sorry` | 1 | 1 | 0 |
| 4 | numbered results | — | — | 0 |

The theorem delta is the plan's §"Deliverable, per agent" row 3 exception. If
orchestrator step 5 requires `counts.sh` to be byte-identical to `702def0`,
`ScottDomains/ScottDomains/Audit/Projections.lean` is the single file to drop,
and this report carries its content.
