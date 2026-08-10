---
round: r0049
from: agent7
to: orchestrator
subject: thm26-and-added-binders
date: 2026-0809-17:05
started: 2026-0809-16:44
finished: 2026-0809-17:05
related:
  - plans/r0049-plan-from-orchestrator-to-orchestrator-six-at-the-unproven.md
  - reports/r0044-report-from-agent1-to-orchestrator-sneq-s2-s4.md
  - reports/r0044-report-from-agent2-to-orchestrator-sneq-s5-s7.md
  - reports/r0047-report-from-agent4-to-orchestrator-boundedcomplete.md
---

# r0049 agent7 — Theorem 26's `hs` is a repair of a printed defect, and two more `S≠` rows close

## 1. The answer, in one paragraph

`hs : ∀ i, 0 < s i` **cannot be dropped, and it is not a defect of ours.**
Theorem 26 **as printed** is false for every signature with two or more 0-ary
slots — including the paper's own worked signature `(2,0,0,0,0,0)` — and the
refutation is kernel-checked at a transcription that grants every hypothesis the
printed sentence carries. The argument on record at `Combinator.lean:60–72` was
correctly rejected by r0044's agent2 and by `docs/Status.md`: its inference is
invalid, and this round proves that too. The conclusion it drew is nevertheless
right, by a different argument that never mentions `fst ∘ ψ = id`. Row 12 of
r0044 agent2's table therefore moves from **kind 1 (a defect of ours)** to
**kind 3 (a repair of a printed defect)**, and the paper's printed-defect count
goes from nine to **ten**.

Of the 13 `S≠` rows attributable to this development, **2 moved this round**
(row 45, row p9b), **2 had already moved in r0047** and are re-measured here
(Lemma 17 `→` and `⊸`), **1 is reclassified** (Theorem 26), and **8 remain open**
with a named residue each. Defects attributable to us: **13 → 8**.

## 2. The Theorem 26 verdict, with its evidence

### 2.1 The paper, checked before it was convicted

`scripts/a7-thm26-page.sh` re-extracts printed pp. 38–39 (PDF pages 39–40; PDF
page `n` is printed page `n − 1` throughout). Verbatim:

> By a continuous algebra we mean a domain with various continuous operations
> singled out. In particular, our λ-calculus model can be considered as a
> continuous algebra of signature `(2,0,0,0,0,0)`. The binary operation is the
> operation of functional application. Here, `0` indicates a 0-ary operation,
> which is just a constant.

> **Theorem 26** Given a signature `(s₁, s₂, …, s_n)`, there are combinations
> `F₁, F₂, …, F_n` defining operations on `D` of these arities such that whenever
> a continuous algebra of this signature is given on a domain `A` that is a
> retract of `D`, then `A` can be made isomorphic to a subalgebra of this fixed
> algebra structure on `D`.

Arity 0 is admitted, and the paper's own example carries **five** 0-ary slots.
The `hs` binder therefore does exclude signatures the paper intends.

### 2.2 The argument on record is invalid, and this round proves it

`Combinator.lean:60–72` derives its contradiction from `fst(ψ(x)) = x`, then
concludes from two one-point algebras `A = {a}`, `B = {b}` that `a = fst(Fᵢ) = b`.
`fst ∘ ψ = id` is a property of the paper's *construction* and of `thm26`'s own
conclusion; the printed statement asks only for an isomorphism onto *some*
subalgebra.

`R49.Agent7.isAlgEmbedding_const_of_subsingleton` makes the objection precise and
kernel-checked: at a one-element carrier, with every arity `0` and every `Fᵢ`
interpreting to the same `c`, the **constant map** `fun _ => c` is an injective
homomorphism onto the subalgebra `{c}`. Two distinct one-point algebras are
isomorphic to the *same* subalgebra, and no contradiction follows from the
one-point pair alone.

### 2.3 The genuine counterexample

What the one-point algebra does is not contradict — it **collapses**. Because the
combinations `F₁, …, F_n` are quantified *before* the algebra, two instances of
the printed statement speak about the same `Fᵢ`, `Fⱼ`:

| # | instance | forces |
| -- | -------- | ------ |
| 1 | the algebra with `oᵢ = oⱼ` | `Fᵢ = h₁(oᵢ) = h₁(oⱼ) = Fⱼ` |
| 2 | the algebra with `oᵢ ≠ oⱼ` | `Fᵢ = h₂(oᵢ) ≠ h₂(oⱼ) = Fⱼ`, by injectivity of `h₂` |

`R49.Agent7.not_thm26Printed_of_two_zero_arities` is that contradiction:

    @not_thm26Printed_of_two_zero_arities :
      ∀ {D : Type u_1} [CompletePartialOrder D] (M : Combinator.LambdaModel D)
        [Domain D] {n : ℕ} (s : Fin n → ℕ) {i j : Fin n},
        i ≠ j → s i = 0 → s j = 0 → ∀ {x y : D}, x ≠ y → ¬ Thm26Printed M s

    depends on axioms: [propext, Classical.choice, Quot.sound]

Both instances are the carrier `D` itself with the identity retraction and
constant operations, so both are continuous algebras of the signature on a
domain that is a retract of `D`. Nothing about `ψ`, `pair`, `fst` or the paper's
fixed-point equation enters.

### 2.4 Why the transcription is the generous one

A refutation is only as strong as the hypotheses it grants. `Thm26Printed` grants
all three the printed sentence carries — `A` is a `Domain`, `A` is a retract of
`D` via a Scott-continuous pair `(e, p)` with `p ∘ e = id`, and the operations are
Scott-continuous argumentwise — and asks for the **weakest** reading of the
conclusion, an injective homomorphism. Two consequences, both deliberate:

1. `isSubalgebraOf_range` proves the image of such a homomorphism really is a
   subalgebra (closed under every `Fᵢ`, read applicatively, exactly as
   `thm26_subalgebra` reads it). So "isomorphic to a subalgebra" and "admits an
   injective homomorphism" name the same fact, and nothing is lost by not
   carrying the subalgebra as data.
2. Any order-theoretic strengthening of "isomorphic" — requiring `h` continuous,
   or an order isomorphism onto its image — only **strengthens** what is being
   refuted, so the refutation survives every such reading.

A 0-ary operation carries no argument, so the argumentwise-continuity condition
is vacuous at the slots that bite; the witnesses' operations are constant maps
and are continuous anyway (`ScottContinuous.const`).

### 2.5 The one caveat, stated rather than buried

The refutation instantiates the printed statement at `A := D`, which needs
`[Domain D]`. That is exactly what **Theorem 25 as printed** asserts of `D`
("there is a non-trivial **domain** `D` …"), and exactly what
`Universality.thm25` does **not** currently deliver — rows 9–11 of the table in
§3 are that gap. So the refutation lands at the paper's own `D`, and cannot yet
be composed with this development's `thm25` until those rows close. It is
hypothesis-parametric and kernel-checked either way.

### 2.6 The separate, weaker fact about our own statement

`Combinator.thm26`'s Lean statement carries the extra conjunct `fst(ψ a) = a`,
which the printed theorem does not. That conjunct makes **one** 0-ary slot
already fatal: `Fᵢ` is fixed before the operations are chosen, so `fst(Fᵢ)` would
have to equal every constant at once.
`R49.Agent7.not_thm26_statement_of_zero_arity` is that refutation
(`[propext, Classical.choice, Quot.sound]`). It is a statement about our
transcription, not about the paper, and it is reported separately for that
reason. Both results agree that `hs` cannot be dropped.

### 2.7 Consequences for the documents

| # | Location | Says | Should say |
| -- | -------- | ---- | ---------- |
| 1 | `Combinator.lean:60–72` | Theorem 26 is false at arity 0, "by the following argument, which is stated here and is *not* Lean-checked", the argument turning on `fst(ψ(x)) = x` | the conclusion is right and now Lean-checked (`not_thm26Printed_of_two_zero_arities`); the argument printed there is **not** the proof — it needs two 0-ary slots and never uses `fst ∘ ψ = id` |
| 2 | `docs/Status.md` result 26 | "`hs` is a defect of ours, not a repair … To settle it: exhibit a genuine arity-0 counterexample to the printed conclusion, or drop `hs`" | settled in the first direction; `hs` is a repair. Result 26 is proved as repaired |
| 3 | `docs/Status.md` "Defects in the printed paper" | **Nine**; row 1 of the "suspected / actually" table reads "Theorem 26 false at arity 0 → refutes the paper's *proof*, not its statement" | **Ten.** That row moves out of the suspected-and-refuted table into the printed-defect list: the statement is false for any signature with ≥ 2 zeros. The *stated reason* on record was still wrong, which is why the row belonged there until now |
| 4 | `docs/Status.md` counts row 9 | 18 `S≠` (13 ours, 5 repairs) | 18 `S≠` (**8** ours, **6** repairs) after this round |
| 5 | `PaperInventory.md` row 2c | Theorem 26 listed as a qualification on the numbered results | it is a repair, alongside Lemma 9 items 3 and 5 |

No existing declaration and no existing docstring was edited. Item 1 is a
correction the orchestrator may apply; agent7 is not authorized to edit a
declaration in place and left the file untouched.

## 3. The thirteen rows, one by one

Every type below is `#check @d` against the built `.olean`, and every axiom
footprint `#print axioms` in the same run —
`scripts/a1-probe.sh scripts/a7-r49-rows.lean`, one command. The r0044 tables are
one round older than r0047's removals, so the row population was re-derived
against the environment rather than inherited.

| # | Row (paper, printed p.) | Declaration measured | r0044 kind | r0049 status |
| -- | ---------------------- | -------------------- | :--------: | ------------ |
| 1 | recovery formula, p. 9 | `Kleene.sSup_recoverAt` | 1, added binder | **moved** — `R49.Agent7.sSup_recoverAt_bcFree` |
| 2 | "there are domains `D, E` with `D → E` not a domain", p. 11 | `JungSFP.lemma213` | 1, missing witness | **open** — residue named |
| 3 | "the strict step functions form a basis", p. 12 | `PRepFun.strictHomIsAlgebraic` | 1, missing conclusion | **open** — residue named; the binder is *not* the defect |
| 4 | Lemma 17, `D → E`, p. 32 | `ClosureProperties.lem17_fun` | 1, added binder | **moved in r0047** — `R47.Agent4.lem17_fun`, re-measured |
| 5 | Lemma 17, `D ⊸ E`, p. 32 | `ClosureProperties.lem17_strictFun` | 1, added binder | **moved in r0047** — `R47.Agent4.lem17_strictFun`, re-measured |
| 6 | p9b, the stabilizing index, p. 31 | `JungFinite.mubDiff_nonempty` | 2, incorrectly specified | **moved** — `R49.Agent7.exists_mubIter_eq_succ_of_isNormalIn` |
| 7 | p16, the Lemma 17 `♮` sketch, p. 32 | `PowerdomainMap.isProjection_plotkin` | 1, 3 of 4 conjuncts | **open** — residue named |
| 8 | Lemma 24a, "non-trivial **domains** `D` and `E`", p. 37 | `Universality.lem24` | 1, "is a domain" | **open** — obstruction named |
| 9 | Lemma 24b, `D ≅ D → E`, p. 37 | `Universality.lem24` | 1 | **open** — same |
| 10 | Theorem 25a, "non-trivial **domain** `D`", p. 37 | `Universality.thm25` | 1 | **open** — same |
| 11 | Theorem 25b, `D ≅ D → D`, p. 37 | `Universality.thm25` | 1 | **open** — same |
| 12 | Theorem 25c, image of a closure on `U`, p. 37 | `Universality.thm25` | 1 | **open** — same |
| 13 | Theorem 26, p. 39 | `Combinator.thm26` | 1, added binder | **binder proved necessary; row reclassified kind 3** |

Tally: **2 moved this round, 2 moved in r0047, 1 reclassified, 8 open.**

### 3.1 Row 1 — the recovery equation, at the paper's hypotheses

The paper's sentence (printed p. 9) quantifies over all domains `D` and `E`.
`Kleene.sSup_recoverAt` still carries `[BoundedComplete β]`, measured this round:

    @Kleene.sSup_recoverAt : ∀ {α β} [CompletePartialOrder α] [CompletePartialOrder β]
      [IsAlgebraic α] [IsAlgebraic β] [BoundedComplete β] {f : α → β},
      ScottContinuous f → ∀ (x : α), sSup (Kleene.recoverAt f x) = f x

r0044's agent1 proved the binder deletable with an out-of-package probe
(`scripts/a1-probe45.lean`) and r0046's agent5 re-ran it; **neither round landed
the result inside the build**, so the row was still `S≠`. It is landed now:

    @R49.Agent7.sSup_recoverAt_bcFree : ∀ {α β} [CompletePartialOrder α]
      [CompletePartialOrder β] [IsAlgebraic α] [IsAlgebraic β] {f : α → β},
      ScottContinuous f → ∀ (x : α), sSup (Kleene.recoverAt f x) = f x

    depends on axioms: [propext, Quot.sound]

Same footprint as the original — **no `Classical.choice`**. The mechanism is one
trade: `IsAlgebraic β` carries `directedOn_compactsBelow`, so an upper bound for
two members of the recovering set is **drawn from** `compactsBelow (f x₃)`
instead of **built** as a join; being compact, it lies in the recovering set
itself. `directedOn_recoverAt_bcFree` depends on **no axioms at all**.

`sSup_recoverAt_imp_old` and `eq_of_graphPairs_eq_imp_old` record the direction:
the binder-free statements imply the ones the development already had, so the bar
was not lowered. `eq_of_graphPairs_eq_bcFree` carries the determination statement
along.

### 3.2 Row 6 — the stabilizing index

Printed p. 31, re-extracted this round (`pdftotext -layout -f 32 -l 32`):

> Now, if `u ⊆ N ◁ A`, then `U(u) ⊆ N`. Hence, `Uⁿ(u) ⊆ N` for each `n`. If `N`
> is finite, then there must be an `n` for which `Uⁿ(u) = Uⁿ⁺¹(u)`. This is a
> third fact about Plotkin orders: for each finite `u ⊆ A`,
> `U^∞(u) = ⋃ₙ Uⁿ(u)` is finite.

r0044's agent2 classified this row kind 2 because `JungFinite.mubDiff_nonempty`
states a different proposition — its hypotheses are "every stage is finite" plus
"`U^∞(u)` is infinite", and its conclusion is that every successive difference is
nonempty. That reading is confirmed by re-measurement.

**A correction to that row, in the paper's favour.** Sentences 1 and 2 were
already stated and proved, at `ScottDomains.mubClosure_subset_of_isNormalIn`,
whose own docstring quotes them. Only the **third** sentence was unstated. That
is what this round adds:

    @R49.Agent7.exists_mubIter_eq_succ_of_isNormalIn :
      ∀ {α} [PartialOrder α] {A N u : Set α},
        IsNormalIn N A → N.Finite → u ⊆ N → ∃ n, mubIter A u n = mubIter A u (n + 1)

    depends on axioms: [propext, Classical.choice, Quot.sound]

with `mubIter_subset_of_isNormalIn` (sentence 2, in the per-stage form the third
sentence consumes) and `finite_mubClosure_of_isNormalIn` (the "third fact" the
paragraph is written to reach). The proof is the counting argument the sentence
elides: the stages increase and sit inside a finite `N`, so `n ≤ |Uⁿ(u)| ≤ |N|`
for every `n` if no stage repeats, which fails at `n = |N| + 1`.

Note what the paper's sentence needs and does not say: `N ◁ A` in this
development is only "`N ∩ ↓x` nonempty and directed for every `x ∈ A`", and the
step from that to `U(u) ⊆ N` is `minimalUpperBounds_subset_of_isNormalIn` — the
"(why?)" step plus minimality. The paper is right; the step is not free.

### 3.3 Rows 4 and 5 — re-measured, not re-derived

`ClosureProperties.lem17_fun` and `lem17_strictFun` **still carry
`[BoundedComplete β]` in the package**. r0047's agent4 did not edit them; it
added `R47.Agent4.lem17_fun` and `lem17_strictFun` without the binder, which is
the same discipline row 1 follows here. Measured:

    @ScottDomains.lem17_fun            : … [Domain α] [Domain β] [BoundedComplete β],
      IsBifinite α → IsBifinite β → IsBifinite (ScottHom α β)
    @R47.Agent4.lem17_fun              : … [Domain α] [Domain β],
      IsBifinite α → IsBifinite β → IsBifinite (ScottHom α β)

One qualification r0047's report does not make and a reader of the count needs:
the replacement is a **trade**, not a pure deletion — `[BoundedComplete β]` is
gone and the two `IsBifinite` hypotheses do the work. That is fine for these two
rows, because Lemma 17's printed statement is "if `D` and `E` are **bifinite**
domains", so `IsBifinite α` and `IsBifinite β` are the paper's own hypotheses and
were already present. The rows are genuinely at the paper's hypotheses.

### 3.4 Row 3 — a correction: the binder is not this row's defect

    @PRepFun.strictHomIsAlgebraic : ∀ {α β} [CompletePartialOrder α]
      [CompletePartialOrder β] [Domain α] [Domain β] [BoundedComplete β],
      IsAlgebraic (StrictHom α β)

The `[BoundedComplete β]` here is **not** an added binder: the paper's Theorem 7
assumes `D` and `E` are *bounded complete* domains, so on hypotheses the Lean
statement is already more general than the paper's (it omits
`[BoundedComplete α]`). The row is `S≠` entirely because of its **conclusion** —
the paper names a specific basis, the strict step functions, and `IsAlgebraic`
says only that *some* basis exists. r0044's agent1 states this; it is repeated
here because a binder-deletion round is exactly where it would be mistaken for a
target. The residue is unchanged: the package contains no strict step function,
and `Effective/FunctionSpace.lean:256–264` concedes it in its own docstring.

`R47.Agent4.domain_strictHom` proves `Domain (StrictHom α β)` without
`[BoundedComplete β]`, at the cost of `IsBifinite α`/`IsBifinite β`, so even the
binder question is already answered elsewhere and answered as a trade.

### 3.5 Rows 8–12 — the obstruction, named

`lem24` and `thm25` conclude about a `Cpo`, and the missing conjunct is "is a
domain" — `IsAlgebraic` plus a countable basis on the carrier. This is **not** a
transcription slip that a restatement fixes, and the reason is mathematical:
`D` is produced as the image of a closure on `U`, and the image of a closure
operator on an algebraic lattice is a **continuous** lattice, not in general an
algebraic one. r0044's agent2 records that the paper's own proof of Lemma 24
concludes "Hence there is a **cpo** `D ≅ D → E`" — the printed lemma is stronger
than the printed proof, and our statement is the proof.

Two things follow, and they should not be merged. Closing these rows requires
either an algebraicity argument specific to the recursive closure the
construction builds, or the recognition that the printed lemma over-claims — a
suspected eleventh printed defect that this round did **not** attempt and does
not assert. What is certain is that the five rows are one item, not five, and
that §2.5 above now depends on them: the Theorem 26 refutation cannot be composed
with this development's `thm25` until `Domain D` is available.

### 3.6 Rows 2 and 7 — residues, unchanged and re-confirmed

* **Row 2** (`JungSFP.lemma213`) needs the existential witness `∃ D E` satisfying
  its seven hypotheses. The paper's own route is the Figure 3c poset, still
  unbuilt. `lemma213`'s two call sites both apply it contrapositively at abstract
  `D`, `E`; neither instantiates at a concrete poset. No new finding.
* **Row 7** (p16) supplies one of four conjuncts and supplies it weakly.
  Re-measured: its conclusion is `ScottHom.IsProjection`, which `#print` gives as
  `(∀ x, p (p x) = p x) ∧ ∀ x, p x ≤ x`, whereas
  `ScottHom.IsFinitaryProjection p = ∃ (hp : p.IsProjection), Domain ↥(Set.range ⇑p)`.
  The three missing conjuncts are: `M = {p♮ | p ∈ Fp(D), im(p) finite}` is
  directed; `⊔M = id`; the members have finite image. The first of these needs
  the finiteness of `Plotkin.Powerdomain (im p)` for finite `im p`, which no
  declaration in the package concludes. Estimated at a full stream of work, not a
  residue of this one; not attempted, and reported as open rather than as an
  attempt that failed.

## 4. Declarations added

Eighteen — 4 `def`s and 14 theorems — all in `ScottDomains.R49.Agent7`, in two
new modules. No existing declaration was edited; no `def` of a claim was changed.

`ScottDomains/A7Thm26Arity.lean` (10): `IsSubalgebraOf`, `IsAlgEmbedding`,
`exists_map_eq`, `isSubalgebraOf_range`, `ArgwiseContinuous`, `Thm26Printed`,
`isAlgEmbedding_const_of_subsingleton`, `combEval_eq_of_zero_arity`,
`not_thm26Printed_of_two_zero_arities`, `not_thm26_statement_of_zero_arity`.

**For the row-11 census (`Prop`-valued `def`s nothing attempts):** three of the
four new `def`s — `IsSubalgebraOf`, `IsAlgEmbedding`, `ArgwiseContinuous` — are
**concepts**, in r0044 agent6's split, not claims: they name notions the
statements are written in, and no theorem is owed for them. The fourth,
`Thm26Printed`, **is** a claim, and it is attempted and **refuted** in the same
file. Row 11 gains nothing from this round.

`ScottDomains/A7SneqRows.lean` (8): `directedOn_recoverAt_bcFree`,
`sSup_recoverAt_bcFree`, `eq_of_graphPairs_eq_bcFree`, `sSup_recoverAt_imp_old`,
`eq_of_graphPairs_eq_imp_old`, `mubIter_subset_of_isNormalIn`,
`exists_mubIter_eq_succ_of_isNormalIn`, `finite_mubClosure_of_isNormalIn`.

Axiom footprints, every theorem, `#print axioms`:

| # | declaration | axioms |
| -- | ---------- | ------ |
| 1 | `directedOn_recoverAt_bcFree` | **none** |
| 2 | `exists_map_eq` | `[propext]` |
| 3 | `sSup_recoverAt_bcFree` | `[propext, Quot.sound]` |
| 4 | `eq_of_graphPairs_eq_bcFree` | `[propext, Quot.sound]` |
| 5 | `sSup_recoverAt_imp_old` | `[propext, Quot.sound]` |
| 6 | `eq_of_graphPairs_eq_imp_old` | `[propext, Quot.sound]` |
| 7 | `mubIter_subset_of_isNormalIn` | `[propext, Classical.choice, Quot.sound]` |
| 8 | `exists_mubIter_eq_succ_of_isNormalIn` | `[propext, Classical.choice, Quot.sound]` |
| 9 | `finite_mubClosure_of_isNormalIn` | `[propext, Classical.choice, Quot.sound]` |
| 10 | `isSubalgebraOf_range` | `[propext, Classical.choice, Quot.sound]` |
| 11 | `combEval_eq_of_zero_arity` | `[propext, Classical.choice, Quot.sound]` |
| 12 | `isAlgEmbedding_const_of_subsingleton` | `[propext, Classical.choice, Quot.sound]` |
| 13 | `not_thm26Printed_of_two_zero_arities` | `[propext, Classical.choice, Quot.sound]` |
| 14 | `not_thm26_statement_of_zero_arity` | `[propext, Classical.choice, Quot.sound]` |

No `sorryAx`. `sorry` 0 in 0 files, unchanged.

**Nothing here is a discharge-at.** The two `*_imp_old` theorems are the only
declarations carrying an added instance binder, and their whole purpose is to
record that the binder-free statements imply the ones already in the tree.

## 5. Build and measurement

`scripts/compile.sh -r r0049` over the whole package
(`ScottDomains/logs/compile-20260809-165700.agent7.log`):

| # | measurement | before | after |
| -- | ---------- | -----: | ----: |
| 1 | jobs | 1365 | **1367** |
| 2 | lake errors | 0 | **0** |
| 3 | lean diagnostics | 0 | **0** |
| 4 | other warnings | 0 | **0** |
| 5 | `sorry` declarations | 0 | **0** |
| 6 | modules | 118 (derived, 120 − 2) | **120** |
| 7 | lines | — | 44,124 |
| 8 | theorems | — | 2,042 |

Baseline log: `compile-20260809-164543.agent7.log`.

## 6. Reproducing

    scripts/a7-thm26-page.sh                       # printed pp. 38–39, verbatim
    scripts/a1-probe.sh scripts/a7-r49-rows.lean   # every row's elaborated type + axioms
    scripts/compile.sh -r r0049                    # the build

`scripts/a7-r49-rows.lean` lives outside `ScottDomains/ScottDomains/`, so
`lake build` never elaborates it and `scripts/counts.sh` never counts it. The
module list is explicit because for six of the thirteen rows the namespace path
is not the module path.

## 7. For the next round

1. **Rows 8–12 are one item, not five**, and the item is whether the closure
   image is algebraic. Whoever takes it should decide first whether the printed
   Lemma 24 over-claims (the printed proof concludes "cpo"), because that decides
   whether the work is a proof or an eleventh printed-defect entry.
2. **§2.5 is a live dependency**: the Theorem 26 refutation composes with this
   development's `thm25` only once `Domain D` is available, which is item 1.
3. **Row 7 (p16) is a stream, not a residue.** Its first missing conjunct needs
   finiteness of `Plotkin.Powerdomain (im p)` for finite `im p`, which nothing in
   the package concludes.
4. `Combinator.lean:60–72`'s argument should be replaced by a pointer to
   `not_thm26Printed_of_two_zero_arities`; the conclusion stands, the argument
   does not, and the file currently advertises the argument as the reason.
