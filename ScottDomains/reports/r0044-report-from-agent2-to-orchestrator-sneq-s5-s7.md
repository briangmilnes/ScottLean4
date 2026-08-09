---
round: r0044
from: agent2
to: orchestrator
subject: sneq-s5-s7
date: 2026-0808-17:32
started: 2026-0808-17:05
finished: 2026-0808-17:32
related:
  - plans/r0044-plan-from-orchestrator-to-orchestrator-specification-defects.md
  - analyses/property-coverage.2026-0808-11:59.orchestrator.md
  - analyses/property-coverage-remeasure.2026-0808-16:55.orchestrator.md
---

# r0044, Class 1, agent 2 — the `S≠` rows of §5, §6 and §7, split three ways

## 1. The answer

**My area holds 13 `S≠` rows, not the 9 the plan assigns. Of the 13, 10 are
defects in the formalization and 3 are correct work.**

| # | Kind | Count | Meaning |
| -- | ---- | ----: | ------- |
| 1 | under-specified | **9** | a strict weakening of the paper's claim |
| 2 | incorrectly specified | **1** | not a weakening; says something the paper does not say |
| 3 | deliberately divergent | **3** | the printed statement is false; ours is the repair — **not a defect** |
| — | total | **13** | |

Two of the three kind-3 rows are **kernel-checked** refutations of the printed
text (`Flat.plotkin_printed_clause_one_fails`,
`FpEmbedding.TwoMub.not_isEmbeddingProjectionPair`); the third
(`Colimit.stgEmb_ne_mk_eta`) is kernel-checked but refutes a *reading* of the
printed sentence rather than the sentence itself — see §5.3.

Eight of the nine kind-1 rows are the **added-binder** shape the orchestrator's
mid-round correction names: the paper's conclusion is stated, and a hypothesis
the paper does not impose is carried alongside it. Only one kind-1 row (p16) is
the missing-conjunct shape r0040 was looking for.

## 2. The population: 13, derived

The plan's 9-and-9 split is wrong; agent1's re-derivation of 5-and-13 is right,
and I reproduce it independently from the per-agent tables rather than from
agent1's message.

| # | Source | Area | `S≠` rows | Mine? |
| -- | ------ | ---- | --------: | ----- |
| 1 | r0040 agent1 §2, §3 | rows 45, 53, 59 | 3 | no |
| 2 | r0040 agent2 §4 → Lem 10 | Lemma 9 items 3 and 5 | 2 | no |
| 3 | r0040 agent3 Thm 11 → §5 | — (report line 17: "0 `S≠`") | 0 | — |
| 4 | r0040 agent4 §6 | Thm 16.2, Lem 17 `→`, Lem 17 `◦→`, p9b | 4 | **yes** |
| 5 | r0040 agent5 §7 | Lem 24a/b, Thm 25a/b/c, Thm 26, prose row 27 | 7 | **yes** |
| 6 | r0043 agent3 §5 | row 18, the `⊢♮` characterization | 1 | **yes** |
| 7 | r0043 agent4 §6 | p16, the Lemma 17 `♮` sketch | 1 | **yes** |
| — | total | | **18** | **13** |

r0043's agent5 stream added no `S≠` row (`grep "S≠"` over its report: zero hits),
and r0043's agent1 stream *removed* one in the improving direction (row 45,
`S≠ → S+P`), which its report left counted as `S≠` because the move was out of
scope. So the 18 in the plan is the right total and 5/13 is the right split.

## 3. The rows

Every "Lean, elaborated" cell below is `#check @d` against the built `.olean`,
printed by `scripts/a2-r0044-sneq-check.sh` — never read off a source line. Every
declaration also carries `#print axioms`; all 21 checked declarations depend on
`[propext, Classical.choice, Quot.sound]` except `eta_le_eta_iff`, which is
`[propext, Quot.sound]`. No `sorryAx` anywhere.

| # | Paper's sentence | printed p. | Declaration | Kind | What is wrong |
| -- | --------------- | ---------: | ----------- | :--: | ------------- |
| 1 | "If `u, v ∈ P*f(N⊥)`, then `u ⊢♮ v` iff 1. `⊥ ∈ v` and `u ⊇ v` or 2. `u = v`" | 26 | `Flat.plotkin_le_iff`, `Flat.plotkin_printed_clause_one_fails` | **3** | clause 1 is false as printed; ours drops `⊥` from the inclusion |
| 2 | Thm 16.2: "the inclusion map `i : Fp(D) ↪ (D → D)` is an embedding" | 32 | `Section62.thm16_positive`, `FpEmbedding.TwoMub.not_isEmbeddingProjectionPair` | **3** | false; refuted at the five-element `TwoMub` |
| 3 | Lem 17, `D → E` | 32 | `ScottDomains.lem17_fun` | **1** | added binder `[BoundedComplete β]` |
| 4 | Lem 17, `D ◦→ E` | 32 | `ClosureProperties.lem17_strictFun` | **1** | added binder `[BoundedComplete β]` |
| 5 | p9b: "If `N` is finite, then there must be an `n` for which `Uⁿ(u) = Uⁿ⁺¹(u)`" | 31 | `JungFinite.mubDiff_nonempty` | **2** | different hypotheses *and* a different conclusion |
| 6 | p16: "`M = {p♮ \| p ∈ Fp(D) and im(p) is finite}` is directed and has the identity as its least upper bound. The functions in `M` are themselves finitary projections with finite images" | 32 | `PowerdomainMap.isProjection_plotkin` | **1** | 3 of 4 conjuncts missing, and the 4th weakened |
| 7 | Lem 24a: "there are non-trivial **domains** `D` and `E` such that `E ≅ E × E`" | 37 | `Universality.lem24` | **1** | `E : Cpo`; "is a domain" missing |
| 8 | Lem 24b: "… and `D ≅ D → E`" | 37 | `Universality.lem24` | **1** | `D : Cpo`; "is a domain" missing |
| 9 | Thm 25a: "there is a non-trivial **domain** `D` such that `D ≅ D × D`" | 37 | `Universality.thm25` | **1** | `D : Cpo`; "is a domain" missing |
| 10 | Thm 25b: "`… ≅ D → D`" | 37 | `Universality.thm25` | **1** | same |
| 11 | Thm 25c: "and `D` is the image of a closure on `U`" | 37 | `Universality.thm25` | **1** | the clause is verbatim; its subject is a `Cpo` |
| 12 | Thm 26: "Given a signature `(s₁, …, s_n)`, there are combinations `F₁, …, F_n` …" | 39 | `Combinator.thm26`, `thm26_subalgebra`, `thm26_retract` | **1** | added binder `hs : ∀ i, 0 < s i`; the paper admits arity 0 |
| 13 | "each stage of the construction is embedded in the next one by the map `x ↦ (x, {x})`" | 42 | `BifiniteUniversal.eta_le_eta_iff`, `Colimit.stgEmb_ne_mk_eta` | **3** | the construction's connecting map is not `eta` |

### 3.1 The elaborated statements

Row 1.

    @Flat.plotkin_le_iff : ∀ {u v : Plotkin.FinCompacts Flat.NatBot},
      v ≤ u ↔ (⊥ ∈ v ∧ ∀ a ∈ v, a ≠ ⊥ → a ∈ u) ∨ u = v

    Flat.plotkin_printed_clause_one_fails :
      ∃ u, ∃ v ≤ u, ¬((⊥ ∈ v ∧ ∀ a ∈ v, a ∈ u) ∨ u = v)

Row 2.

    @Section62.thm16_positive : ∀ {α} [CompletePartialOrder α] [Domain α],
      Section62.HasGreatestStableNormal α →
        ∃ s, Monotone s ∧ (∀ (p : ↑(Fp α)), s ↑p = p) ∧ ∀ (g : ScottHom α α), ↑(s g) ≤ g

Rows 3 and 4.

    @lem17_fun : ∀ {α β} [CompletePartialOrder α] [CompletePartialOrder β]
      [Domain α] [Domain β] [BoundedComplete β],
      IsBifinite α → IsBifinite β → IsBifinite (ScottHom α β)

    @ClosureProperties.lem17_strictFun : … same binders … → IsBifinite (StrictHom α β)

Row 5.

    @JungFinite.mubDiff_nonempty : ∀ {α} [PartialOrder α] {A u : Set α},
      (∀ (n : ℕ), (mubIter A u n).Finite) → (mubClosure A u).Infinite →
        ∀ (n : ℕ), (JungFinite.mubDiff A u n).Nonempty

Row 6.

    @PowerdomainMap.isProjection_plotkin : ∀ {D} [CompletePartialOrder D] [IsAlgebraic D]
      {p : D → D} (hcont : ScottContinuous p),
      (∀ x, p (p x) = p x) → (∀ x, p x ≤ x) →
        { toFun := PowerdomainMap.plotkin p, scottContinuous' := ⋯ }.IsProjection

Rows 7 and 8.

    Universality.lem24 : ∀ (U) [CompletePartialOrder U] [Nontrivial U],
      IsRepresentable₂ U PowerdomainRep.prodCpo → IsRepresentable₂ U Cpo.funSpace →
        ∃ D E, Nontrivial D.carrier ∧ Nontrivial E.carrier ∧
          Recursive.IsClosureOf D (Universality.cpoOf U) ∧
          Recursive.IsClosureOf E (Universality.cpoOf U) ∧
          Universality.Iso E (PowerdomainRep.prodCpo E E) ∧ Universality.Iso D (D.funSpace E)

Rows 9, 10 and 11.

    Universality.thm25 : ∀ (U) [CompletePartialOrder U] [Nontrivial U],
      IsRepresentable₂ U PowerdomainRep.prodCpo → IsRepresentable₂ U Cpo.funSpace →
        ∃ D, Nontrivial D.carrier ∧ Recursive.IsClosureOf D (Universality.cpoOf U) ∧
          Universality.Iso D (PowerdomainRep.prodCpo D D) ∧ Universality.Iso D (D.funSpace D)

Row 12.

    @Combinator.thm26 : ∀ {D} [CompletePartialOrder D] (M : Combinator.LambdaModel D)
      {n : ℕ} (s : Fin n → ℕ), (∀ i, 0 < s i) →
        ∃ F, ∀ (o : Fin n → D), ∃ ψ, Function.Injective ⇑ψ ∧ (∀ a, M.fstH (ψ a) = a) ∧
          ∀ i (l : List D), l.length = s i →
            M.iterApp (M.combEval (F i)) (List.map (⇑ψ) l) = ψ (M.iterApp (o i) l)

Row 13.

    @BifiniteUniversal.eta_le_eta_iff : ∀ {A} [PartialOrder A] {x y : A},
      BifiniteUniversal.eta x ≤ BifiniteUniversal.eta y ↔ x ≤ y

    Colimit.stgEmb_ne_mk_eta :
      (Colimit.stgEmb 1) Colimit.pointB1 ≠ Colimit.mk (BifiniteUniversal.eta Colimit.pointB1)

## 4. The three kind-3 rows, each with its printed defect named

### 4.1 Row 1 — the `⊢♮` characterization (printed p. 26)

I re-read the printed page rather than take r0043's word for it.
`scripts/pdf-crop.sh "papers/Gunter Scott 1990.pdf" 27 600 700 4150 5000 500 …`
renders the two clauses at 600 dpi and they read, unambiguously,

> 1. `⊥ ∈ v` and `u ⊇ v` or
> 2. `u = v`

The direction matters and is the whole argument: with `⊆` in clause 1 the
development's witness would satisfy the printed disjunction and nothing would be
refuted. It is `⊇`.

The defect: clause 1 requires `⊥ ∈ u` implicitly, by demanding all of `v`
inside `u`. Taking `u = {1}`, `v = {1, ⊥}` in `P*f(N⊥)`, the Egli–Milner order
gives `u ⊢♮ v` (Lean: `v ≤ u`) while `u ⊉ v` and `u ≠ v`, so the printed
biconditional fails. `plotkin_le_iff` is the repair, `v ∖ {⊥} ⊆ u`, and
`plotkin_printed_clause_one_fails` is the refutation, both kernel-checked. This
is the ninth of the paper's known printed defects and is already recorded;
`docs/StatementRecovery.md` does not cover §5.2, and `PaperInventory.md:57`
records it. **Kind 3, confirmed independently. Not a defect of ours.**

### 4.2 Row 2 — Theorem 16's second conjunct (printed p. 32)

> **Theorem 16** If `D` is bifinite, then the poset `Fp(D)` of finitary
> projections on `D` is an algebraic lattice and the inclusion map
> `i : Fp(D) ↪ (D → D)` is an embedding.

"Embedding" is the paper's own §3.1 notion, an embedding–projection pair, so the
conjunct asserts a continuous `s : (D → D) → Fp(D)` with `s ∘ i = id` and
`i ∘ s ⊑ id`. `FpEmbedding.TwoMub.not_isEmbeddingProjectionPair` refutes it at
the five-element `TwoMub`, a finite — hence bifinite — poset that is not bounded
complete, and `thm16_positive` is the repair under
`HasGreatestStableNormal α`, whose printed form I checked:

    HasGreatestStableNormal α = ∀ (f : ScottHom α α), ∃ N, IsNormalIn N (compacts α) ∧
      N ⊆ FpEmbedding.stableCompacts f ∧
      ∀ N', IsNormalIn N' (compacts α) → N' ⊆ FpEmbedding.stableCompacts f → N' ⊆ N

**Kind 3.** One residue worth recording, which agent4's r0040 report states and
its table does not: the repair's `s` is only `Monotone`, not a `ScottHom`, so
even the repaired conjunct is stated one notch below the paper's word "embedding"
by this declaration. `thm16_positive_isEmbeddingProjectionPair` supplies the
continuous upgrade only over a bounded complete domain.

### 4.3 Row 13 — the §7.4 stage embedding (printed p. 42)

> It should be noted that each stage of the construction is embedded in the next
> one by the map `x ↦ (x, {x})`.

Read literally — "the map `x ↦ (x, {x})` embeds each stage in the next" — this
sentence is **true and proved**: `eta_le_eta_iff` gives `eta x ≤ eta y ↔ x ≤ y`
over any partial order, and `Colimit.mk` is the antisymmetrization, so `mk ∘ eta`
is an order embedding `Stg n ↪o Stg (n+1)`. On that reading the row is `S+P` and
does not belong to this population at all, which would make the count 12.

Read as the paper plainly intends it — the sentence identifies the connecting map
*of the construction* — it is false, and the development kernel-checks that:
`Colimit.stgEmb` is `M` applied to the previous connecting map
(`Colimit.lean:481–490`), and `stgEmb_ne_mk_eta` shows the two maps differ
already at stage 1, at `pointB1 = (⊥, ∅)`. `PaperInventory.md:139` records this
as the third printed defect in §7.4.

**Kind 3 under the intended reading, and not `S≠` at all under the literal one.
Either way it is not a defect of ours.** I record the ambiguity rather than
resolve it silently, because the choice moves the population between 12 and 13.

## 5. The kind-1 rows

### 5.1 Rows 3 and 4 — Lemma 17's `[BoundedComplete β]`

> **Lemma 17** If `D` and `E` are bifinite domains, then so are the cpo's
> `D → E`, `D ◦→ E`, `D × E`, `D ⊗ E`, `D + E`, `D ⊕ E`, `D⊥`, `D♮`, `D♯` and
> `D♭`. (printed p. 32)

`[Domain α]`/`[Domain β]` are not additions — this development's `IsBifinite` is
Theorem 14's clause 2 minus "is a domain", so the two together are the paper's
own phrase "bifinite domains". `[BoundedComplete β]` is an addition, it is the
hypothesis §6 exists to remove, and it makes both rows strict weakenings.
**Kind 1, added binder.**

Following the orchestrator's mid-round caution I tested whether the binder is
removable the way agent1's row 45 turned out to be. **It is not, by this proof.**
`lem17_fun` consumes it at `Skeleton/Lemma17.lean:408` through
`CompactFunction.exists_finite_isLUB_of_isCompactElement`, whose section variable
is `[BoundedComplete β]` (`CompactFunction.lean:135`) — that is the step-function
decomposition of a compact function, and it is where bounded completeness enters.
Removing the binder is a mathematical open item, exactly as the development's own
docstring says; it is not agent1's shape, where the binder was inert.

Two incidental measurements from the same reading, both bearing on the r0044
vacuity stream:

1. **An underscore-prefixed binder name is not evidence of an unused
   hypothesis.** `lem17_fun (_h₁ : IsBifinite α) (_h₂ : IsBifinite β)` looks
   vacuous in both hypotheses and is not: both are eliminated at lines 422–423 to
   produce the normal subposets `N₁` and `N₂`. Any instrument that ranks
   candidates by leading-underscore binders will report this theorem as vacuous
   and be wrong.
2. `ClosureProperties.lemma17`, the ten-fold conjunction, carries
   `[BoundedComplete β]` **and** forces `{α β : Type u_1}` into one universe,
   which the eight clean individual conjuncts do not.

### 5.2 Row 6 — the Lemma 17 `♮` sketch (printed p. 32)

> To see that `D♮` is bifinite, one shows that the set
> `M = {p♮ | p ∈ Fp(D) and im(p) is finite}` is directed and has the identity as
> its least upper bound. The functions in `M` are themselves finitary projections
> with finite images so `D♮` is bifinite.

Four conjuncts: `M` directed; `⊔M = id`; the members are **finitary**
projections; the members have **finite image**. `isProjection_plotkin` supplies
one of the four, and **more weakly than agent4's r0043 table records**. Its
conclusion is `ScottHom.IsProjection`, which `#print` gives as

    IsProjection p = (∀ x, p (p x) = p x) ∧ ∀ x, p x ≤ x

whereas `IsFinitaryProjection p = ∃ (hp : p.IsProjection), Domain ↥(Set.range ⇑p)`.
So the paper's word "finitary" is not delivered either, and the hypothesis is a
bare continuous projection rather than `p ∈ Fp(D)` with finite image. **Kind 1:
three conjuncts missing, and the surviving one weakened from "finitary
projection" to "projection".** agent4's r0043 table marks conjunct 1 "yes"; it
should read "partly".

### 5.3 Rows 7–11 — Lemma 24 and Theorem 25 conclude about a `Cpo`

> **Lemma 24** Let `U` be a non-trivial cpo. If the product and function space
> operators can be represented over `U`, then there are non-trivial **domains**
> `D` and `E` such that `E ≅ E × E` and `D ≅ D → E`. (printed p. 37)

> **Theorem 25** If `U` is a non-trivial **domain** which represents products and
> function spaces, then there is a non-trivial **domain** `D` such that
> `D ≅ D × D ≅ D → D` and `D` is the image of a closure on `U`. (printed p. 37)

Both Lean statements bind `D`, `E : Cpo` and never claim algebraicity or a
countable basis. **Kind 1 ×5: the missing conjunct is "is a domain".**

Two facts the r0040 report gets right and that the reader of a count needs:

* The deviation is **the paper's own**. Lemma 24's printed proof concludes
  "Hence there is a **cpo** `D ≅ D → E`" — the statement is stronger than the
  proof that follows it. Our statement is the paper's proof, not the paper's
  lemma.
* The two statements are **not pure weakenings**. `lem24` adds
  `Recursive.IsClosureOf D/E (cpoOf U)`, which the printed Lemma 24 does not
  state (its proof does), and `thm25`'s hypothesis is `[CompletePartialOrder U]`
  where the paper writes "domain `U`", which strengthens the theorem. Formally
  the pair is incomparable to the printed pair. I classify by the direction in
  which the Lean statement fails to deliver the paper's claim, which is kind 1;
  the strengthenings are recorded here so the classification is not read as a
  full account of the difference.

### 5.4 Row 12 — Theorem 26's positivity binder, and a correction to `PaperInventory.md` row 2c

> **Theorem 26** Given a signature `(s₁, s₂, …, s_n)`, there are combinations
> `F₁, F₂, …, F_n` defining operations on `D` of these arities such that whenever
> a continuous algebra of this signature is given on a domain `A` that is a
> retract of `D`, then `A` can be made isomorphic to a subalgebra of this fixed
> algebra structure on `D`. (printed p. 39)

The paper admits arity `0` explicitly, one page earlier: "our λ-calculus model
can be considered as a continuous algebra of signature `(2,0,0,0,0,0)` … here,
`0` indicates a 0-ary operation, which is just a constant" (printed p. 38). All
three Lean declarations carry `hs : ∀ i, 0 < s i`. **Kind 1, added binder: the
theorem is stated at the special case of positive arities.**

`Combinator.lean:60–72` and `PaperInventory.md` row 2c both call this a
correction to a **false** printed theorem — which would make the row kind 3. **I
do not think that is established, and I record the disagreement rather than
inherit it.** The docstring's argument is:

> Suppose `sᵢ = 0`. `Fᵢ` is one fixed element of `D` … an isomorphism of `A` onto
> a subalgebra must send `A`'s constant `oᵢ` to `Fᵢ`. Take two one-point algebras
> `A = {a}` and `B = {b}` with `a ≠ b`, both retracts of `D`. Both embeddings
> must hit that same `Fᵢ`, and **the paper's own `ψ` satisfies `fst(ψ(x)) = x`**
> (`thm26`'s first conjunct), so `a = fst(Fᵢ) = b` — a contradiction.

The contradiction is derived from `fst ∘ ψ = id`, which is a property of the
paper's *construction* and of `thm26`'s own conclusion, **not of the printed
statement**, which asks only that `A` "be made isomorphic to a subalgebra". Two
one-point algebras are isomorphic to the same one-point subalgebra `{Fᵢ}`, so the
printed sentence is not refuted by this witness. What the argument does establish
is the docstring's second sentence — "the paper's construction breaks down before
that: `Fᵢ` reads a slot *out of an argument*, and a 0-ary operation supplies no
argument to read it out of" — which refutes the *proof*, not the theorem.

Recommended edit to `PaperInventory.md` row 2c: replace "the theorem is **false**
for a signature admitting arity 0" with "the paper's *construction* does not
reach a signature admitting arity 0; whether the theorem itself fails there is
open, and the docstring argument turns on `fst ∘ ψ = id`, a property of the
construction". The row's status as a qualification on the 24 is unchanged.

### 5.5 Row 5 is the only kind 2

> Now, if `u ⊆ N ◁ A`, then `U(u) ⊆ N`. Hence, `Uⁿ(u) ⊆ N` for each `n`. **If `N`
> is finite, then there must be an `n` for which `Uⁿ(u) = Uⁿ⁺¹(u)`.** (printed
> p. 31)

`JungFinite.mubDiff_nonempty` is not a weakening of that sentence. Its hypotheses
are "every stage `Uⁿ(u)` is finite" — not the paper's "`Uⁿ(u) ⊆ N` with `N`
finite" — **plus** "`U^∞(u)` is infinite", which the paper's sentence does not
assume at all; and its conclusion, "every successive difference is nonempty",
is not the paper's existential stabilizing index and does not produce one. It is
a true theorem serving the same Fact 3 by a different route. **Kind 2: it asserts
something the paper does not say.**

A reading the orchestrator may prefer: since nothing states p9b and the nearest
declaration states a different proposition, the row is arguably `N`, not `S≠`.
The same reading would move row 6 to `N`. I leave both at `S≠` to keep r0040's
convention stable, and flag that the convention is doing real work in exactly two
of my thirteen rows.

## 6. Adjudication: agent3's rows 25–27 stay `S+P`

agent3 flagged three of its own `S+P` rows (`{|1,⊥|} = ⊥ = {|⊥|}` in `♯`;
`{|1,⊥|} = {|1|} ≠ ⊥` in `♭`; the three elements distinct in `♮`; all §5.3,
printed p. 27) as arguably `S≠`, because they are stated at
`IdealCompletion.principal` / `Plotkin.principal` of a finite set rather than at
the paper's `{|·|}` and `⋓`. Elaborated:

    Flat.smyth_oneBot_eq_bot_eq_unit_bot :
      IdealCompletion.principal Flat.bOneBot = ⊥ ∧ IdealCompletion.principal ⊥ = ⊥
    Flat.hoare_oneBot_eq_one :
      IdealCompletion.principal Flat.pfOneBot = IdealCompletion.principal Flat.pfOne
    Flat.hoare_oneBot_ne_bot : IdealCompletion.principal Flat.pfOneBot ≠ ⊥
    Flat.plotkin_three_distinct :
      Plotkin.principal Flat.fcOneBot ≠ Plotkin.principal Flat.fcOne ∧
      Plotkin.principal Flat.fcOneBot ≠ Plotkin.principal Flat.fcBot ∧
      Plotkin.principal Flat.fcOne ≠ Plotkin.principal Flat.fcBot

**Ruling: `S+P`. They are not `S≠` under any of the three kinds.** The two
presentations denote the same element, and `{|·|}`-versus-`principal` is a
notational identification, not a change of proposition: nothing is weakened
(kind 1) and nothing is asserted that the paper does not assert (kind 2).
The gap agent3 found is real but is a **composition gap** — `unit_coe_compact`,
`principal_op_principal` and the `FinSets` instances are each kernel-checked and
their two-line composition is not written — which is the same category as "no
declaration composes Theorem 18's two propositions", already tracked as a
composition gap rather than a specification defect. Recommendation: write the two
lines and the question disappears; do not move the label.

## 7. Corrections to other streams and to the documents

| # | Claim | Where | Correction |
| -- | ----- | ----- | ---------- |
| 1 | "the 9 `S≠` rows in §5, §6, §7" | r0044 plan, Class 1 | **13**, derived in §2. §5 contributes 1, §6 contributes 5, §7 contributes 7 |
| 2 | `ClosureProperties.lem17_fun` | r0040 agent4 report row 4; `Skeleton/Lemma17.lean` is in `namespace ScottDomains` only | the declaration is **`ScottDomains.lem17_fun`**; `ClosureProperties.lem17_fun` does not elaborate |
| 3 | `Skeleton.Recovered.thm14`, `Skeleton.Recovered.IsBifiniteViaProjections` | r0040 agent4 §4, r0043 agent4 §5, `docs/StatementRecovery.md` | the module is `ScottDomains.Skeleton.Recovered`; the **namespace is `ScottDomains.Recovered`**. `ScottDomains.Skeleton.Recovered.IsBifiniteViaProjections` does not elaborate |
| 4 | p16 conjunct 1 "the members are projections — **yes**" | r0043 agent4 §5 table | partly: `IsProjection`, not `IsFinitaryProjection`, and at a bare continuous projection rather than at `p ∈ Fp(D)` with finite image |
| 5 | "Theorem 26 is **false** for a signature admitting arity 0" | `Combinator.lean:60–72`, `PaperInventory.md` row 2c | not established at the paper's own wording; see §5.4 |

Item 3 is the same class of defect r0043's citation check was built to catch and
did not: `scripts/r0043-verify-citations.sh` tests backticked tokens against a
list of names, and a name whose *namespace prefix* is wrong while its final
component exists resolves in that test and fails in Lean. agent7's generalized
sweep should compare fully-qualified names, not final components.

## 8. Measurement discipline

**No `.lean` file was edited.** The only files this round writes are this report
and `scripts/a2-r0044-sneq-check.sh`; page renderings went to the scratchpad.

| # | Measurement | Value | Required |
| -- | ----------- | ----- | -------- |
| 1 | modules | 100 | 100 |
| 2 | lines | 37,300 | 37,300 |
| 3 | theorems | 1,773 | 1,773 |
| 4 | `sorry` | 0 in 0 files | 0 |
| 5 | jobs | 1,339 | 1,339 |
| 6 | lake errors | 0 | 0 |
| 7 | diagnostics / other warnings | 0 / 0 | 0 |
| 8 | wall clock | 0.91 s (replay) | — |

`scripts/counts.sh`; `scripts/compile.sh -r r0044`, log
`ScottDomains/logs/compile-20260808-172046.agent2.log`.

## 9. Reproducing this

    scripts/a2-r0044-sneq-check.sh

One command, no arguments. It imports the thirteen modules the rows live in,
`#check @d` and `#print axioms d` for the 21 declarations cited above, and
`#print`s the five definitions the classifications turn on
(`HasGreatestStableNormal`, `IsProjection`, `IsFinitaryProjection`,
`IsBifiniteViaProjections`, `stgEmb`). The module list is hard-coded because for
six of the thirteen rows the namespace path is not the module path — which is how
corrections 2 and 3 of §7 were found.

The printed-page evidence for row 1:

    scripts/pdf-render.sh "ScottDomains/papers/Gunter Scott 1990.pdf" 27 <out> 600
    scripts/pdf-crop.sh   "ScottDomains/papers/Gunter Scott 1990.pdf" 27 600 700 4150 5000 500 <out>

PDF page `n` is printed page `n − 1` throughout this paper.
