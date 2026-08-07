---
round: r0034
from: agent4
to: orchestrator
subject: theorem-26-lemma-28
date: 2026-0807-07:30
started: 2026-0806-22:50
finished: 2026-0807-07:30
related:
  - plans/r0034-plan-from-orchestrator-to-agent4-theorem-26-lemma-28.md
---

# r0034 agent4 — Theorem 26 and Lemma 28

## Result in one line

**Theorem 26 is proved** (kernel-checked, no `sorry`, three standard axioms), in
its true §7.2 statement — which is *not* the statement the plan describes. Of
Lemma 28's operators, **three of seven are proved representable over the abstract
carrier** (`→`, `×`, `()⊥`); **two of the remaining four are refuted** for the
closure reading by an explicit counterexample, and **two are blocked** because the
operator is not a function `Cpo → Cpo` in this development. Every gap is named,
with the exact remaining work.

## Measured counts

| # | Metric | Value |
| - | ------ | ----- |
| 1 | New modules | 2 — `ScottDomains/Combinator.lean`, `ScottDomains/CombinatorRep.lean` |
| 2 | New lines | 1201 (631 + 570) |
| 3 | New `theorem`/`lemma` declarations | 71 (42 + 29) |
| 4 | New `def`/`structure`/`inductive` declarations | 38 (29 + 9) |
| 5 | Build | `scripts/compile.sh -r r0034`: **0 errors, 0 warnings**, 1074 jobs, wall 3.31 s |
| 6 | `sorry` in the two new modules | **0** |
| 7 | `sorry` repository-wide | 8, all pre-existing (`Skeleton/Recovered.lean` ×7, `Skeleton/Section6.lean` ×1) |
| 8 | Repository totals after the round | 47 modules, 15 249 lines, 730 theorem-ish declarations |
| 9 | Axiom audit | `thm26`, `thm26_subalgebra`, `thm26_retract`, `exists_lambdaModel_of_thm25`, `rep_arrow`, `rep_prod`, `rep_lift`, `isRepresentable_of_retracts`, `isRepresentable₂_of_retracts` — each `[propext, Classical.choice, Quot.sound]`; **none depends on `sorryAx`** |

Commits on branch `agent4` (not pushed, per the standing rule):
`aa189da`, `d6b4642`, `39f9222`, plus the report commit.

## Part 1 — Theorem 26

### The plan's reading of Theorem 26 does not match the paper

The plan says: "for any signature `(s₁,…,s_n)`, combinators `F₁,…,F_n` solving the
equations", to be stated in `Recursive.Solves` / `IsSolvable` vocabulary. The PDF
(page 39, §7.2) says:

> **Theorem 26** Given a signature `(s₁, s₂, …, s_n)`, there are combinations
> `F₁, F₂, …, F_n` defining operations on `D` of these arities such that whenever
> a continuous algebra of this signature is given on a domain `A` that is a
> retract of `D`, then `A` can be made isomorphic to a subalgebra of this fixed
> algebra structure on `D`.

Theorem 26 is an **Engeler-style universal-algebra** result about the λ-calculus
model of §7.2, not a recursive-domain-equation result. Nothing is "solved"; the
`Fᵢ` are *combinations* — variable-free applicative expressions — not solutions of
`X ≅ F(X)`. `Recursive.Solves` and `IsSolvable` are the wrong vocabulary and are
not used. This is the same class of error the r0031 agent recorded for Lemma 28,
and it argues for reading §7 statements out of the PDF before assigning them.

### What was proved

`ScottDomains.Combinator.thm26`, in `ScottDomains/Combinator.lean`:

```
theorem thm26 (M : LambdaModel D) {n : ℕ} (s : Fin n → ℕ) (hs : ∀ i, 0 < s i) :
    ∃ F : Fin n → Comb, ∀ o : Fin n → D, ∃ ψ : ScottHom D D,
      Function.Injective ⇑ψ ∧ (∀ a, M.fstH (ψ a) = a) ∧
      ∀ (i : Fin n) (l : List D), l.length = s i →
        M.iterApp (M.combEval (F i)) (l.map ⇑ψ) = ψ (M.iterApp (o i) l)
```

The quantifier order is the paper's: `F` depends on the signature alone and is
chosen **before** the algebra; `ψ` depends on the algebra. The last conjunct is the
paper's displayed calculation `Fᵢ(ψ(a₁))⋯(ψ(a_{sᵢ})) = ψ(oᵢ(a₁,…,a_{sᵢ}))`.

Supporting statements:

| # | Declaration | Content |
| - | ----------- | ------- |
| 1 | `LambdaModel` | the applicative structure: `app`/`lam` with the β-law, `pairH`/`fstH`/`sndH` with the two projection laws |
| 2 | `LambdaModel.ofOrderIso` | that structure derived from `D ≃o (D → D)` and `D ≃o D × D` alone |
| 3 | `exists_lambdaModel_of_thm25` | **Theorem 25** supplies the hypothesis — a nontrivial `D`, image of a closure on `P N`, carrying the structure |
| 4 | `Comb`, `combEval`, `bComb`, `fstSndPowComb` | the paper's *combinations*: `Fᵢ` is an explicit variable-free term over `S`, `K`, `fst`, `snd`, with `B = S(KS)K` doing the "rewritten in terms of `S`, `K`, `fst`, and `snd`" |
| 5 | `Construction.psi` | `ψ` as `kleeneFix` of the paper's displayed fixed-point equation, in the cpo `D → D` |
| 6 | `thm26_subalgebra` | the "isomorphic to a subalgebra" reading: `ψ` injective on `A`, `ψ '' A` closed under the `Fᵢ` |
| 7 | `thm26_retract` | the paper's own hypothesis: `A` a retract of `D` via `(e, p)` with `p ∘ e = id`; `φ = ψ ∘ e` is injective and carries the induced operation to `Fᵢ` |

### Design decision — how the signature is indexed

**`Fin n → ℕ`**, recorded in the module docstring. The paper writes `(s₁,…,s_n)`, a
finite *sequence*, and the proof uses the ordering: `Fᵢ` reads the `i`-th slot of a
right-nested tuple by applying `snd` exactly `i` times, so the index must carry a
**position**, not merely an identity. A general finite type `ι` with `[Fintype ι]`
carries an identity but not a position, so every use would have to choose an
enumeration of `ι` — reintroducing `Fin n` under an extra layer. `Fin n → ℕ` is
therefore the form the rest of §7 should reuse.

### Correction to the paper — Theorem 26 is false for arity 0

The paper admits `0` in a signature explicitly ("`0` indicates a 0-ary operation,
which is just a constant", of the signature `(2,0,0,0,0,0)`). **The theorem is
false for any signature containing `0`.** The argument, stated in the module
docstring and *not* Lean-checked:

`Fᵢ` is one fixed element of `D`. A subalgebra of `⟨D, F₁,…,F_n⟩` contains `Fᵢ` and
has `Fᵢ` as its own `i`-th constant, so an isomorphism of `A` onto a subalgebra
must send `A`'s constant `oᵢ` to `Fᵢ`. Take two one-point algebras `A = {a}` and
`B = {b}` with `a ≠ b`, both retracts of `D`. Both embeddings must hit the same
`Fᵢ`, and `thm26`'s first conjunct gives `fst(ψ(x)) = x`, so `a = fst(Fᵢ) = b` — a
contradiction. The paper's construction breaks down one step earlier: `Fᵢ` reads a
slot *out of an argument*, and a 0-ary operation supplies no argument.

`thm26` therefore carries `hs : ∀ i, 0 < s i`. This is a correction, not a
convenience, and should be recorded in `docs/PaperInventory.md` alongside the
Theorem 16 refutation.

### Two smaller decisions

* The paper terminates the right-nested tuple with the combination `K`. Nothing
  reads past the last slot, so `⊥` is used, which keeps `S` and `K` out of the data
  `ψ` depends on. They remain necessary for `Fᵢ`, which the paper requires to be a
  combination.
* An `m`-ary continuous operation on `D` is taken to be an **element** of `D`
  acting by iterated application. This costs no generality, because `D ≅ D → D`
  makes `D` reflexive; `elem_of_hom₁` and `elem_of_hom₂` record the bridge at the
  arities used, and the general induction is the same.

## Part 2 — Lemma 28 over an abstract carrier

### Three further corrections from the PDF

1. **Lemma 28 lists nine operators, not seven**: `→`, `⇸`, `×`, `⊗`, `+`, `⊕`,
   `()⊥`, `()♯`, `()♭`. The plan's seven drop `⇸` (strict function space) and `⊕`
   (coalesced sum).
2. **Its "representable" means *p-representable***. §7.3 redefines the word two
   paragraphs earlier, with `Fp(U)` — finitary **projections** — on the bottom row
   of the diagram, then says "since there will be no chance of confusion, let us
   just use the term 'representable' for 'p-representable' for the remainder of
   this section." `IsRepresentable` / `IsRepresentable₂` are the `Fc(U)` notion, so
   they do not state Lemma 28 at any `U`. (r0031 recorded this; it is corroborated.)
3. **Its `U` is not `P N`** — it is §7.3's domain of ideals over finite unions of
   half-open dyadic intervals, for which **Theorem 27** supplies a projection onto
   every bounded complete domain. Over `P N` the `+` conjunct is false, and §7.1
   says so.

Work here was done for the closure reading, because that is the notion the
development's `IsRepresentable` fixes; the two places where the readings diverge
are measured below rather than papered over.

### The exact interface the abstract carrier assumes

**This is what the orchestrator needs for the instantiation at merge.** There is
exactly one hypothesis, per operator, and it is a `Prop`:

```
def Retracts (U V : Type u) [CompletePartialOrder U] [CompletePartialOrder V] : Prop :=
  ∃ (fn : ScottHom U V) (gr : ScottHom V U), IsClosurePair fn gr
```

`IsClosurePair fn gr` unfolds to `(∀ y, fn (gr y) = y) ∧ (∀ x, x ≤ gr (fn x))` —
the paper's `F⁻ ∘ F⁺ = id` and `F⁺ ∘ F⁻ ⊒ id`. Nothing else about the carrier is
used anywhere: no algebraicity, no countable basis, no lattice completeness, no
`Domain U`, no `Nontrivial U`, no `[Inhabited]`, no universe constraint beyond
`U V : Type u` in one universe.

To instantiate at agent3's `U`, supply one `Retracts` witness per operator:

| # | Theorem to instantiate | Signature | Instance needed at `U` |
| - | ---------------------- | --------- | ---------------------- |
| 1 | `Combinator.rep_arrow` | `Retracts U (ScottHom U U) → IsRepresentable₂ U Cpo.funSpace` | `Retracts U (U → U)` |
| 2 | `Combinator.rep_prod` | `Retracts U (U × U) → IsRepresentable₂ U prodCpo` | `Retracts U (U × U)` |
| 3 | `Combinator.rep_lift` | `Retracts U (WithBot U) → IsRepresentable U liftOp` | `Retracts U U⊥` |

At `U = P N` all three witnesses come from **Theorem 22**
(`ScottDomains.thm22 L hsup`, needing `Domain L` and lattice completeness of `L`);
at §7.3's `U` they come from **Theorem 27**. `rep_arrow` at `P N` reproves
`ScottDomains.lem23` and `rep_prod` at `P N` reproves
`PowerdomainRep.isRepresentable_prod`, which is the check that the abstraction is
faithful — neither existing proof was edited.

Note for the merge: `Retracts U (WithBot U)` is *not* available at `U = P N` by
Theorem 22, because `P N⊥` is not a lattice (it has no binary meets at the adjoined
bottom). It is available at a carrier of Theorem 27's kind, where the requirement
is bounded completeness rather than lattice completeness.

### The generic scheme

`isRepresentable_of_retracts` (unary) and `isRepresentable₂_of_retracts` (binary)
take `Retracts U V`, a conjugating family `C` of closures on `V` with monotonicity
and a pointwise-continuity condition, and an isomorphism
`im(C p) ≅ F(im p₁, im p₂)`, and produce representability. Continuity of
`p ↦ R_F(C p)` is `scottContinuous_repFamily`, which generalizes
`PowerdomainRep.scottContinuous_repOf` from the index `Fc(U) × Fc(U)` to an
arbitrary preordered index so the unary and binary cases share one script.

### The four operators not proved, and exactly why

**`⊗` (smash) and `⊕` (coalesced sum) — the closure reading is refuted.** Let `U`
be the three-chain `⊥ ⊏ p ⊏ q` and `r = s` the closure `⊥ ↦ p`, `p ↦ p`, `q ↦ q`
(idempotent, and inflationary because every point lies below its image). Then
`im(r) = {p, q}` with bottom `p`, so `im(r) ⊗ im(s)` has the single non-bottom pair
`(q,q)` plus an adjoined bottom — **2 elements**. The paper's own functorial action
`r ⊗ s = smash ∘ (r × s) ∘ unsmash` sends the adjoined bottom to
`smash(r ⊥, s ⊥) = ⟨(p,p)⟩` and each `⟨(x,y)⟩` to `⟨(r x, s y)⟩`, so its image is all
four pairs drawn from `{p,q}` — **4 elements**. Two is not four. The same
computation refutes `⊕` (3 elements against 5). This is a hand computation recorded
in `CombinatorRep.lean`'s docstring; it is not Lean-checked.

The mechanism is general and explains the paper's own choice: `im(r)`'s bottom is
`r ⊥`, which a closure need not send to the ambient `⊥`, so a non-bottom point of
`U` is collapsed by the target and not by the source. **A projection has `p ⊥ = ⊥`,
so the obstruction disappears** — a second, independent reason why §7.3 states
Lemma 28 for `Fp(U)`, beyond the reason the paper gives.

**`+` (separated sum) — the scheme applies; the functorial action is missing.**
Not refuted. §4.4 defines `D + E` as `D⊥ ⊕ E⊥`, so its bottom is *adjoined*,
exactly as for `()⊥`, and the collapse does not occur. The carrier
`CoalescedSum (WithBot U) (WithBot U)` already has its cpo structure, so **no new
cpo construction is needed**. What is missing is `r + s` on that carrier plus its
Scott continuity against `CoalescedSum.sumSup`; `isLUB_leftParts_of_isLUB`,
`isLUB_rightParts_of_isLUB`, `isLUB_image_sumInl` and `isLUB_image_sumInr` are the
intended instruments. Estimated 150–200 lines. With it, `rep_sepSum` is
`isRepresentable₂_of_retracts` applied exactly as `rep_prod` is, under
`Retracts U (CoalescedSum (WithBot U) (WithBot U))`.

**`()♯` (Smyth) and `()♭` (Hoare) — the operator is not a function `Cpo → Cpo`.**
Blocked one level before the proof. Both are defined here as
`IdealCompletion (Pf ↥(compacts D))`, which requires `[Domain D]`.
`IsRepresentable` quantifies over `r : Fc(U)` and needs `F (im r)`, and `im r` for
a closure on a bare cpo carries only a `CompletePartialOrder` (`lem19`), not a
`Domain`. So `IsRepresentable U ()♯` does not typecheck. Two ways out: define the
two powerdomains for arbitrary cpos (Smyth: Scott-closed filters; Hoare: non-empty
Scott-closed subsets), or restrict `IsRepresentable` to closures whose image *is* a
domain — which is the paper's own `Fc(D)`, whose second conjunct `ClosurePoset`
deliberately drops. The second is smaller and is the route §7.3 takes, since
Theorem 27's projections land in bounded complete domains.

## Acceptance criteria, measured

| # | Criterion | Status |
| - | --------- | ------ |
| 1 | `thm26` proved | **met** — kernel-checked, no `sorry`, three standard axioms; plus `thm26_subalgebra` and `thm26_retract` |
| 2 | Seven representability proofs over the abstract carrier, each named for its operator | **3 of 7** — `rep_arrow`, `rep_prod`, `rep_lift`. Two of the remaining four (`⊗`, `⊕`) are **refuted** for the closure reading; two (`()♯`, `()♭`) are blocked at the operator's type; `+` is reachable and scoped above |
| 3 | Instantiation at `U` deferred to the merge, not stubbed with a `sorry` | **met** — the three `Retracts` hypotheses are named above; no `sorry` was added |
| 4 | Compile reports 0 errors and 0 warnings beyond `sorry` | **met** — 0 errors, 0 warnings; the 8 `sorry`s are pre-existing and in other agents' files |

## Recommendations

1. Record in `docs/PaperInventory.md`: **Theorem 26 is false for signatures
   containing arity 0**, alongside the Theorem 16 refutation.
2. Record that **Lemma 28 is a p-representability statement over `Fp(U)`, listing
   nine operators**, and that the closure reading of `⊗` and `⊕` is refuted by the
   three-chain counterexample. Any further §7.3 work should build `Fp(U)`'s
   representability notion rather than reuse `IsRepresentable`.
3. Assign `+` as a small follow-up (150–200 lines, no new cpo construction).
4. Before assigning the remaining §7 statements, read them out of the PDF: two of
   the three §7 statements assigned this round (Theorem 26 here, Lemma 28 in
   r0031) were described in plans by paraphrases that did not match the source.
