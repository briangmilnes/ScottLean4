---
round: r0031
from: agent4
to: orchestrator
subject: lemmas-28-30
date: 2026-0806-20:20
started: 2026-0806-20:05
finished: 2026-0806-20:25
related: plans/r0031-plan-from-orchestrator-to-agent4-lemmas-28-30.md
---

# r0031 agent4 — the product operator over `P N`, and what Lemmas 28 and 30 actually say

## Filename deviation, stated up front

The plan asks for `reports/r0030-report-from-agent4-to-orchestrator-powerdomain-universal.md`.
That name carries round `r0030` and the subject of a superseded plan. GRASE rule 7.6
requires a report to share its plan's `rNNNN`, and this plan is `r0031` with subject
`lemmas-28-30`, so the report is written under the matching name. Nothing else in the
plan is deviated from.

## Result 1 — the critical path, landed

**`ScottDomains.PowerdomainRep.isRepresentable_prod : IsRepresentable₂ (Set ℕ) prodCpo`**
is proved and kernel-accepted. This is the hypothesis Lemma 24 lacked; with
`ScottDomains.lem23` (the function-space operator) both of Lemma 24's hypotheses are now
available, so Lemma 24 → Theorem 25 → Theorems 26 and 27 are unblocked.

The proof is the paper's own, quoted in the module docstring from §7.1:

> A similar construction can be carried out for the product operator. Suppose
> `×⁻ : P N → (P N × P N)`, `×⁺ : (P N × P N) → P N` such that `×⁻ ∘ ×⁺ = id` and
> `×⁺ ∘ ×⁻ ⊒ id`. For `r, s ∈ Fc(P N)` define `R×(r, s) = ×⁺ ∘ (r × s) ∘ ×⁻`. We
> leave for the reader the demonstration that this makes sense and `R×` represents
> the product operator.

`(×⁻, ×⁺)` is Theorem 22 (`ScottDomains.thm22`) applied at `L = P N × P N`. Discharging
its three hypotheses there is the only work the paper does not do:

| # | Obligation | Declaration | Argument |
| -- | ---------- | ----------- | -------- |
| 1 | `K(D × E) = K(D) × K(E)`, as a set | `compacts_prod` | `Set.ext` over `isCompactElement_prod_iff` (`Skeleton/Lemma17.lean`) |
| 2 | `D × E` algebraic | `isAlgebraic_prod` | `compactsBelow` splits as a rectangle; directedness coordinatewise, the least upper bound by `isLUB_prod` after `Set.fst_image_prod` / `Set.snd_image_prod`, whose nonemptiness side conditions are `⊥ ∈ compactsBelow` |
| 3 | `D × E` a domain | `domain_prod` | `Set.Countable.prod` against row 1 |
| 4 | `P N × P N` a complete lattice | `isLUB_sSup_prod_set` | `Prod.supSet` is coordinatewise and `P X` is a complete lattice |

An end-to-end check that the result plugs into the existing §7 pipeline:
**`recursiveDomain_prod : Recursive.IsSolvable.{0} fun X => prodCpo X X`** — a domain
`D ≅ D × D`, by `Recursive.IsRepresentable₂.diag` and Theorem 21, exactly parallel to
`recursiveDomain_funSpace`, and the first step of Lemma 24's own proof.

### A generic representation scheme, not a second copy

`R→` (Lemma 23) and `R×` are one construction with two parameters changed. The file
states it once — `repOf`, `isClosure_repOf`, `repRangeOrderIso`, `scottContinuous_repOf` —
for an arbitrary cpo `V` and an arbitrary continuous family `C : Fc(U) × Fc(U) → (V → V)`
of closures. `UniversalDomain.lean` was **not** edited; `lem23` keeps its specialized
copies. Any further conjunct (`⊗`, `()⊥`, the constant operators) now costs only its own
`C`, its closure and monotonicity laws, one `isLUB` lemma, and one range isomorphism.

### The `Fc(U)` appeal is discharged

The plan asked whether `IsClosure.domain_range` closes r0028 agent5's recorded gap —
that identifying `ClosurePoset U` with the paper's `Fc(U)` appealed to Lemma 19 at a
strength the development lacked.

**It fully discharges it, and nothing in this file needs it.** The paper's own sentence
is "In the event that `D` is a domain, the requirement that `im(r)` be a domain is
unnecessary because we have the following: Lemma 19", and
`FinitaryProjectionPoset.lean`'s `mem_Fc_iff : r ∈ Fc α ↔ IsClosure r` is that sentence
formalized, with `IsClosure.domain_range` supplying its right-to-left half. So over
`P N` — a domain by `Powerset.lean` — `ClosurePoset (Set ℕ)` and `Fc (Set ℕ)` have the
same members. `IsRepresentable₂` is stated over `ClosurePoset`, so this file's proofs
never invoke the identification; the identification is what makes the *statement*
faithful, and it now holds.

### Axioms

`#print axioms` was run over all 20 declarations and the output transcribed into a
comment at the foot of the file (then removed, so the build emits no `info` lines).
Every declaration depends on `[propext, Classical.choice, Quot.sound]` and nothing else;
**none depends on `sorryAx`**. `compacts_prod`, `compactsBelow_prod` and `prodCpo` are
choice-free. Elsewhere `Classical.choice` enters by the same door it enters `lem23` by —
`ScottHom`'s `SupSet` instance is a `dite` on an undecidable continuity predicate — plus,
in `isRepresentable_prod`, `Set.Countable.exists_eq_range` inside `thm22`, which chooses
the enumeration of the basis of `P N × P N`.

## Result 2 — Lemma 28 and Lemma 30 are not what the plan describes

This is the substantive negative finding, and it changes what those two rows need.

The plan states them as: Lemma 30 is "the universal / closure property of the
powerdomains (§5.3)", and Lemma 28 is "the operators `→, ×, ⊗, +, ()⊥, ()], ()[` are
representable over the universal domain `U`" with Lemma 23 supplying its function-space
conjunct. `pdftotext -layout` over `papers/Gunter Scott 1990.pdf` recovers both
statements legibly, and neither reading survives. Verbatim, from §7.3 and §7.4:

> **Lemma 28** The following operators are representable over `U`: `→`, `⇸`, `×`, `⊗`,
> `+`, `⊕`, `()⊥`, `()♯`, `()♭`.

> **Lemma 30** The following operators are p-representable over `V`: `→`, `⇸`, `×`, `⊗`,
> `+`, `⊕`, `()⊥`, `()♯`, `()♭`, `()♮`.

Three differences, each of which changes the work:

1. **Neither lemma is about `P N`.** Lemma 28's `U` is §7.3's domain of ideals over the
   finite non-empty unions of half-open intervals `[r, t)` of dyadic rationals in
   `[0, 1)`, ordered by superset. Lemma 30's `V` is §7.4's bifinite universal domain, the
   fixed point of `D ↦ D⁺` over `⟨M(A), ⊢⟩` supplied by Theorem 29 — whose full proof the
   paper itself defers to [Gun87]. The development constructs neither domain.
2. **Both are about p-representability.** §7.3 defines the notion afresh: "let us say
   that an operator `F` on cpo's is **p-representable** over a cpo `U` if and only if
   there is a continuous function `R_F` which completes the following diagram (up to
   isomorphism)", with **`Fp(U)`** — finitary *projections* — on the bottom row, not
   `Fc(U)`. `IsRepresentable` and `IsRepresentable₂` (`UniversalDomain.lean`) are the
   `Fc(U)` notion, so as written they state Lemma 28 for no value of `U`.
3. **Lemma 23 is therefore not Lemma 28's function-space conjunct.** The paper claims
   only a resemblance: "The proof that `→` is representable over `U` is almost identical
   to the proof we gave above that it is representable over `P N`."

The inventory rows in `docs/PaperInventory.md` are already correct on all three points
("representable over `U`", "p-representable over universal bifinite `V`"); it is the
r0031 plan's prose that contradicts them. One inventory row is wrong and should be fixed:
`§5.3 | Universal & closure properties (see Lem 13, 28, 30)` — §5.3 contains Lemma 13 but
neither Lemma 28 nor Lemma 30; its universal property is **Theorem 12** (next section).

Consequently **Lemma 28 and Lemma 30 are left unstated**, per the plan's own instruction
that a recorded blocker is a result and a guessed statement is a defect. The blockers,
precisely:

| # | Missing prerequisite | For |
| -- | -------------------- | --- |
| 1 | `IsPRepresentable` / `IsPRepresentable₂` over `Fp(U)` — the §7.3 notion. `Fp` exists (`FinitaryProjectionPoset.lean`); the representability predicate over it does not | Lem 28, Lem 30 |
| 2 | §7.3's domain `U`: ideals over the finite non-empty unions of dyadic half-open intervals under `⊇`, plus **Theorem 27** (a projection `U → D` for every bounded complete domain `D`) | Lem 28 |
| 3 | §7.4's domain `V`: `M(A)`, the operator `()⁺`, **Theorem 29**, and a fixed point `V ≅ V⁺` | Lem 30 |

## Result 3 — Theorem 12 is recoverable, and is the §5.3 universal property

The plan's item 1 describes, under the name "Lemma 30", "the sense in which the
powerdomain is free, i.e. that a continuous map from `D` into a suitable structure
extends uniquely to the powerdomain". That statement is real, is in §5.3, and is
**Theorem 12**. `docs/PaperInventory.md` currently marks it `✗ not statable — "axioms T"
is never defined in the legible text`. That is no longer accurate: `pdftotext -layout`
recovers the definition. Verbatim:

> **Definition:** A continuous algebra (of signature `(2)`) is a cpo `E` together with a
> continuous binary function `⊕ : E × E → E`. We refer to the following collection of
> axioms on `⊕` as theory `T♮`:
> 1. associativity: `(r ⊕ s) ⊕ t = r ⊕ (s ⊕ t)`
> 2. commutativity: `r ⊕ s = s ⊕ r`
> 3. idempotence: `s ⊕ s = s`.
>
> (These are the well-known semi-lattice axioms.) A homomorphism between continuous
> algebras `D` and `E` is a continuous function `f : D → E` such that
> `f(s ⊕ t) = f(s) ⊕ f(t)` for all `s, t ∈ D`.

> **Theorem 12** Let `D` be a domain. Suppose `⟨E, ⊕⟩` is a continuous algebra which
> satisfies `T♮`. For any continuous `f : D → E`, there is a unique homomorphism
> `ext(f) : D♮ → E` which completes the following diagram [`f = ext(f) ∘ {|·|}`].
>
> *Proof:* (Hint) If `u = {x₁, …, xₙ} ∈ s ∈ D♮`, and `û` is the principal ideal generated
> by `u`, then define `ext(f)(û) = f(x₁) ⊕ … ⊕ f(xₙ)`. This function has a unique
> continuous extension to all of `D♮` given by `ext(f)(s) = ⨆{ext(f)(û) | u ∈ s}`.

and the two variants, also verbatim: "consider the following axiom: `4♯. s ⊕ t ⊑ s`. Let
`T♯` be the set of axioms obtained by adding axiom `4♯` to the axioms in `T♮`. Similarly,
let `T♭` be obtained by adding the axiom `4♭. s ⊑ s ⊕ t` … Theorem 12 still holds when
`D♮` and `T♮` are replaced by `D♯` and `T♯` respectively, or by `D♭` and `T♭`
respectively."

Theorem 12 was **not** attempted here, for two reasons, and the orchestrator should
decide where it goes:

* It is assigned elsewhere — the inventory records statement recovery for Theorem 12 as
  r0030 agent5's item.
* It is a full round of work, not a tail-end addition. It needs `⊕` on `D♮` (§5.3's
  `s ⊕ t = {w | u ∪ v ⊢♮ w for some u ∈ s, v ∈ t}`) proved an ideal and continuous,
  `{|x|} : D → D♮` likewise, `ext(f)` on principal ideals as a `Finset` fold whose
  well-definedness is exactly the three `T♮` axioms, monotonicity of `ext(f)` with
  respect to `⊢♮`, the directed supremum, and uniqueness. Writing a statement with a
  `sorry` body would have raised the development's `sorry` count, which the plan forbids.

## Result 4 — `+` is not representable over `P N`, by the paper's own assertion

Of the plan's list `×, ⊗, +, ()⊥`, the `+` conjunct is false over `P N`. §7.1:
"Unfortunately, there is no representation for the operator `F(X) = X + X` over `P N`",
and §7.3 opens by naming that failure as the reason the paper builds a second universal
domain at all: "one slightly bothersome drawback to `P N` … is the fact that it cannot
represent the sum operator `+`". `⊗` and `()⊥` over `P N` are asserted by the paper
nowhere; they are reachable with the generic scheme above (both `(P N)⊥` and the smash
product are countably based algebraic lattices, so Theorem 22 supplies the conjugating
pair), but stating them would be adding results the paper does not, so they were not
written. If the orchestrator wants them, each is roughly the size of the `ProdMap`
section of this file.

## Measurements

| # | Quantity | Value |
| -- | -------- | ----- |
| 1 | New files | 1 — `ScottDomains/Powerdomain/Universal.lean`, 447 lines |
| 2 | Files edited outside it | 0 |
| 3 | New declarations | 20, all in `namespace ScottDomains.PowerdomainRep` |
| 4 | Paper results proved | 1 — §7.1's product-representability remark |
| 5 | Paper results left unstated with a recorded blocker | 2 — Lemma 28, Lemma 30 |
| 6 | Declarations depending on `sorryAx` | 0 of 20 |
| 7 | `sorry` count, whole library | 1 — `Skeleton/Section6.lean:196`, pre-existing, untouched |
| 8 | Build | 976 jobs, 0 errors, 0 warnings (the one `sorry` warning is row 7) |

Verbatim final `lake build` line, from
`ScottDomains/logs/compile-20260806-201913.agent4.log`:

    compile: exit 0 · wall 0:01.63 · mem 1669 MiB single / 1796 MiB tree pss / 2456 MiB tree rss · jobs 976 · diagnostics 0 · lake errors 0 · sorry 1 · other warnings 0

(The wall time is a warm incremental rebuild; only `Powerdomain/Universal.lean` was
elaborated, at 841 ms.)

## Commits on branch `agent4`

| # | SHA | Contents |
| -- | --- | -------- |
| 1 | `94accbc` | `isRepresentable_prod` and the generic scheme, 19 declarations, plus build logs |
| 2 | `38989e3` | `recursiveDomain_prod`, the axiom-audit comment, and this report |

Not pushed and no upstream set, per plan rule 5.

## What the orchestrator should decide

1. Fix the `docs/PaperInventory.md` §5.3 row: its universal property is Theorem 12, not
   Lemmas 28/30.
2. Move Theorem 12 from `✗ not statable` to `✗ prove`, with the recovered text above.
3. Add `IsPRepresentable` over `Fp(U)` as a prerequisite row for Lemmas 28 and 30, and
   §7.3's `U` and §7.4's `V` as prerequisite constructions.
4. Decide whether `⊗` and `()⊥` over `P N` are wanted as extensions the paper does not
   state.
