import ScottDomains.Effective.A2Compactness

/-!
# `StepFunctionsDecidable` over the consistency-guarded enumeration (r0049, agent3)

`Effective.StepFunctionsDecidable` transcribes Theorem 7's proof sentence,
printed p. 12, quoted exactly:

> The proof that the poset of step functions has decidable ordering and finite
> normal subposets is tedious, but not difficult, **using the effective
> presentations of `D` and `E`**.

Through r0048 it read `IsRecursive d → IsRecursive e → IsRecursive (scottHom d
e)`, naming one enumeration whose guard `IsCompactElement (ofPairs Q)` r0047
kernel-checked is **not** the boundedness test the sentence is about
(`R47.Agent2.not_forall_isCompactElement_ofPairs_imp_bddAbove`, witness at
`α = β = N⊥` under a presentation that is `IsRecursive`). This file records the
r0049 restatement.

## What is here

| # | Declaration | What it settles |
| -- | ---------- | --------------- |
| 1 | `StepFunctionsDecidableCompactGuard` | the pre-r0049 statement, verbatim and citable |
| 2 | `stepFunctionsDecidable_of_compactGuard` | **the direction of the change: old → new**, a weakening |
| 3 | `isStepEnumeration_scottHom`, `isStepEnumeration_scottHomC` | both enumerations witness the new existential; this is why the change is a weakening and not a change of subject |
| 4 | `ScottHomCRecursive`, `stepFunctionsDecidable_of_scottHomC` | the claim reduced to recursion theory over the `Consistent` guard |
| 5 | `consistentEnum_apply`, `consistentEnum_le_iff` | the order test on that enumeration as a finite condition on the two index sets — the residue handed to agent4 |
| 6 | `StrictHomCRecursive`, `strictStepFunctionsDecidable_of_strictHomC` | the same for `⊸` |
| 7 | `four_claims_of_residue` | what the residue closes: three claims from the arrow half, one from the strict half |

## The direction, and why it is this one

r0046's `R46.Agent1.stepFunctionsDecidable_of_unconditional` runs old → new and
r0047's `R47.Agent3.freeCarrier_of_preservesRecursivePresentation` runs new → old.
**This one runs old → new**, like r0046's: the new statement is a strict
weakening as a proposition, because `Effective.scottHom d e` — the old subject —
is one of the enumerations the new existential ranges over (item 3). Nothing the
paper asserts is given up: the printed sentence fixes no tie-break for an index
set whose step functions are unbounded, and that is the only index at which the
two enumerations differ (`R47.Agent2.consistentEnum_eq_scottHomEnum`).

The weakening is not idle. Under the old statement the claim was blocked on a
guard **its own hypotheses do not determine**, which is a defect of the
transcription and not an open mathematical question. Under the new one it is
discharged by `IsRecursive (R47.Agent2.scottHomC d e)`, whose guard is
`R47.Agent2.Consistent` — a condition on `d`, `e` and the index set alone, which
`R47.Agent2.bddAbove_stepsOf_iff` proves is exactly the existence of the join and
which `R47.Agent2.bddAbove_iff_exists_normal` reduces to §3.2's own condition 2.

## What is *not* done here

`ScottHomCRecursive` is not proved, and the obstruction is recursion theory, not
domain theory. Section 5 measures how much of it is left: the order test on
`consistentEnum` is reduced to a condition quantifying only over the two decoded
index sets, so what remains is (a) `Primrec` facts for the
`Denumerable (Finset (ℕ × ℕ))` coding, (b) a decision procedure for
`Consistent (pairsOf d e Q)` from `IsRecursive d` and `IsRecursive e`, and (c) a
decision procedure for `b ⊑ ⨆{values below a}` in `E`. None of the three is
`Nat.bitwise` and none is `REPred`, the two obstructions r0046 and r0047 measured
as real for other purposes.
-/

namespace ScottDomains.R49.Agent3

open ScottDomains ScottDomains.Effective ScottDomains.R47.Agent2

/-! ## 1. The join of no step functions -/

section Empty

variable {α β : Type*} [CompletePartialOrder α] [CompletePartialOrder β]

/-- `ofPairs ∅ = ⊥`. Needed because both enumerations fall back to `⊥` on the
indices their guard rejects, and `IsStepEnumeration` asks every value to be an
`ofPairs`: the empty index set is the one that names `⊥`.

`∅` is directed (vacuously), so `sSup ∅` is its least upper bound, and every
element — `⊥` included — is an upper bound of `∅`. -/
theorem ofPairs_empty : ScottHom.ofPairs (∅ : Set (α × β)) = (⊥ : ScottHom α β) := by
  have hs : ScottHom.stepsOf (∅ : Set (α × β)) = (∅ : Set (ScottHom α β)) := by
    ext g
    simp [ScottHom.stepsOf]
  have hdir : DirectedOn (· ≤ ·) (∅ : Set (ScottHom α β)) := fun _ hx => hx.elim
  rw [ScottHom.ofPairs, hs]
  exact le_bot_iff.mp (hdir.isLUB_sSup.2 fun _ hx => hx.elim)

end Empty

/-! ## 2. Both enumerations are step-function enumerations -/

section Arrow

variable {α β : Type*} [CompletePartialOrder α] [Domain α]
  [CompletePartialOrder β] [Domain β] [BoundedComplete β]

omit [BoundedComplete β] in
theorem pairsOf_empty (d : EffectivePresentation α) (e : EffectivePresentation β) :
    Effective.pairsOf d e (∅ : Finset (ℕ × ℕ)) = (∅ : Set (α × β)) := by
  simp [Effective.pairsOf]

/-- **The pre-r0049 subject witnesses the new statement.** On an index whose
guard holds, `scottHomEnum` is `ofPairs` of that index set; on the rest it is
`⊥`, which is `ofPairs` of the empty index set. -/
theorem isStepEnumeration_scottHom (d : EffectivePresentation α)
    (e : EffectivePresentation β) : IsStepEnumeration d e (Effective.scottHom d e) := by
  classical
  intro n
  by_cases h : IsCompactElement
      (ScottHom.ofPairs (Effective.pairsOf d e (Denumerable.ofNat (Finset (ℕ × ℕ)) n)))
  · exact ⟨Denumerable.ofNat (Finset (ℕ × ℕ)) n,
      Effective.scottHomEnum_of_ofNat d e rfl h⟩
  · refine ⟨(∅ : Finset (ℕ × ℕ)), ?_⟩
    show Effective.scottHomEnum d e n = _
    rw [Effective.scottHomEnum, if_neg h, pairsOf_empty, ofPairs_empty]

/-- **The consistency-guarded enumeration witnesses it too**, by the same two
cases. This is the half that matters: it is the enumeration whose guard is
determined by `d` and `e`. -/
theorem isStepEnumeration_scottHomC (d : EffectivePresentation α)
    (e : EffectivePresentation β) : IsStepEnumeration d e (scottHomC d e) := by
  classical
  intro n
  by_cases h : Consistent (Effective.pairsOf d e (Denumerable.ofNat (Finset (ℕ × ℕ)) n))
  · refine ⟨Denumerable.ofNat (Finset (ℕ × ℕ)) n, ?_⟩
    show consistentEnum d e n = _
    rw [consistentEnum, if_pos h]
  · refine ⟨(∅ : Finset (ℕ × ℕ)), ?_⟩
    show consistentEnum d e n = _
    rw [consistentEnum, if_neg h, pairsOf_empty, ofPairs_empty]

/-! ## 3. The pre-r0049 statement, and the direction of the change -/

/-- **`Effective.StepFunctionsDecidable` as it stood through r0048**, kept
verbatim so the r0049 restatement is auditable against the thing it replaced
rather than against a paraphrase.

It asserts that **one** enumeration of `K(D → E)` is recursive: `scottHom d e`,
whose guard is `IsCompactElement (ofPairs Q)`. r0047 refuted that guard as the
boundedness test the printed sentence is about, and refuted it *inside* the
hypotheses this statement grants — `R47.Agent2.natBot_guard_true_but_unbounded`
runs at `α = β = N⊥` under `R45.Agent1.natBotPresentation`, which
`R45.Agent1.isRecursive_natBot` proves is `IsRecursive`.

**This is not a claim of the paper and must not be counted as an open result.**
Gunter & Scott name no tie-break for an unbounded index set; the guard is ours. -/
def StepFunctionsDecidableCompactGuard (d : EffectivePresentation α)
    (e : EffectivePresentation β) : Prop :=
  IsRecursive d → IsRecursive e → IsRecursive (Effective.scottHom d e)

/-- **The r0049 restatement is a weakening of the proposition and not of the
paper.**

The kernel checks here that the pre-r0049 statement implies the post-r0049 one,
which is the direction that fixes what changed: one named enumeration became an
existential over the enumerations satisfying `IsStepEnumeration`, and
`isStepEnumeration_scottHom` says the named one is among them.

**Direction:** old → new, the same direction as r0046's
`R46.Agent1.stepFunctionsDecidable_of_unconditional` and the opposite of r0047's
`R47.Agent3.freeCarrier_of_preservesRecursivePresentation`. The complementary
check — that no bar was lowered — is `Effective.Theorem7ArrowRecursive`, which is
untouched and still reached from the new form by
`Effective.exists_isRecursive_of_stepFunctionsDecidable`. -/
theorem stepFunctionsDecidable_of_compactGuard {d : EffectivePresentation α}
    {e : EffectivePresentation β} (h : StepFunctionsDecidableCompactGuard d e) :
    StepFunctionsDecidable d e :=
  fun hd he => ⟨Effective.scottHom d e, isStepEnumeration_scottHom d e, h hd he⟩

/-! ## 4. The claim over the consistency-guarded enumeration -/

/-- **Theorem 7's proof sentence over the enumeration whose guard `d` and `e`
determine.** The literal restatement the r0049 plan asks for, kept as a named
claim rather than as the `def` itself: writing it *into*
`Effective.StepFunctionsDecidable` would commit the printed sentence to our
second choice of tie-break, where it makes none.

This is **the residue**, and it is recursion theory. `R47.Agent2.Consistent` is a
condition on `d`, `e` and the index set alone;
`R47.Agent2.bddAbove_stepsOf_iff` proves it is exactly the existence of the join,
and `R47.Agent2.bddAbove_iff_exists_normal` reduces deciding it to a search over
finite normal subposets which `R47.Agent2.isNormalIn_joinClosure` makes
terminate. Nothing here needs `Nat.bitwise` or `REPred`. -/
def ScottHomCRecursive (d : EffectivePresentation α) (e : EffectivePresentation β) :
    Prop :=
  IsRecursive d → IsRecursive e → IsRecursive (scottHomC d e)

/-- **The restated claim, discharged from the residue.** This is what the
restatement was for: the claim is now reachable through an enumeration whose
guard is determined by its own hypotheses. -/
theorem stepFunctionsDecidable_of_scottHomC {d : EffectivePresentation α}
    {e : EffectivePresentation β} (h : ScottHomCRecursive d e) :
    StepFunctionsDecidable d e :=
  fun hd he => ⟨scottHomC d e, isStepEnumeration_scottHomC d e, h hd he⟩

/-! ## 5. The order test on `consistentEnum`, as a finite condition

What `RecursiveLE (scottHomC d e)` asks for is a total recursive decision of
`consistentEnum d e m ≤ consistentEnum d e n`. The two lemmas here remove all
reference to the function space from that test: after them, every quantifier
ranges over the two decoded index sets, which are finite, and every atomic
condition is a `≤` in `E` against a join of finitely many compacts of `E`. -/

/-- The enumeration evaluated pointwise on a consistent index set: the value at
`x` is the join in `E` of the values whose sources lie below `x`. This is
`R47.Agent2.ofPairs_apply` transported through the guard.

Stated as two lemmas rather than one `if`, because the `if` in the *statement*
would need a `Decidable (Consistent …)` instance and the only one available is
`Classical.propDecidable` — writing the case split into the statement would put a
classical instance where a decision procedure is the thing being asked for. -/
theorem consistentEnum_apply_of_consistent (d : EffectivePresentation α)
    (e : EffectivePresentation β) {n : ℕ}
    (h : Consistent (Effective.pairsOf d e (Denumerable.ofNat (Finset (ℕ × ℕ)) n)))
    (x : α) :
    consistentEnum d e n x =
      sSup (Prod.snd ''
        belowSet (Effective.pairsOf d e (Denumerable.ofNat (Finset (ℕ × ℕ)) n)) x) := by
  classical
  show consistentEnum d e n x = _
  rw [consistentEnum, if_pos h]
  exact ofPairs_apply (finite_pairsOf d e _) (pairsOf_subset_compacts d e _) h x

omit [BoundedComplete β] in
/-- The other branch: on an inconsistent index set the enumeration is `⊥`, which
in `D → E` is the constant-`⊥` function. -/
theorem consistentEnum_apply_of_not_consistent (d : EffectivePresentation α)
    (e : EffectivePresentation β) {n : ℕ}
    (h : ¬ Consistent (Effective.pairsOf d e (Denumerable.ofNat (Finset (ℕ × ℕ)) n)))
    (x : α) : consistentEnum d e n x = ⊥ := by
  classical
  show consistentEnum d e n x = _
  rw [consistentEnum, if_neg h]
  rfl

/-- **The order on the enumeration is a finite condition on the two index sets.**

`R47.Agent2.ofPairs_le_iff` supplies the consistent case; the inconsistent case
is `⊥ ≤ _`, which is why the hypothesis appears on the right as an antecedent
rather than as a case split the caller must perform. Composed with
`consistentEnum_apply_of_consistent` the right-hand side mentions only: membership in the
decoded finset, `d.enum`, `e.enum`, `≤` in `E`, and a join in `E` of a finite set
of compacts.

This is the interface for the recursion theory. A decision procedure for the
right-hand side, plus the `Primrec` facts for the `Finset (ℕ × ℕ)` coding, is
`RecursiveLE (scottHomC d e)`. -/
theorem consistentEnum_le_iff (d : EffectivePresentation α) (e : EffectivePresentation β)
    (m n : ℕ) :
    consistentEnum d e m ≤ consistentEnum d e n ↔
      (Consistent (Effective.pairsOf d e (Denumerable.ofNat (Finset (ℕ × ℕ)) m)) →
        ∀ p ∈ Effective.pairsOf d e (Denumerable.ofNat (Finset (ℕ × ℕ)) m),
          p.2 ≤ consistentEnum d e n p.1) := by
  classical
  by_cases h : Consistent (Effective.pairsOf d e (Denumerable.ofNat (Finset (ℕ × ℕ)) m))
  · constructor
    · intro hle _
      have hEq : consistentEnum d e m
          = ScottHom.ofPairs (Effective.pairsOf d e
              (Denumerable.ofNat (Finset (ℕ × ℕ)) m)) := by
        rw [consistentEnum, if_pos h]
      rw [hEq] at hle
      exact (ofPairs_le_iff (finite_pairsOf d e _) (pairsOf_subset_compacts d e _) h).mp hle
    · intro hp
      have hEq : consistentEnum d e m
          = ScottHom.ofPairs (Effective.pairsOf d e
              (Denumerable.ofNat (Finset (ℕ × ℕ)) m)) := by
        rw [consistentEnum, if_pos h]
      rw [hEq]
      exact (ofPairs_le_iff (finite_pairsOf d e _) (pairsOf_subset_compacts d e _) h).mpr (hp h)
  · constructor
    · exact fun _ hc => absurd hc h
    · intro _
      have hEq : consistentEnum d e m = (⊥ : ScottHom α β) := by
        rw [consistentEnum, if_neg h]
      rw [hEq]
      exact bot_le

end Arrow

/-! ## 6. The same for `⊸`

`Effective` carries no `Prop`-valued claim for the strict half — r0046 stated the
reduction `R46.Agent3.theorem7StrictRecursive_of_strictStepFunctionsDecidable`
with the hypothesis written out rather than named. The strict counterpart of the
r0049 restatement is therefore *added* here, not restated: no existing `def`
changes. -/

section Strict

variable {α β : Type*} [CompletePartialOrder α] [Domain α]
  [CompletePartialOrder β] [Domain β] [BoundedComplete β]

/-- The `⊸` counterpart of `Effective.IsStepEnumeration`: every value enumerated
is the join of the **strict** step functions named by some finite set of index
pairs of `d` and `e`. -/
def IsStrictStepEnumeration [Domain (StrictHom α β)] (d : EffectivePresentation α)
    (e : EffectivePresentation β) (f : EffectivePresentation (StrictHom α β)) : Prop :=
  ∀ n : ℕ, ∃ Q : Finset (ℕ × ℕ), f.enum n = R46.Agent3.strictStepJoin d e Q

/-- **Theorem 7's third sentence at proof-sentence strength**, "similar facts
hold for `D ⊸ E`", stated the way r0049 states the arrow: some strict
step-function enumeration of `K(D ⊸ E)` built from `d` and `e` is recursive. -/
def StrictStepFunctionsDecidable [Domain (StrictHom α β)] (d : EffectivePresentation α)
    (e : EffectivePresentation β) : Prop :=
  IsRecursive d → IsRecursive e →
    ∃ f : EffectivePresentation (StrictHom α β),
      IsStrictStepEnumeration d e f ∧ IsRecursive f

omit [BoundedComplete β] in
theorem strictPairsOf_empty (d : EffectivePresentation α) (e : EffectivePresentation β) :
    R46.Agent3.strictPairsOf d e (∅ : Finset (ℕ × ℕ)) = (∅ : Set (α × β)) := by
  ext p
  simp [R46.Agent3.strictPairsOf, pairsOf_empty d e]

omit [BoundedComplete β] in
theorem strictStepJoin_empty (d : EffectivePresentation α) (e : EffectivePresentation β) :
    R46.Agent3.strictStepJoin d e (∅ : Finset (ℕ × ℕ)) = (⊥ : StrictHom α β) := by
  refine Subtype.ext ?_
  show ScottHom.ofPairs (R46.Agent3.strictPairsOf d e (∅ : Finset (ℕ × ℕ))) = _
  rw [strictPairsOf_empty, ofPairs_empty]
  rfl

/-- r0046's enumeration witnesses the strict statement. -/
theorem isStrictStepEnumeration_strictHom [Domain (StrictHom α β)]
    (d : EffectivePresentation α) (e : EffectivePresentation β) :
    IsStrictStepEnumeration d e (R46.Agent3.strictHom d e) := by
  classical
  intro n
  by_cases h : IsCompactElement
      (R46.Agent3.strictStepJoin d e (Denumerable.ofNat (Finset (ℕ × ℕ)) n))
  · refine ⟨Denumerable.ofNat (Finset (ℕ × ℕ)) n, ?_⟩
    show R46.Agent3.strictHomEnum d e n = _
    rw [R46.Agent3.strictHomEnum, if_pos h]
  · refine ⟨(∅ : Finset (ℕ × ℕ)), ?_⟩
    show R46.Agent3.strictHomEnum d e n = _
    rw [R46.Agent3.strictHomEnum, if_neg h, strictStepJoin_empty]

/-- r0047's consistency-guarded strict enumeration witnesses it as well. -/
theorem isStrictStepEnumeration_strictHomC [Domain (StrictHom α β)]
    (d : EffectivePresentation α) (e : EffectivePresentation β) :
    IsStrictStepEnumeration d e (strictHomC d e) := by
  classical
  intro n
  by_cases h : Consistent
      (R46.Agent3.strictPairsOf d e (Denumerable.ofNat (Finset (ℕ × ℕ)) n))
  · refine ⟨Denumerable.ofNat (Finset (ℕ × ℕ)) n, ?_⟩
    show strictConsistentEnum d e n = _
    rw [strictConsistentEnum, if_pos h]
  · refine ⟨(∅ : Finset (ℕ × ℕ)), ?_⟩
    show strictConsistentEnum d e n = _
    rw [strictConsistentEnum, if_neg h, strictStepJoin_empty]

/-- The strict residue, the `⊸` counterpart of `ScottHomCRecursive`. -/
def StrictHomCRecursive [Domain (StrictHom α β)] (d : EffectivePresentation α)
    (e : EffectivePresentation β) : Prop :=
  IsRecursive d → IsRecursive e → IsRecursive (strictHomC d e)

theorem strictStepFunctionsDecidable_of_strictHomC [Domain (StrictHom α β)]
    {d : EffectivePresentation α} {e : EffectivePresentation β}
    (h : StrictHomCRecursive d e) : StrictStepFunctionsDecidable d e :=
  fun hd he => ⟨strictHomC d e, isStrictStepEnumeration_strictHomC d e, h hd he⟩

/-- The strict statement is also reached from r0046's enumeration, which is the
`⊸` reading of `stepFunctionsDecidable_of_compactGuard` — same direction. -/
theorem strictStepFunctionsDecidable_of_strictHom [Domain (StrictHom α β)]
    {d : EffectivePresentation α} {e : EffectivePresentation β}
    (h : IsRecursive d → IsRecursive e → IsRecursive (R46.Agent3.strictHom d e)) :
    StrictStepFunctionsDecidable d e :=
  fun hd he => ⟨R46.Agent3.strictHom d e, isStrictStepEnumeration_strictHom d e, h hd he⟩

omit [BoundedComplete β] in
/-- Theorem 7's third sentence at recursion-theoretic strength, from the strict
statement at fixed `d` and `e`. -/
theorem exists_isRecursive_of_strictStepFunctionsDecidable [Domain (StrictHom α β)]
    {d : EffectivePresentation α} {e : EffectivePresentation β}
    (h : StrictStepFunctionsDecidable d e) (hd : IsRecursive d) (he : IsRecursive e) :
    ∃ f : EffectivePresentation (StrictHom α β), IsRecursive f :=
  let ⟨f, _, hf⟩ := h hd he
  ⟨f, hf⟩

end Strict

/-! ## 7. What the residue closes

The plan's arithmetic, checked. From the universal closure of `ScottHomCRecursive`
follow three claims — `Effective.StepFunctionsDecidable`,
`Effective.Theorem7ArrowRecursive`, and `Effective.PreservesRecursivePresentation`
at `R47.Agent3.arrowOp` — and from the strict residue a fourth,
`Effective.Theorem7StrictRecursive`. The last of the three is
`R47.Agent3.preservesRecursivePresentation_arrowOp_iff`, which holds at a single
universe, so the composite is stated at `u = v`. -/

/-- **Three claims from one residue**, at a single universe. -/
theorem three_claims_of_residue.{u}
    (h : ∀ {α : Type u} {β : Type u} [CompletePartialOrder α] [Domain α]
      [CompletePartialOrder β] [Domain β] [BoundedComplete β]
      (d : EffectivePresentation α) (e : EffectivePresentation β), ScottHomCRecursive d e) :
    (∀ {α : Type u} {β : Type u} [CompletePartialOrder α] [Domain α]
        [CompletePartialOrder β] [Domain β] [BoundedComplete β]
        (d : EffectivePresentation α) (e : EffectivePresentation β),
        StepFunctionsDecidable d e) ∧
      Effective.Theorem7ArrowRecursive.{u, u} ∧
      Effective.PreservesRecursivePresentation R47.Agent3.arrowOp.{u} := by
  have harrow : Effective.Theorem7ArrowRecursive.{u, u} :=
    theorem7ArrowRecursive_of_scottHomC fun d e hd he => h d e hd he
  exact ⟨fun d e => stepFunctionsDecidable_of_scottHomC (h d e), harrow,
    R47.Agent3.preservesRecursivePresentation_arrowOp_iff.mpr harrow⟩

/-- **The fourth**, from the strict residue. -/
theorem theorem7StrictRecursive_of_residue.{u}
    (h : ∀ {α : Type u} {β : Type u} [CompletePartialOrder α] [Domain α]
      [CompletePartialOrder β] [Domain β] [BoundedComplete β] [Domain (StrictHom α β)]
      (d : EffectivePresentation α) (e : EffectivePresentation β), StrictHomCRecursive d e) :
    Effective.Theorem7StrictRecursive.{u, u} :=
  theorem7StrictRecursive_of_strictHomC fun d e hd he => h d e hd he

/-! ## 8. The paper's own index set carries no guard at all

Read Theorem 7's proof, printed p. 12, on its own terms:

> Suppose `N ◁ K(D)` is finite and `s : N → K(E)` is monotone. Then the function
> `step(s) : D → E` given by taking `step(s)(x) = ⨆{f(y) | y ∈ N ∩ ↓x}` is
> continuous and compact in the ordering on `D → E`. These are called *step
> functions* and it is possible to show that they form a basis for `D → E`.

(`f(y)` is a misprint for `s(y)`: `f` is not bound anywhere in the sentence.)

**Gunter & Scott index the basis by a pair `(N, s)` — `N` a finite normal
subposet of `K(D)`, `s` a monotone map into `K(E)` — and not by an arbitrary
finite set of pairs.** That is the whole reason their step is "tedious, but not
difficult": on their index there is no boundedness question to decide. `N` normal
makes `N ∩ ↓x` directed for *every* `x` (`directedOn_inter_Iic_of_isNormalIn`),
`s` monotone carries that to a directed subset of `E`, and a directed set in a cpo
has a supremum. The join in the displayed formula therefore always exists.

`consistent_stepPairs` is that statement in this development's terms: the guard
`R47.Agent2.Consistent`, which r0047 built to replace the refuted compactness
test, is **identically true** on the paper's index sets. Neither guard is the
paper's — `Effective.scottHomEnum` guards because our transcription enumerates by
`Finset (ℕ × ℕ)`, which admits index sets the paper's parametrization cannot
name.

Both index sets reach the same basis: this section's `stepPairs N s` is a set of
pairs like any other, so `R47.Agent2.pairSupHom` applied to it *is* `step(s)` —
`snd_belowSet_stepPairs` identifies the two formulas symbol for symbol. What
differs is the recursion theory, and it differs in the direction that matters:
deciding the paper's side conditions is §3.2's condition 2 applied to `u`
(is `{dₙ | n ∈ u} ◁ K(D)`?) and condition 1 applied finitely often (is `s`
monotone?), whereas deciding `Consistent (pairsOf d e Q)` is a search.
-/

section PaperIndex

variable {α β : Type*} [CompletePartialOrder α] [BoundedComplete α]
  [CompletePartialOrder β]

/-- **A normal subposet of `K(D)` cuts a directed set below *every* element**, not
only below the compact ones. `IsNormalIn` gives directedness below members of
`K(D)`; bounded completeness of `D` extends it to all of `D`, because a pair of
compacts below `x` has a join, that join is compact
(`isCompactElement_of_isLUB_pair`) and is still below `x`. -/
theorem directedOn_inter_Iic_of_isNormalIn {N : Set α} (hN : N ◁ compacts α) (x : α) :
    DirectedOn (· ≤ ·) (N ∩ Set.Iic x) := by
  rintro a ⟨haN, hax⟩ b ⟨hbN, hbx⟩
  have hub : ∀ z ∈ ({a, b} : Set α), z ≤ x := by
    rintro z hz
    rcases Set.mem_insert_iff.mp hz with rfl | rfl
    · exact Set.mem_Iic.mp hax
    · exact Set.mem_Iic.mp hbx
  have hlub := isLUB_sSup_of_bddAbove (⟨x, hub⟩ : BddAbove ({a, b} : Set α))
  have hc : IsCompactElement (sSup ({a, b} : Set α)) :=
    isCompactElement_of_isLUB_pair (hN.subset haN) (hN.subset hbN) hlub
  obtain ⟨w, ⟨hwN, hwc⟩, haw, hbw⟩ :=
    hN.directedOn hc a ⟨haN, Set.mem_Iic.mpr (hlub.1 (Set.mem_insert _ _))⟩
      b ⟨hbN, Set.mem_Iic.mpr (hlub.1 (Set.mem_insert_of_mem _ rfl))⟩
  exact ⟨w, ⟨hwN, Set.mem_Iic.mpr ((Set.mem_Iic.mp hwc).trans (hlub.2 hub))⟩, haw, hbw⟩

/-- **The paper's index set**: the graph of `s` over `N`. Gunter & Scott's
`step(s)` is `R47.Agent2.pairSupHom` at this set — see `snd_belowSet_stepPairs`. -/
def stepPairs (N : Set α) (s : α → β) : Set (α × β) := (fun y => (y, s y)) '' N

omit [BoundedComplete α] [CompletePartialOrder β] in
/-- The two formulas are the same one. `R47.Agent2.pairSup (stepPairs N s) x` is
`sSup (Prod.snd '' belowSet (stepPairs N s) x)` by definition, and this rewrites
its argument to `s '' (N ∩ ↓x)` — the printed `⨆{s(y) | y ∈ N ∩ ↓x}`. -/
theorem snd_belowSet_stepPairs (N : Set α) (s : α → β) (x : α) :
    Prod.snd '' R47.Agent2.belowSet (stepPairs N s) x = s '' (N ∩ Set.Iic x) := by
  ext b
  constructor
  · rintro ⟨p, ⟨hp, hpx⟩, rfl⟩
    obtain ⟨y, hyN, rfl⟩ := hp
    exact ⟨y, ⟨hyN, Set.mem_Iic.mpr hpx⟩, rfl⟩
  · rintro ⟨y, ⟨hyN, hyx⟩, rfl⟩
    exact ⟨(y, s y), ⟨⟨y, hyN, rfl⟩, Set.mem_Iic.mp hyx⟩, rfl⟩

/-- **The guard is vacuous on the paper's index sets.**

`R47.Agent2.Consistent (stepPairs N s)` holds for *every* normal `N` and monotone
`s` — no finiteness, no compactness of the values, no hypothesis beyond the two
the printed sentence states. With `R47.Agent2.bddAbove_stepsOf_iff` this says the
step functions the paper names are always bounded above, so the join defining
`step(s)` always exists and the enumeration Gunter & Scott describe has **no junk
branch to guard**.

The consequence for this development is a measurement, not a repair: the
boundedness decision that `ScottHomCRecursive` still owes is an artifact of
enumerating `K(D → E)` by `Finset (ℕ × ℕ)`. Re-indexing by `(u, s)` — `u` a
finite index set with `{dₙ | n ∈ u} ◁ K(D)`, `s` a monotone map on it — replaces
that decision by §3.2's own two conditions, which is what "using the effective
presentations of `D` and `E`" refers to. -/
theorem consistent_stepPairs {N : Set α} (hN : N ◁ compacts α) {s : α → β}
    (hmono : ∀ y ∈ N, ∀ z ∈ N, y ≤ z → s y ≤ s z) :
    R47.Agent2.Consistent (stepPairs N s) := by
  rintro S hS ⟨x, hx⟩
  have hdir : DirectedOn (· ≤ ·) (s '' (N ∩ Set.Iic x)) := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    obtain ⟨w, hw, haw, hbw⟩ := directedOn_inter_Iic_of_isNormalIn hN x a ha b hb
    exact ⟨s w, ⟨w, hw, rfl⟩, hmono a ha.1 w hw.1 haw, hmono b hb.1 w hw.1 hbw⟩
  refine ⟨sSup (s '' (N ∩ Set.Iic x)), ?_⟩
  rintro _ ⟨p, hp, rfl⟩
  obtain ⟨y, hyN, rfl⟩ := hS hp
  exact hdir.le_sSup ⟨y, ⟨hyN, Set.mem_Iic.mpr (hx ⟨_, hp, rfl⟩)⟩, rfl⟩

end PaperIndex

end ScottDomains.R49.Agent3
