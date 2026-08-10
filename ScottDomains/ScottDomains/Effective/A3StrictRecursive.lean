import ScottDomains.Effective.FunctionSpace

/-!
# r0046, agent3: the enumeration of `K(D ⊸ E)`

Gunter & Scott, *Semantic Domains*, Theorem 7's third sentence — "Similar facts
hold for `D ⊸ E`" — and the reason the paper gives for it: **the strict step
functions form a basis of `D ⊸ E`.**

`Effective/FunctionSpace.lean` records that this development had no such basis.
Its `theorem7_strict` proves Theorem 7's third sentence from
`nonempty_effectivePresentation`, with the arguments `d` and `e` **unused**, and
`Theorem7StrictRecursive`'s docstring names the gap:

> the paper's argument is that "the strict step functions form a basis", and this
> development has no strict-step-function basis to enumerate —
> `PRepFun.strictHomDomain` gets `K(D ⊸ E)` countable by injection into
> `K(D → E)`, which names no enumeration.

That was an accurate measurement of the state of the tree. This module removes
it. The basis is built, the enumeration is built, and `strictHom d e` is an
`EffectivePresentation (StrictHom α β)` whose `enum` uses `d` and `e` and whose
values are joins of **strict** step functions named by indices.

## The whole content is one four-line lemma that was already present

`PRepFun.isStrict_of_le` says anything below a strict function is strict. Apply it
to `ScottHom.exists_finite_isLUB_of_isCompactElement`, which writes a compact
function as the least upper bound of a finite set of step functions **below it**,
and every one of those step functions is strict as soon as the function is. So the
strict step functions below a strict compact are exactly the step functions below
it: no separate theory is needed, and `exists_strictSteps_isLUB` below is the
paper's sentence, proved in seven lines.

## The naming of a strict step function is a decidable-shaped side condition

`isStrict_iff_of_isStepPair` is the characterisation the enumeration runs on: a
step function named by the compact pair `(k, b)` is strict **iff** `k = ⊥ → b = ⊥`.
So the set of index pairs naming strict step functions is cut out of
`Effective.pairsOf` by a condition on the pair alone, and `strictPairsOf` is that
cut. Every join of a set of pairs satisfying it is strict outright
(`isStrict_ofPairs`, from `ScottDomains.isStrict_sSup`), which is what lets
`strictStepJoin` land in the subtype with no side condition on the *set*.

## What this does and does not close

| # | Statement | Before | After |
| -- | --------- | ------ | ----- |
| 1 | `K(D ⊸ E)` has an enumeration built from `d`, `e` | absent | `strictHomEnum`, `exists_strictHomEnum_eq` |
| 2 | the strict step functions are a basis of `D ⊸ E` | absent | `exists_strictSteps_isLUB` |
| 3 | `Effective.theorem7_strict` with `d`, `e` used | `d`, `e` unused | `theorem7_strict_ofEnum` |
| 4 | `Effective.Theorem7StrictRecursive` | open, needing 1 **and** recursion theory | open, needing recursion theory **only** |

Row 4 is the measurement this module exists for.
`theorem7StrictRecursive_of_strictStepFunctionsDecidable` reduces the claim to one
hypothesis of exactly the shape `R45.Agent1.theorem7ArrowRecursive_of_stepFunctionsDecidable`
reduces the arrow claim to — `IsRecursive d → IsRecursive e → IsRecursive
(strictHom d e)`. So `⊸` is no longer harder than `→`; the two are now blocked on
the *same* two recursion-theoretic obstructions named in
`Effective/FunctionSpace.lean`'s module docstring (no `Primrec` fact about
`Nat.bitwise` in Mathlib v4.32.2, and `REPred` closed under neither `∧` nor `∃`).

The two `Decidable` fields of `strictHom` are `Classical.dec`, exactly as
`Effective.scottHom`'s are, and for the same reason. This module does not claim to
decide anything; it claims to have the enumeration, which is the ingredient that
was missing.

## The `[Domain (StrictHom α β)]` binder is the claim's own

`Theorem7StrictRecursive`'s `def` carries `[Domain (StrictHom α β)]`, so using it
here is not an added hypothesis. It is discharged at any use site by
`PRepFun.strictHomDomain`, and the `example` at the end of this module checks that
it is discharged from `[Domain α] [Domain β] [BoundedComplete β]` alone.
-/

namespace ScottDomains.R46.Agent3

open ScottDomains ScottDomains.Effective

variable {α β : Type*} [CompletePartialOrder α] [Domain α]
  [CompletePartialOrder β] [Domain β] [BoundedComplete β]

/-! ## 1. Which step functions are strict -/

omit [Domain α] [Domain β] [BoundedComplete β] in
/-- **A step function is strict exactly when its source is not `⊥`, or its value
is.** `g` is named by `(k, b)`, so `g ⊥ = if k ≤ ⊥ then b else ⊥`; and `k ≤ ⊥` is
`k = ⊥`. Both directions read off that one evaluation.

This is the paper's "strict step function" made into a condition on the *pair*,
which is what an enumeration indexed by pairs of indices needs. -/
theorem isStrict_iff_of_isStepPair {g : ScottHom α β} {p : α × β}
    (h : ScottHom.IsStepPair g p) : IsStrict g ↔ (p.1 = ⊥ → p.2 = ⊥) := by
  have hg : g ⊥ = ScottHom.stepFun p.1 p.2 ⊥ := congrFun h.2.2 ⊥
  constructor
  · intro hs hp1
    have hval : ScottHom.stepFun p.1 p.2 (⊥ : α) = p.2 :=
      ScottHom.stepFun_of_le (le_of_eq hp1)
    rw [← hval, ← hg]
    exact hs
  · intro hp
    show g ⊥ = ⊥
    rw [hg]
    by_cases hle : p.1 ≤ (⊥ : α)
    · rw [ScottHom.stepFun_of_le hle]
      exact hp (le_bot_iff.mp hle)
    · exact ScottHom.stepFun_of_not_le hle

omit [Domain α] [Domain β] [BoundedComplete β] in
/-- **A join of strict step functions is strict**, for every set of naming pairs
satisfying the condition — no boundedness hypothesis, because
`ScottDomains.isStrict_sSup` covers both branches of `ScottHom`'s total `sSup`.

This is what lets the enumeration land in the subtype without carrying a proof
about the *set* of pairs. -/
theorem isStrict_ofPairs {P : Set (α × β)} (hP : ∀ p ∈ P, p.1 = ⊥ → p.2 = ⊥) :
    IsStrict (ScottHom.ofPairs P) := by
  refine isStrict_sSup ?_
  rintro f ⟨p, hp, hstep⟩
  exact (isStrict_iff_of_isStepPair hstep).mpr (hP p hp)

/-! ## 2. The strict step functions are a basis of `D ⊸ E`

The paper's reason for Theorem 7's third sentence, and the thing
`Effective/FunctionSpace.lean` records as absent. -/

/-- **Every compact element of `D ⊸ E` is the least upper bound of a finite set of
strict step functions with compact data.** This is Gunter & Scott's "the strict
step functions form a basis".

The proof is `ScottHom.exists_finite_isLUB_of_isCompactElement` at `g.val` —
legitimate because `ClosureProperties.isCompactElement_val_of_isCompactElement`
carries compactness from the subtype to `D → E` — followed by
`PRepFun.isStrict_of_le` on each member. The members are *below* `g.val` by
construction (`ScottHom.stepsBelow`), and `g.val` is strict, so each is strict.
**No strictification and no separate strict-step theory is required**, which is
the measurement: the basis was four lines from the tree the whole time. -/
theorem exists_strictSteps_isLUB {g : StrictHom α β} (hg : IsCompactElement g) :
    ∃ S : Set (ScottHom α β), S.Finite ∧ S ⊆ ScottHom.stepsBelow (g.val : ScottHom α β) ∧
      (∀ h ∈ S, IsStrict h) ∧ IsLUB S (g.val : ScottHom α β) := by
  obtain ⟨S, hfin, hsub, hlub⟩ :=
    ScottHom.exists_finite_isLUB_of_isCompactElement
      (ClosureProperties.isCompactElement_val_of_isCompactElement hg)
  exact ⟨S, hfin, hsub, fun h hh =>
    PRepFun.isStrict_of_le g.2 (ScottHom.le_of_mem_stepsBelow (hsub hh)), hlub⟩

/-! ## 3. The enumeration of `K(D ⊸ E)` -/

/-- The index pairs of `Q` that name a **strict** step function. The cut is by
`isStrict_iff_of_isStepPair`: it is a condition on the pair of compacts alone. -/
def strictPairsOf (d : EffectivePresentation α) (e : EffectivePresentation β)
    (Q : Finset (ℕ × ℕ)) : Set (α × β) :=
  {p | p ∈ Effective.pairsOf d e Q ∧ (p.1 = ⊥ → p.2 = ⊥)}

/-- The join of the strict step functions named by `Q`, as an element of
`D ⊸ E`. Strictness is `isStrict_ofPairs`; no hypothesis on `Q` is needed. -/
noncomputable def strictStepJoin (d : EffectivePresentation α)
    (e : EffectivePresentation β) (Q : Finset (ℕ × ℕ)) : StrictHom α β :=
  ⟨ScottHom.ofPairs (strictPairsOf d e Q), isStrict_ofPairs fun _ hp => hp.2⟩

open Classical in
/-- **The enumeration of `K(D ⊸ E)` induced by `d` and `e`.** The `n`-th value is
the join of the strict step functions named by the `n`-th finite set of index
pairs, when that join is compact, and `⊥` otherwise.

The fallback is the same one `Effective.scottHomEnum` needs and for the same
reason: a finite set of step functions need not be bounded above, `sSup` on
`ScottHom` is total, so the join is a junk value there and need not be compact.
The test is classical, so this is `noncomputable`. -/
noncomputable def strictHomEnum (d : EffectivePresentation α)
    (e : EffectivePresentation β) (n : ℕ) : StrictHom α β :=
  if IsCompactElement (strictStepJoin d e (Denumerable.ofNat (Finset (ℕ × ℕ)) n))
    then strictStepJoin d e (Denumerable.ofNat (Finset (ℕ × ℕ)) n)
    else ⊥

omit [BoundedComplete β] in
theorem strictHomEnum_isCompactElement (d : EffectivePresentation α)
    (e : EffectivePresentation β) (n : ℕ) : IsCompactElement (strictHomEnum d e n) := by
  classical
  simp only [strictHomEnum]
  split_ifs with h
  · exact h
  · exact isCompactElement_bot

/-- **The enumeration exhausts `K(D ⊸ E)`.**

The three steps, in order. (1) `exists_strictSteps_isLUB` writes the compact `g`
as the join of a finite set `S` of strict step functions. (2) `ScottHom.stepPairOf`
names each member of `S` by a compact pair, and
`ScottHom.stepsOf_image_stepPairOf` reads the naming back, so `S` is recovered
from a finite set `P` of pairs; every member of `P` satisfies the strictness
condition by `isStrict_iff_of_isStepPair`, hence `strictPairsOf` on `P`'s index
set is `P` itself. (3) surjectivity of `d.enum` and `e.enum` pulls each pair back
to a pair of indices, a choice on a finite set, whose image names a
`Finset (ℕ × ℕ)`; `Effective.surjective_ofNat_finset` supplies its index. -/
theorem exists_strictHomEnum_eq (d : EffectivePresentation α) (e : EffectivePresentation β)
    {g : StrictHom α β} (hg : IsCompactElement g) : ∃ n, strictHomEnum d e n = g := by
  classical
  obtain ⟨S, hfin, hsub, hstrictS, hlub⟩ := exists_strictSteps_isLUB hg
  have hstepS : ∀ h ∈ S, ∃ p, ScottHom.IsStepPair h p := fun h hh => (hsub hh).1
  have hstepsP : ScottHom.stepsOf (ScottHom.stepPairOf '' S) = S :=
    ScottHom.stepsOf_image_stepPairOf hstepS
  have hPstrict : ∀ p ∈ ScottHom.stepPairOf '' S, p.1 = ⊥ → p.2 = ⊥ := by
    rintro _ ⟨h, hh, rfl⟩
    exact (isStrict_iff_of_isStepPair (ScottHom.isStepPair_stepPairOf (hstepS h hh))).mp
      (hstrictS h hh)
  have hchoice : ∀ p ∈ ScottHom.stepPairOf '' S, ∃ q : ℕ × ℕ, (d.enum q.1, e.enum q.2) = p := by
    rintro _ ⟨h, hh, rfl⟩
    have hp := ScottHom.isStepPair_stepPairOf (hstepS h hh)
    obtain ⟨i, hi⟩ := d.enum_surjective _ hp.1
    obtain ⟨j, hj⟩ := e.enum_surjective _ hp.2.1
    exact ⟨(i, j), by rw [hi, hj]⟩
  choose! φ hφ using hchoice
  have hPfin : (ScottHom.stepPairOf '' S).Finite := hfin.image _
  have hpairs : Effective.pairsOf d e (hPfin.image φ).toFinset = ScottHom.stepPairOf '' S := by
    rw [Effective.pairsOf, Set.Finite.coe_toFinset]
    ext p
    constructor
    · rintro ⟨_, ⟨p', hp', rfl⟩, rfl⟩
      show (d.enum (φ p').1, e.enum (φ p').2) ∈ ScottHom.stepPairOf '' S
      rw [hφ p' hp']
      exact hp'
    · intro hp
      exact ⟨φ p, ⟨p, hp, rfl⟩, hφ p hp⟩
  have hstrictPairs : strictPairsOf d e (hPfin.image φ).toFinset = ScottHom.stepPairOf '' S := by
    rw [strictPairsOf, hpairs]
    ext p
    exact ⟨fun h => h.1, fun h => ⟨h, hPstrict p h⟩⟩
  have hjoin : (strictStepJoin d e (hPfin.image φ).toFinset).val = (g.val : ScottHom α β) := by
    show ScottHom.ofPairs (strictPairsOf d e (hPfin.image φ).toFinset) = _
    rw [hstrictPairs, ScottHom.ofPairs, hstepsP]
    exact (hlub.unique (isLUB_sSup_of_bddAbove ⟨(g.val : ScottHom α β), hlub.1⟩)).symm
  have heq : strictStepJoin d e (hPfin.image φ).toFinset = g := Subtype.ext hjoin
  have hcpt : IsCompactElement (strictStepJoin d e (hPfin.image φ).toFinset) := by
    rw [heq]; exact hg
  obtain ⟨n, hn⟩ := Effective.surjective_ofNat_finset (hPfin.image φ).toFinset
  refine ⟨n, ?_⟩
  simp only [strictHomEnum, hn]
  rw [if_pos hcpt]
  exact heq

open Classical in
/-- **An effective presentation of `D ⊸ E`, built from those of `D` and `E`** —
the enumeration Theorem 7's third sentence asks for.

Contrast `Effective.theorem7_strict`, which proves the same existential from
`nonempty_effectivePresentation` with `d` and `e` unused. Here `d` and `e` supply
the indices the enumeration runs over and the surjectivity that makes it exhaust
`K(D ⊸ E)`. The two `Decidable` fields are `Classical.dec`, exactly as
`Effective.scottHom`'s are. -/
noncomputable def strictHom [Domain (StrictHom α β)] (d : EffectivePresentation α)
    (e : EffectivePresentation β) : EffectivePresentation (StrictHom α β) where
  enum := strictHomEnum d e
  enum_mem_compacts := strictHomEnum_isCompactElement d e
  enum_surjective _ hg := exists_strictHomEnum_eq d e hg
  decidableLE _ := Classical.dec _
  decidableNormal _ := Classical.dec _

/-- **Theorem 7's third sentence with its hypotheses used.** The same statement as
`Effective.theorem7_strict`, but the witness is `strictHom d e` rather than
`nonempty_effectivePresentation _`, so `d` and `e` are consumed. -/
theorem theorem_7_strict_ofEnum [Domain (StrictHom α β)] (d : EffectivePresentation α)
    (e : EffectivePresentation β) : Nonempty (EffectivePresentation (StrictHom α β)) :=
  ⟨strictHom d e⟩

alias theorem7_strict_ofEnum := theorem_7_strict_ofEnum

/-! ## 4. What `Theorem7StrictRecursive` still needs, and what it no longer needs -/

/-- Theorem 7's proof sentence for `⊸`, at fixed `d` and `e`: once the strict
step-function poset is shown to have recursive ordering and recursive finite
normal subposets, the theorem *is* that presentation.

The `⊸` counterpart of `Effective.exists_isRecursive_of_stepFunctionsDecidable`,
and it has the same one-line proof — which is the point. Before this module the
statement could not even be formed, because `strictHom d e` did not exist. -/
theorem exists_isRecursive_of_strictStepFunctionsDecidable [Domain (StrictHom α β)]
    {d : EffectivePresentation α} {e : EffectivePresentation β}
    (h : IsRecursive (strictHom d e)) :
    ∃ f : EffectivePresentation (StrictHom α β), IsRecursive f :=
  ⟨strictHom d e, h⟩

/-- **`Effective.Theorem7StrictRecursive` reduced to one hypothesis**, of exactly
the shape `R45.Agent1.theorem7ArrowRecursive_of_stepFunctionsDecidable` reduces the
arrow claim to.

Nothing here is an added instance binder: the binder list is the one
`Theorem7StrictRecursive`'s own `def` carries, `[Domain (StrictHom α β)]`
included. What changed is the hypothesis — it used to be "an enumeration of
`K(D ⊸ E)`, which does not exist, **and** the recursion theory"; it is now the
recursion theory alone.

The hypothesis is the strengthened form `IsRecursive d → IsRecursive e →
IsRecursive (strictHom d e)` rather than the bare conclusion, for the reason
r0045's agent1 records for the arrow: the paper's proof sentence says "using the
effective presentations of `D` and `E`", so the recursiveness of the *inputs* is
available to the argument. -/
theorem theorem_7_strictRecursive_of_strictStepFunctionsDecidable.{u, v}
    (h : ∀ {α : Type u} {β : Type v} [CompletePartialOrder α] [Domain α]
      [CompletePartialOrder β] [Domain β] [BoundedComplete β] [Domain (StrictHom α β)]
      (d : EffectivePresentation α) (e : EffectivePresentation β),
      IsRecursive d → IsRecursive e → IsRecursive (strictHom d e)) :
    Effective.Theorem7StrictRecursive.{u, v} := by
  intro α β _ _ _ _ _ _ d e hd he
  exact ⟨strictHom d e, h d e hd he⟩

alias theorem7StrictRecursive_of_strictStepFunctionsDecidable :=
  theorem_7_strictRecursive_of_strictStepFunctionsDecidable

/-- The `[Domain (StrictHom α β)]` binder used above is discharged from the
hypotheses Theorem 7 actually states — the same check `Effective.lean`'s
`theorem7_strict` records for its own binder. -/
example : Domain (StrictHom α β) := PRepFun.strictHomDomain

end ScottDomains.R46.Agent3
