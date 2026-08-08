import ScottDomains.ComputableFunction
import ScottDomains.FunctionSpaceCountable
import ScottDomains.PRepFun
-- `Denumerable (Finset (ℕ × ℕ))`, which names the finite sets of index pairs the
-- enumeration of `K(D → E)` runs over.
import Mathlib.Logic.Equiv.Finset

/-!
# Theorem 7's second and third sentences: effective presentations of `D → E` and `D ⊸ E`

Gunter & Scott, *Semantic Domains*, Theorem 7 (printed p. 12), quoted in full:

> **Theorem 7** If `D` and `E` are bounded complete domains, then `D → E` is also a
> bounded complete domain. Moreover, if `D` and `E` have effective presentations,
> then `D → E` has an effective presentation as well. Similar facts hold for
> `D ⊸ E`.

with the proof sketch's middle sentence:

> The proof that the poset of step functions has decidable ordering and finite
> normal subposets is tedious, but not difficult, using the effective
> presentations of `D` and `E`.

and §3.2's closing claim:

> In the remaining sections of the chapter we will discuss a great many operators
> like `· → ·` and `· ⊸ ·`. We will leave it to the reader to convince himself
> that all of these operators preserve the property of having an effective
> presentation.

`FunctionSpaceCountable.lean` proved the **first** sentence
(`isBoundedCompleteDomain_scottHom`) and `PRepFun.strictHomDomain` its `⊸`
counterpart. The second and third sentences had no Lean statement of any kind —
r0040 measured them as the only numbered property in the paper in that state.

## The measurement this file starts from: the definition as rendered is degenerate

`EffectivePresentation` reads the paper's "effectively decidable" as a Lean
`DecidablePred`. `EffectivePresentation.lean`'s own docstring already recorded that
a `Decidable` instance may be `Classical.dec`. The consequence is stronger than
that note suggests and is proved here as `nonempty_effectivePresentation`:

> **Every** domain has an effective presentation.

`Domain` requires `K(D)` countable, `K(D)` contains `⊥`, so a surjection
`ℕ ↠ K(D)` exists (`Set.Countable.exists_eq_range`), and both decidability
conditions are then discharged by `Classical.dec`. Nothing else is needed. So at
this strength Theorem 7's second sentence, its third sentence, and §3.2's closing
claim about *every* operator of §§4–7 are all corollaries of the corresponding
`Domain` instances, which the development already had. They are stated below and
proved, and the proofs are one line each — which is the finding, not an
achievement.

## What is built anyway, and why

`scottHom` below does **not** take that shortcut for the enumeration. It builds
the paper's own enumeration of `K(D → E)`: index a finite set of pairs of indices
by `Denumerable (Finset (ℕ × ℕ))`, read it as a finite set of compact pairs
(`pairsOf`), and take the join of the step functions those pairs name
(`ScottHom.ofPairs`, from `FunctionSpaceCountable.lean`). Surjectivity onto
`K(D → E)` is exactly `ScottHom.exists_ofPairs_of_isCompactElement` — every
compact function is a finite join of step functions — so the enumeration is the
one Theorem 7's proof sketch describes, not an abstract re-indexing.

One guard is needed and is where the paper's own difficulty sits. A finite set of
step functions need not be bounded above, and `sSup` on `ScottHom` is total, so
`ofPairs P` is a junk value on such a `P` and need not be compact. `scottHomEnum`
therefore tests `IsCompactElement (ofPairs P)` and falls back to `⊥`, which is
compact. **That test is the paper's "tedious, but not difficult" step**: deciding
whether the join of a finite set of step functions exists is what condition 2 of
an effective presentation of `E` is for. Here it is a classical `if`, so the
enumeration is `noncomputable`.

## The two decidability fields, and the recursion-theoretic form

`scottHom`'s `decidableLE` and `decidableNormal` are `Classical.dec`. The content
they are standing in for is stated, not assumed away:

| # | Name | What it says | Status |
| -- | ---- | ------------ | ------ |
| 1 | `RecursiveNormal`, `IsRecursive` | conditions 1 and 2 decided by a total recursive function, not a Lean `Decidable` | definitions |
| 2 | `StepFunctionsDecidable` | Theorem 7's proof sentence: `IsRecursive (scottHom d e)` | named `Prop`, open |
| 3 | `Theorem7ArrowRecursive` | Theorem 7's second sentence at that strength | named `Prop`, open |
| 4 | `PreservesRecursivePresentation` | §3.2's closing claim, one instance per operator | named `Prop` schema, open |

`exists_isRecursive_of_stepFunctionsDecidable` proves row 2 ⟹ row 3 at fixed
`d`, `e`, which is the paper's own proof structure: the theorem *is* the
decidability of the step-function poset.

Two obstructions block discharging rows 2–4 here, and both are recursion theory
rather than domain theory:

* `RecursiveLE` for `P N` — the one presentation this development has
  (`Effective/Powerset.lean`) — reduces to `Computable fun p : ℕ × ℕ => p.1 ||| p.2`,
  and Mathlib v4.32.2 states no `Primrec`/`Computable` fact about `Nat.lor`,
  `Nat.bitwise` or `Nat.testBit`.
* `ComputableFunction.lean` already records the second: `REPred`'s API in this
  Mathlib is five lemmas and supplies closure under neither `∧` nor `∃`, so even
  composition of computable functions is unavailable.

Neither is rediscovered here; both are cited.
-/

namespace ScottDomains.Effective

open ScottDomains.Computable (RecursiveLE)

/-! ## The `DecidablePred` reading is satisfied by every domain -/

/-- **Every domain has an effective presentation**, as `EffectivePresentation`
currently renders the definition.

The enumeration is any surjection `ℕ ↠ K(D)`, which exists because `Domain`
requires `K(D)` countable (`Set.Countable.exists_eq_range`) and `K(D)` is nonempty
(`isCompactElement_bot`). Both decidability conditions are discharged by
`Classical.dec`, which is legitimate for a `DecidablePred` and carries no
computational content.

This is a measurement of the definition, not a theorem about domains: it says the
`DecidablePred` reading of "effectively decidable" makes §3.2's predicate hold of
everything, so every claim of the form "such-and-such an operator preserves the
property of having an effective presentation" is true for free. The
recursion-theoretic strengthening below is what those claims were meant to say. -/
theorem nonempty_effectivePresentation (α : Type*) [CompletePartialOrder α] [Domain α] :
    Nonempty (EffectivePresentation α) := by
  classical
  obtain ⟨f, hf⟩ :=
    (Domain.countable_compacts (α := α)).exists_eq_range ⟨⊥, isCompactElement_bot⟩
  exact ⟨{ enum := f
           enum_mem_compacts := fun n => show f n ∈ compacts α by rw [hf]; exact ⟨n, rfl⟩
           enum_surjective := fun k hk => by
             have hk' : k ∈ Set.range f := by rw [← hf]; exact hk
             exact hk'
           decidableLE := fun _ => Classical.dec _
           decidableNormal := fun _ => Classical.dec _ }⟩

/-! ## The paper's enumeration of `K(D → E)` -/

variable {α β : Type*} [CompletePartialOrder α] [Domain α]
  [CompletePartialOrder β] [Domain β] [BoundedComplete β]

/-- The finite set of compact pairs named by a finite set of index pairs. Each pair
`(i, j)` names the step function `dᵢ ↦ eⱼ`; `ScottHom.ofPairs` takes their join. -/
def pairsOf (d : EffectivePresentation α) (e : EffectivePresentation β)
    (Q : Finset (ℕ × ℕ)) : Set (α × β) :=
  (fun q : ℕ × ℕ => (d.enum q.1, e.enum q.2)) '' (↑Q : Set (ℕ × ℕ))

open Classical in
/-- **The enumeration of `K(D → E)` induced by `d` and `e`.** The `n`-th value is
the join of the step functions named by the `n`-th finite set of index pairs, when
that join is compact, and `⊥` otherwise.

The fallback is not bookkeeping. A finite set of step functions need not be
bounded above; `sSup` on `ScottHom` is total, so `ofPairs` returns a junk value
there. Deciding which case holds is the step Theorem 7's proof sketch calls
"tedious, but not difficult, using the effective presentations of `D` and `E`" —
see `StepFunctionsDecidable`. Here the decision is classical, so the definition is
`noncomputable`. -/
noncomputable def scottHomEnum (d : EffectivePresentation α) (e : EffectivePresentation β)
    (n : ℕ) : ScottHom α β :=
  if IsCompactElement (ScottHom.ofPairs (pairsOf d e (Denumerable.ofNat (Finset (ℕ × ℕ)) n)))
    then ScottHom.ofPairs (pairsOf d e (Denumerable.ofNat (Finset (ℕ × ℕ)) n))
    else ⊥

omit [BoundedComplete β] in
theorem scottHomEnum_isCompactElement (d : EffectivePresentation α)
    (e : EffectivePresentation β) (n : ℕ) : IsCompactElement (scottHomEnum d e n) := by
  classical
  simp only [scottHomEnum]
  split_ifs with h
  · exact h
  · exact isCompactElement_bot

/-- `Denumerable.ofNat` enumerates the finite sets of index pairs onto. Stated
rather than used inline because `Finset (ℕ × ℕ)` carries **two** `Encodable`
instances — `Finset.encodable` and the one derived from `Denumerable.finset`,
which `Mathlib/Logic/Equiv/Finset.lean` warns are different encodings — and
`Denumerable.ofNat_encode` holds only of the second. Letting the lemma supply its
own `encode` avoids picking the wrong instance. -/
theorem surjective_ofNat_finset :
    Function.Surjective (Denumerable.ofNat (Finset (ℕ × ℕ))) :=
  fun Q => ⟨_, Denumerable.ofNat_encode Q⟩

omit [BoundedComplete β] in
/-- The defining equation of `scottHomEnum` at an index naming `Q`, with the
compactness test discharged. -/
theorem scottHomEnum_of_ofNat (d : EffectivePresentation α) (e : EffectivePresentation β)
    {n : ℕ} {Q : Finset (ℕ × ℕ)} (hQ : Denumerable.ofNat (Finset (ℕ × ℕ)) n = Q)
    (h : IsCompactElement (ScottHom.ofPairs (pairsOf d e Q))) :
    scottHomEnum d e n = ScottHom.ofPairs (pairsOf d e Q) := by
  classical
  simp only [scottHomEnum, hQ]
  exact if_pos h

/-- **The enumeration exhausts `K(D → E)`.** This is where
`ScottHom.exists_ofPairs_of_isCompactElement` — every compact function is a finite
join of step functions with compact data — is spent: it produces the finite set of
compact pairs, and surjectivity of `d` and `e` pulls each pair back to a pair of
indices. The pullback is a choice on a finite set, so its image is finite and names
a `Finset (ℕ × ℕ)`. -/
theorem exists_scottHomEnum_eq (d : EffectivePresentation α) (e : EffectivePresentation β)
    {g : ScottHom α β} (hg : IsCompactElement g) : ∃ n, scottHomEnum d e n = g := by
  classical
  obtain ⟨P, hfin, hsub, hgP⟩ := ScottHom.exists_ofPairs_of_isCompactElement hg
  have hchoice : ∀ p ∈ P, ∃ q : ℕ × ℕ, (d.enum q.1, e.enum q.2) = p := by
    intro p hp
    obtain ⟨i, hi⟩ := d.enum_surjective p.1 (hsub hp).1
    obtain ⟨j, hj⟩ := e.enum_surjective p.2 (hsub hp).2
    exact ⟨(i, j), by rw [hi, hj]⟩
  choose! φ hφ using hchoice
  have hpairs : pairsOf d e (hfin.image φ).toFinset = P := by
    rw [pairsOf, Set.Finite.coe_toFinset]
    ext p
    constructor
    · rintro ⟨_, ⟨p', hp', rfl⟩, rfl⟩
      show (d.enum (φ p').1, e.enum (φ p').2) ∈ P
      rw [hφ p' hp']
      exact hp'
    · intro hp
      exact ⟨φ p, ⟨p, hp, rfl⟩, hφ p hp⟩
  have hcpt : IsCompactElement (ScottHom.ofPairs (pairsOf d e (hfin.image φ).toFinset)) := by
    rw [hpairs, ← hgP]
    exact hg
  obtain ⟨n, hn⟩ := surjective_ofNat_finset (hfin.image φ).toFinset
  exact ⟨n, by rw [scottHomEnum_of_ofNat d e hn hcpt, hpairs, ← hgP]⟩

open Classical in
/-- **An effective presentation of `D → E`, built from those of `D` and `E`.**

The enumeration is the paper's: the `n`-th finite set of index pairs, read as step
functions and joined. The two decidability fields are `Classical.dec`; what they
should be is `StepFunctionsDecidable` below. -/
noncomputable def scottHom (d : EffectivePresentation α) (e : EffectivePresentation β) :
    EffectivePresentation (ScottHom α β) where
  enum := scottHomEnum d e
  enum_mem_compacts := scottHomEnum_isCompactElement d e
  enum_surjective _ hg := exists_scottHomEnum_eq d e hg
  decidableLE _ := Classical.dec _
  decidableNormal _ := Classical.dec _

/-! ## Theorem 7's second and third sentences -/

/-- **Theorem 7, second sentence.** "If `D` and `E` have effective presentations,
then `D → E` has an effective presentation as well."

Proved by `scottHom`, whose enumeration is the step-function enumeration the proof
sketch names. The hypotheses `d` and `e` are genuinely used: they supply the
indices the enumeration runs over and the surjectivity that makes it exhaust
`K(D → E)`. What they do not supply is the two decision procedures — see
`Theorem7ArrowRecursive`. -/
theorem theorem7_arrow (d : EffectivePresentation α) (e : EffectivePresentation β) :
    Nonempty (EffectivePresentation (ScottHom α β)) :=
  ⟨scottHom d e⟩

omit [BoundedComplete β] in
/-- **Theorem 7, third sentence, for `⊸`.** "Similar facts hold for `D ⊸ E`."

The paper's reason is that "the strict step functions form a basis" for `D ⊸ E`.
This development has no strict-step-function basis; what it has is
`PRepFun.strictHomDomain`, which makes `D ⊸ E` a domain by injecting
`K(D ⊸ E)` into `K(D → E)`. So the presentation here comes from
`nonempty_effectivePresentation` and the arguments `d` and `e` are **unused** —
recorded as a hypothesis-strength gap rather than hidden by dropping them from the
statement. The statement is the paper's; the proof is weaker than the paper's.

The `[Domain (StrictHom α β)]` binder is not an extra hypothesis: it is what
`PRepFun.strictHomDomain` supplies, and the `example` below discharges it. It has
to be a binder because the *statement* mentions `EffectivePresentation (StrictHom
α β)`, whose elaboration needs the instance before any tactic runs. -/
theorem theorem7_strict [Domain (StrictHom α β)] (_d : EffectivePresentation α)
    (_e : EffectivePresentation β) :
    Nonempty (EffectivePresentation (StrictHom α β)) :=
  nonempty_effectivePresentation _

/-- `theorem7_strict`'s instance binder is dischargeable from the hypotheses
Theorem 7 actually states. -/
example : Domain (StrictHom α β) := PRepFun.strictHomDomain

omit [BoundedComplete β] in
/-- **§3.2's closing claim**: "all of these operators preserve the property of
having an effective presentation."

`γ` stands for the value at `α` and `β` of any operator of §§4–7 — `×`, `+`, `⊕`,
`⊗`, `→`, `⊸`, the powerdomains — for which the development has a `Domain`
instance. The claim holds, and `d` and `e` are unused: that is the whole content
of `nonempty_effectivePresentation`. The version of this claim that is not
vacuous is `PreservesRecursivePresentation`. -/
theorem operator_preserves_effectivePresentation {γ : Type*} [CompletePartialOrder γ]
    [Domain γ] (_d : EffectivePresentation α) (_e : EffectivePresentation β) :
    Nonempty (EffectivePresentation γ) :=
  nonempty_effectivePresentation γ

/-! ## The recursion-theoretic strengthening — stated, open -/

/-- Condition 2 of §3.2 read recursion-theoretically: the finite normal subposets
of the basis are recognized by a total recursive function of the *index* of the
finite index set.

The index is needed because the condition quantifies over `u : Finset ℕ` and
Mathlib v4.32.2 has no `Primcodable (Finset ℕ)` instance, so `ComputablePred`
cannot be asked of a predicate on `Finset ℕ` at all. `Denumerable (Finset ℕ)`
names each `u` by a natural, which is what §3.2's "for any finite set `u ⊆ ℕ`"
means operationally.

The companion for condition 1 is `ScottDomains.Computable.RecursiveLE`, defined in
`ComputableFunction.lean` (r0031); it is reused rather than restated. -/
def RecursiveNormal {γ : Type*} [CompletePartialOrder γ] [Domain γ]
    (d : EffectivePresentation γ) : Prop :=
  ComputablePred fun n : ℕ =>
    (d.enum '' (↑(Denumerable.ofNat (Finset ℕ) n) : Set ℕ)) ◁ compacts γ

/-- `d` is an effective presentation in the paper's intended sense: both conditions
are decided by a total recursive function. This is strictly stronger than the
`EffectivePresentation` structure, whose two `Decidable` fields may be
`Classical.dec` — see `nonempty_effectivePresentation`. -/
def IsRecursive {γ : Type*} [CompletePartialOrder γ] [Domain γ]
    (d : EffectivePresentation γ) : Prop :=
  RecursiveLE d ∧ RecursiveNormal d

/-- **§3.2's notion, as a structure**: an enumeration of the basis whose two
conditions are decided by *total recursive* functions rather than by arbitrary
`Decidable` instances.

This exists because `EffectivePresentation` alone is vacuous.
`nonempty_effectivePresentation` shows **every** domain has one — `Domain`
already supplies a countable nonempty `K(D)`, and `Classical.dec` supplies both
`Decidable` fields — so the structure as written adds nothing to `Domain`, and a
theorem taking an `EffectivePresentation` hypothesis is not asking for what the
paper asks for. A term of `RecursivePresentation` is.

**Why this extends rather than replaces.** Promoting `recursiveLE` to a field of
`EffectivePresentation` itself was the obvious move and it does not work: it
would leave `Effective.powersetPresentation` unconstructible. That instance's
`RecursiveLE` reduces to `Computable fun p : ℕ × ℕ => p.1 ||| p.2`, and
**Mathlib has no bitwise computability at all** — `Mathlib/Computability/`
mentions no `Nat.bitwise`, and there is no `Primrec` route through `binaryRec`.
Replacing the structure would therefore delete the development's only instance,
along with the six `decide`-closed examples in `Effective/Powerset.lean` that
demonstrate its conditions are genuinely computed rather than classical.
Extending keeps both and still makes the distinction a type.

**Deliberately uninstantiated.** No `RecursivePresentation` exists yet, and that
is the honest state: constructing one at `P N` is exactly the missing
computability fact above. Recording it as an empty type rather than pretending
otherwise is the point — the whole reason this structure exists is that an
unfalsifiable class had been standing in for a substantive one. -/
structure RecursivePresentation (γ : Type*) [CompletePartialOrder γ] [Domain γ]
    extends EffectivePresentation γ where
  /-- Condition 1 decided by a total recursive function. -/
  recursiveLE : RecursiveLE toEffectivePresentation
  /-- Condition 2 decided by a total recursive function. -/
  recursiveNormal : RecursiveNormal toEffectivePresentation

/-- The structure delivers the predicate. -/
theorem RecursivePresentation.isRecursive {γ : Type*} [CompletePartialOrder γ]
    [Domain γ] (d : RecursivePresentation γ) : IsRecursive d.toEffectivePresentation :=
  ⟨d.recursiveLE, d.recursiveNormal⟩

/-- …and the predicate builds the structure, so the two readings are
interchangeable and no result has to be stated twice. -/
def RecursivePresentation.ofIsRecursive {γ : Type*} [CompletePartialOrder γ]
    [Domain γ] (d : EffectivePresentation γ) (h : IsRecursive d) :
    RecursivePresentation γ :=
  { d with recursiveLE := h.1, recursiveNormal := h.2 }

/-- **Theorem 7's proof sentence**, printed p. 12: "The proof that the poset of
step functions has decidable ordering and finite normal subposets is tedious, but
not difficult, using the effective presentations of `D` and `E`."

Against `scottHom`'s enumeration — which *is* the step-function enumeration — that
sentence says exactly that the constructed presentation is recursive. Open: the
`decidableLE` and `decidableNormal` fields of `scottHom` are `Classical.dec`, and
promoting them needs the two obstructions named in the module docstring. -/
def StepFunctionsDecidable (d : EffectivePresentation α)
    (e : EffectivePresentation β) : Prop :=
  IsRecursive (scottHom d e)

/-- Theorem 7's proof sentence implies its second sentence at recursion-theoretic
strength, at fixed `d` and `e`. This is the paper's own proof structure: once the
step-function poset is shown to have decidable ordering and recognizable finite
normal subposets, the theorem is that presentation. -/
theorem exists_isRecursive_of_stepFunctionsDecidable {d : EffectivePresentation α}
    {e : EffectivePresentation β} (h : StepFunctionsDecidable d e) :
    ∃ f : EffectivePresentation (ScottHom α β), IsRecursive f :=
  ⟨scottHom d e, h⟩

/-- **Theorem 7's second sentence at the paper's intended strength**, quantified as
the paper states it. Open; `exists_isRecursive_of_stepFunctionsDecidable` reduces
it to `StepFunctionsDecidable`. -/
def Theorem7ArrowRecursive : Prop :=
  ∀ {α β : Type*} [CompletePartialOrder α] [Domain α] [CompletePartialOrder β]
    [Domain β] [BoundedComplete β] (d : EffectivePresentation α)
    (e : EffectivePresentation β), IsRecursive d → IsRecursive e →
      ∃ f : EffectivePresentation (ScottHom α β), IsRecursive f

/-- **Theorem 7's third sentence at the same strength**, for `D ⊸ E`. Open, and
for a further reason than the arrow's: the paper's argument is that "the strict
step functions form a basis", and this development has no strict-step-function
basis to enumerate — `PRepFun.strictHomDomain` gets `K(D ⊸ E)` countable by
injection into `K(D → E)`, which names no enumeration.

The `[Domain (StrictHom α β)]` binder is discharged at any use site by
`PRepFun.strictHomDomain`, which is a theorem rather than an instance so that it
fires only where it is named. -/
def Theorem7StrictRecursive : Prop :=
  ∀ {α β : Type*} [CompletePartialOrder α] [Domain α] [CompletePartialOrder β]
    [Domain β] [BoundedComplete β] [Domain (StrictHom α β)]
    (d : EffectivePresentation α) (e : EffectivePresentation β),
    IsRecursive d → IsRecursive e →
      ∃ f : EffectivePresentation (StrictHom α β), IsRecursive f

/-- **§3.2's closing claim at recursion-theoretic strength**, as a schema with one
instance per operator: the operator's value `γ` at `α` and `β` carries a recursive
presentation whenever `α` and `β` do.

`Theorem7ArrowRecursive` is this schema's instance at `γ = D → E`, universally
quantified. Every operator of §§4–7 supplies another instance; none is discharged.
This is the widest of the §3.2 gaps — it is the claim that carries effective
presentability across the rest of the chapter. -/
def PreservesRecursivePresentation (γ : Type*) [CompletePartialOrder γ] [Domain γ]
    (d : EffectivePresentation α) (e : EffectivePresentation β) : Prop :=
  IsRecursive d → IsRecursive e → ∃ f : EffectivePresentation γ, IsRecursive f

end ScottDomains.Effective
