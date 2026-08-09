import ScottDomains.Effective.FunctionSpace
import ScottDomains.Flat

/-!
# r0045, agent1: a `RecursivePresentation` that exists, and what the §3.2 claims
actually say

`Effective/FunctionSpace.lean` introduced `RecursivePresentation` — an
`EffectivePresentation` whose two conditions are decided by *total recursive*
functions rather than by arbitrary `Decidable` instances — and recorded it as
**deliberately uninstantiated**, on the reading that constructing one requires a
computability fact Mathlib does not supply.

This file constructs one, at `N⊥ = Flat ℕ`:

    ScottDomains.R45.Agent1.natBotRecursivePresentation : RecursivePresentation (Flat ℕ)

so the type is inhabited, and the inhabitant's two `ComputablePred` witnesses are
built from `Primrec` combinators — `Classical.dec` cannot supply a `Computable`
conjunct, which is the whole point of the `EffectivePresentation` /
`RecursivePresentation` distinction (`docs/StructuresVsTypeClassesVsPropsInLean4.md`).

## Two measurements that correct `Effective/FunctionSpace.lean`

| # | Claim on record | Measured against Mathlib v4.32.2 |
| -- | --------------- | -------------------------------- |
| 1 | "Mathlib v4.32.2 has no `Primcodable (Finset ℕ)` instance, so `ComputablePred` cannot be asked of a predicate on `Finset ℕ` at all" (`Effective/FunctionSpace.lean`, `RecursiveNormal`'s docstring) | **false.** `Primcodable.ofDenumerable` (`Mathlib/Computability/Primrec/Basic.lean:139`, priority 10) turns any `Denumerable α` into `Primcodable α`, and `Denumerable (Finset α)` is `Mathlib/Logic/Equiv/Finset.lean:109`. `Primrec.ofNat` (`:233`) then makes the decoding `ℕ → Finset ℕ` primitive recursive |
| 2 | "no `RecursivePresentation` exists yet, and that is the honest state" | **superseded by this file**, for `Flat ℕ`. It remains true for `P N`: that one does need bitwise computability, and the grep is confirmed — `bitwise\|lor\|testBit` over `Mathlib/Computability/` is still 0 hits |

Row 1 does not make the *powerset* presentation recursive. `Effective/Powerset.lean`
enumerates `K(P N)` by binary expansion, and its condition 1 reduces to
`Computable fun p : ℕ × ℕ => p.1 ||| p.2`, which is the blocked one. The
obstruction is specific to that enumeration, not to `RecursiveNormal`'s use of
`Finset ℕ`.

## Why a flat cpo is the domain where this is cheap

Two facts make both conditions decidable by arithmetic on indices:

* `K(X⊥) = X⊥` (`Flat.compacts_eq_univ`), so the enumeration is a surjection onto
  the whole type and `natBotEnum` can be the obvious one — `0 ↦ ⊥`, `k+1 ↦ up k`.
* In a flat cpo `↓x` is a chain, so **a subset is normal exactly when it contains
  `⊥`** (`isNormalIn_compacts_flat_iff`). Condition 2 collapses from a
  directedness test to a single membership test, and through the enumeration to
  `0 ∈ u`.

Condition 1 is `a = 0 ∨ a = b` (`natBotEnum_le_iff`), which is `PrimrecPred` by
`Primrec.eq` and `PrimrecPred.or`.

Condition 2 needs one bridge that Mathlib does not state: `RecursiveNormal`
quantifies over `Denumerable.ofNat (Finset ℕ) n`, so `0 ∈ ofNat (Finset ℕ) n` has
to be shown primitive recursive *in `n`*. `Denumerable.finset` decodes `n` to a
list and applies `Denumerable.raise' · 0`, whose values are increasing from the
head, so `0` is a member exactly when the decoded list's head is `0`
(`zero_mem_ofNat_finset_iff`). That is `Primrec.list_head?` composed with
`Primrec.ofNat`.

## What this does and does not settle about agent1's four claims

`PreservesRecursivePresentation γ d e` leaves `γ` unrelated to `α` and `β`, so it
is discharged by **any** `γ` carrying a recursive presentation, whatever `d` and
`e` are — including `γ := α` with `d` itself (`preservesRecursivePresentation_id`,
one line). Both instances below are therefore evidence that the *statement* does
not say what §3.2's closing sentence says; see the r0045 report. They are recorded
here rather than suppressed because the alternative — leaving the schema looking
open when it is trivially satisfiable — is the defect r0044 measured.

`Theorem7ArrowRecursive` gets a **reduction**, not a discharge:
`theorem7ArrowRecursive_of_stepFunctionsDecidable` derives it from the
hypothesis-strengthened step-function claim. `StepFunctionsDecidable` and
`Theorem7StrictRecursive` are untouched and open; the report states why.
-/

namespace ScottDomains.R45.Agent1

open ScottDomains.Effective
open ScottDomains.Computable (RecursiveLE)

/-! ## The decoding `RecursiveNormal` quantifies over

`Denumerable (Finset ℕ)` is `Mathlib/Logic/Equiv/Finset.lean:109`. It decodes `n`
to a list of naturals and turns that list into a strictly increasing one by
`Denumerable.raise'`, which is the only part of the encoding these lemmas need to
see. -/

/-- The decoding, unfolded once. `Denumerable.finset` is built by `Denumerable.mk'`
from an explicit equivalence, so its `decode` is definitionally `some ∘ e.symm`
and `Denumerable.ofNat_of_decode` applies with `rfl`. -/
theorem ofNat_finset_eq (n : ℕ) :
    Denumerable.ofNat (Finset ℕ) n =
      Finset.map (Denumerable.eqv ℕ).symm.toEmbedding
        (Denumerable.raise'Finset (Denumerable.ofNat (List ℕ) n) 0) :=
  Denumerable.ofNat_of_decode rfl

/-- Membership in the decoded `Finset` is membership in the raised list: the
`Finset.map` is along `(Denumerable.eqv ℕ).symm = Denumerable.ofNat ℕ`, which is
the identity on `ℕ` (`Denumerable.ofNat_nat`). -/
theorem mem_ofNat_finset_iff (n x : ℕ) :
    x ∈ Denumerable.ofNat (Finset ℕ) n ↔
      x ∈ Denumerable.raise' (Denumerable.ofNat (List ℕ) n) 0 := by
  rw [ofNat_finset_eq]
  simp [Denumerable.raise'Finset, Denumerable.eqv]

/-- `Denumerable.raise' l n` is bounded below by `n`: its head is `m + n` and the
tail is raised from `m + n + 1`. This is the increasing-sequence fact
(`Denumerable.raise'_sorted`) in the form the membership test needs. -/
theorem le_of_mem_raise' : ∀ (l : List ℕ) (n x : ℕ), x ∈ Denumerable.raise' l n → n ≤ x
  | [], n, x, h => by simp [Denumerable.raise'] at h
  | m :: l, n, x, h => by
    rw [Denumerable.raise', List.mem_cons] at h
    rcases h with rfl | h
    · omega
    · have := le_of_mem_raise' l (m + n + 1) x h
      omega

/-- **`0` is a member of a raised list exactly when the list's head is `0`.**
Every later entry is at least `m + 1` where `m` is the head, so no later entry can
be `0`. -/
theorem zero_mem_raise'_zero_iff (l : List ℕ) :
    (0 : ℕ) ∈ Denumerable.raise' l 0 ↔ l.head? = some 0 := by
  cases l with
  | nil => simp [Denumerable.raise']
  | cons m l =>
    rw [Denumerable.raise', List.mem_cons]
    simp only [List.head?_cons, Option.some.injEq]
    constructor
    · rintro (h | h)
      · omega
      · have := le_of_mem_raise' l (m + 0 + 1) 0 h
        omega
    · rintro rfl
      exact Or.inl rfl

/-- The membership test `RecursiveNormal` needs, as a test on the decoded list. -/
theorem zero_mem_ofNat_finset_iff (n : ℕ) :
    (0 : ℕ) ∈ Denumerable.ofNat (Finset ℕ) n ↔
      (Denumerable.ofNat (List ℕ) n).head? = some 0 :=
  (mem_ofNat_finset_iff n 0).trans (zero_mem_raise'_zero_iff _)

/-- **`fun n => 0 ∈ ofNat (Finset ℕ) n` is primitive recursive.** This is the fact
`Effective/FunctionSpace.lean` recorded as unavailable: `Primcodable (Finset ℕ)`
comes from `Primcodable.ofDenumerable`, and the decoding is primitive recursive by
`Primrec.ofNat`, so the test is `Primrec.list_head?` followed by an equality
test. -/
theorem primrecPred_zero_mem_ofNat_finset :
    PrimrecPred fun n : ℕ => (0 : ℕ) ∈ Denumerable.ofNat (Finset ℕ) n :=
  (PrimrecRel.comp Primrec.eq (Primrec.list_head?.comp (Primrec.ofNat (List ℕ)))
      (Primrec.const (some 0))).of_eq
    fun n => (zero_mem_ofNat_finset_iff n).symm

/-- `Finset ℕ` is `Primcodable`, by `Primcodable.ofDenumerable`. Stated as an
`example` because it is a measurement, not a lemma: the docstring of
`Effective.RecursiveNormal` says this instance does not exist. -/
example : Primcodable (Finset ℕ) := inferInstance

/-- …and a predicate **on `Finset ℕ` itself** can therefore be primitive
recursive, which is the second half of the sentence being corrected. The transfer
is `Primrec.ofNat_iff`: for a denumerable domain, a function is primitive
recursive exactly when its composite with the decoding is. -/
theorem primrecPred_zero_mem_finset : PrimrecPred fun u : Finset ℕ => (0 : ℕ) ∈ u :=
  Primrec.primrecPred (Primrec.ofNat_iff.mpr primrecPred_zero_mem_ofNat_finset.decide)

/-! ## Normal subposets of a flat cpo -/

/-- **In a flat cpo, normal means "contains `⊥`".** `↓x` is `{⊥, x}`, a chain, so
directedness of `N ∩ ↓x` is automatic and the only content of `N ◁ K(X⊥)` is the
nonemptiness conjunct, which by `IsNormalIn.bot_mem` is exactly `⊥ ∈ N`.

This is where condition 2 of §3.2 becomes a membership test rather than a search:
in `P N` the corresponding characterization (`isNormalIn_compacts_set_iff`) needs
closure under binary union as well, because there `↓x` is not a chain. -/
theorem isNormalIn_compacts_flat_iff {X : Type*} {N : Set (Flat X)} :
    N ◁ compacts (Flat X) ↔ (⊥ : Flat X) ∈ N := by
  constructor
  · intro h
    exact h.bot_mem (Flat.isCompactElement (⊥ : Flat X))
  · intro hbot
    refine ⟨fun a _ => Flat.isCompactElement a,
      fun x _ => ⟨⟨⊥, hbot, Set.mem_Iic.mpr bot_le⟩, ?_⟩⟩
    rintro a ⟨haN, hax⟩ b ⟨hbN, hbx⟩
    have hax' : a ≤ x := Set.mem_Iic.mp hax
    have hbx' : b ≤ x := Set.mem_Iic.mp hbx
    rcases Flat.le_iff.mp hax' with h | h
    · exact ⟨b, ⟨hbN, hbx⟩, (le_of_eq h).trans (Flat.bot_le' b), le_rfl⟩
    · exact ⟨a, ⟨haN, hax⟩, le_rfl, hbx'.trans (le_of_eq h.symm)⟩

/-! ## The enumeration of `K(N⊥)` -/

/-- **The enumeration of `K(N⊥) = N⊥`**: index `0` names `⊥`, index `k+1` names
`up k`. `Flat.compacts_eq_univ` makes surjectivity onto the basis surjectivity
onto the type. -/
def natBotEnum : ℕ → Flat ℕ
  | 0 => ⊥
  | (k + 1) => Flat.up k

@[simp] theorem natBotEnum_zero : natBotEnum 0 = ⊥ := rfl

@[simp] theorem natBotEnum_succ (k : ℕ) : natBotEnum (k + 1) = Flat.up k := rfl

theorem natBotEnum_eq_bot_iff {n : ℕ} : natBotEnum n = ⊥ ↔ n = 0 := by
  cases n with
  | zero => simp
  | succ k => simp

theorem natBotEnum_injective : Function.Injective natBotEnum := by
  intro a b h
  cases a with
  | zero =>
    cases b with
    | zero => rfl
    | succ j => simp at h
  | succ i =>
    cases b with
    | zero => simp at h
    | succ j => simpa using h

theorem natBotEnum_surjective (k : Flat ℕ) : ∃ n, natBotEnum n = k := by
  cases k with
  | bot => exact ⟨0, rfl⟩
  | up a => exact ⟨a + 1, rfl⟩

/-- **Condition 1, as arithmetic on indices.** `dₐ ⊑ d_b` exactly when `a = 0`
(the index of `⊥`) or `a = b`, because the flat order is `x ⊑ y ↔ x = ⊥ ∨ x = y`
and the enumeration is injective. -/
theorem natBotEnum_le_iff {a b : ℕ} : natBotEnum a ≤ natBotEnum b ↔ a = 0 ∨ a = b := by
  rw [Flat.le_iff]
  constructor
  · rintro (h | h)
    · exact Or.inl (natBotEnum_eq_bot_iff.mp h)
    · exact Or.inr (natBotEnum_injective h)
  · rintro (rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr rfl

/-- **Condition 2, as a membership test on indices.** A finite index set names a
normal subposet exactly when it contains `0`, the index of `⊥`. -/
theorem isNormalIn_natBotEnum_image_iff (u : Finset ℕ) :
    (natBotEnum '' (↑u : Set ℕ)) ◁ compacts (Flat ℕ) ↔ 0 ∈ u := by
  rw [isNormalIn_compacts_flat_iff]
  constructor
  · rintro ⟨i, hi, hbot⟩
    rw [natBotEnum_eq_bot_iff] at hbot
    rwa [hbot] at hi
  · intro h0
    exact ⟨0, h0, rfl⟩

instance decidableNatBotLE (a b : ℕ) :
    Decidable (natBotEnum a ≤ natBotEnum b) :=
  decidable_of_iff _ natBotEnum_le_iff.symm

instance decidableNatBotNormal (u : Finset ℕ) :
    Decidable ((natBotEnum '' (↑u : Set ℕ)) ◁ compacts (Flat ℕ)) :=
  decidable_of_iff _ (isNormalIn_natBotEnum_image_iff u).symm

/-- **An effective presentation of `N⊥`**, with both `Decidable` fields decided by
the tests above rather than by `Classical.dec` — the second instantiation of
`EffectivePresentation` at a type in this development, after
`Effective.powersetPresentation`.

`noncomputable` records that `Flat.instCompletePartialOrder`'s `sSup` is defined by
a classical case split — it is a fact about the *cpo structure of the carrier*, not
about this presentation's two decision procedures, which are programs. The
`example`s below are the evidence for that distinction: the kernel runs them. -/
noncomputable def natBotPresentation : EffectivePresentation (Flat ℕ) where
  enum := natBotEnum
  enum_mem_compacts n := Flat.isCompactElement (natBotEnum n)
  enum_surjective k _ := natBotEnum_surjective k
  decidableLE p := decidableNatBotLE p.1 p.2
  decidableNormal u := decidableNatBotNormal u

/-! ### The decision procedures run

A `Classical.dec` instance is stuck under kernel reduction, so `decide` closing
these is the check that the two fields are programs — the same check
`Effective/Powerset.lean` runs on `P N`. -/

/-- `d₀ = ⊥ ⊑ d₃ = up 2`. -/
example : natBotEnum 0 ≤ natBotEnum 3 := by decide

/-- `up 1` and `up 2` are incomparable: distinct points of a flat cpo always are. -/
example : ¬ (natBotEnum 2 ≤ natBotEnum 3) := by decide

/-- Condition 2 runs, positively: `{d₀, d₂} = {⊥, up 1}` contains `⊥`. -/
example : (natBotEnum '' (↑({0, 2} : Finset ℕ) : Set ℕ)) ◁ compacts (Flat ℕ) := by decide

/-- Condition 2 runs, negatively: `{d₂} = {up 1}` misses `⊥`, so it is not normal —
Lemma 4.3 decided by a program. -/
example : ¬ ((natBotEnum '' (↑({2} : Finset ℕ) : Set ℕ)) ◁ compacts (Flat ℕ)) := by decide

/-! ## The presentation is recursive -/

/-- **Condition 1 is decided by a total recursive function.** `a = 0 ∨ a = b` is
`PrimrecPred` by `Primrec.eq` twice and `PrimrecPred.or`; `natBotEnum_le_iff`
transports it to the order relation. -/
theorem recursiveLE_natBot : RecursiveLE natBotPresentation := by
  have h : PrimrecPred fun p : ℕ × ℕ => p.1 = 0 ∨ p.1 = p.2 :=
    PrimrecPred.or (PrimrecRel.comp Primrec.eq Primrec.fst (Primrec.const 0))
      (PrimrecRel.comp Primrec.eq Primrec.fst Primrec.snd)
  exact h.computablePred.of_eq fun p => natBotEnum_le_iff.symm

/-- **Condition 2 is decided by a total recursive function**, via the
`Finset`-decoding bridge above. -/
theorem recursiveNormal_natBot : RecursiveNormal natBotPresentation :=
  primrecPred_zero_mem_ofNat_finset.computablePred.of_eq fun n =>
    (isNormalIn_natBotEnum_image_iff (Denumerable.ofNat (Finset ℕ) n)).symm

theorem isRecursive_natBot : IsRecursive natBotPresentation :=
  ⟨recursiveLE_natBot, recursiveNormal_natBot⟩

/-- **`RecursivePresentation` is inhabited.** `N⊥` carries one, so §3.2's
non-vacuous notion — the one `Classical.dec` cannot supply, because
`ComputablePred p` contains a `Computable` conjunct — is not an empty type. -/
noncomputable def natBotRecursivePresentation : RecursivePresentation (Flat ℕ) :=
  RecursivePresentation.ofIsRecursive natBotPresentation isRecursive_natBot

/-! ## What the §3.2 claims say once a recursive presentation exists -/

/-- Any domain carrying a recursive presentation discharges
`PreservesRecursivePresentation` at that domain, for **every** `α`, `β`, `d`, `e`.

The reason is the shape of the definition, not a theorem about operators: `γ` is a
parameter unrelated to `α` and `β`, and the conclusion `∃ f : EffectivePresentation
γ, IsRecursive f` does not mention `d` or `e`. §3.2's sentence is about operators
`(D, E) ↦ F D E`; rendering it with a free `γ` loses the dependence, and this
theorem measures how much is lost. -/
theorem preservesRecursivePresentation_of_isRecursive
    {α β γ : Type*} [CompletePartialOrder α] [Domain α] [CompletePartialOrder β]
    [Domain β] [CompletePartialOrder γ] [Domain γ] {f : EffectivePresentation γ}
    (hf : IsRecursive f) (d : EffectivePresentation α) (e : EffectivePresentation β) :
    PreservesRecursivePresentation γ d e :=
  fun _ _ => ⟨f, hf⟩

/-- The schema at `γ := N⊥`: the constant operator `(D, E) ↦ N⊥` preserves
recursive presentability. True, and true for the uninteresting reason that `N⊥`
has one outright. -/
theorem preservesRecursivePresentation_natBot
    {α β : Type*} [CompletePartialOrder α] [Domain α] [CompletePartialOrder β]
    [Domain β] (d : EffectivePresentation α) (e : EffectivePresentation β) :
    PreservesRecursivePresentation (Flat ℕ) d e :=
  preservesRecursivePresentation_of_isRecursive isRecursive_natBot d e

/-- The schema at `γ := α`: the **identity** operator preserves recursive
presentability, by returning the hypothesis. One line, no content, and no appeal
to `Classical.dec` — so this is not the `EffectivePresentation` vacuity but a
second, independent one, living in the quantifier structure of the statement
rather than in a field type. -/
theorem preservesRecursivePresentation_id
    {α β : Type*} [CompletePartialOrder α] [Domain α] [CompletePartialOrder β]
    [Domain β] (d : EffectivePresentation α) (e : EffectivePresentation β) :
    PreservesRecursivePresentation α d e :=
  fun hd _ => ⟨d, hd⟩

/-- **A reduction of Theorem 7's second sentence, quantified as the paper states
it, to its proof sentence.** `Effective.exists_isRecursive_of_stepFunctionsDecidable`
does this at fixed `d` and `e`; this lifts it to the quantified claim, so
`Theorem7ArrowRecursive` now has a theorem concluding it with **one** hypothesis.

The hypothesis is not `StepFunctionsDecidable` itself but its
hypothesis-strengthened form `IsRecursive d → IsRecursive e →
StepFunctionsDecidable d e`. That is deliberate: `StepFunctionsDecidable d e` as
defined quantifies over *arbitrary* presentations `d` and `e`, while Theorem 7's
proof sentence says "using the effective presentations of `D` and `E`" — see the
r0045 report for why the unstrengthened form cannot be provable. -/
theorem theorem7ArrowRecursive_of_stepFunctionsDecidable.{u, v}
    (h : ∀ {α : Type u} {β : Type v} [CompletePartialOrder α] [Domain α]
      [CompletePartialOrder β] [Domain β] [BoundedComplete β] (d : EffectivePresentation α)
      (e : EffectivePresentation β), IsRecursive d → IsRecursive e →
      StepFunctionsDecidable d e) :
    Theorem7ArrowRecursive.{u, v} := by
  intro α β _ _ _ _ _ d e hd he
  exact exists_isRecursive_of_stepFunctionsDecidable (h d e hd he)

end ScottDomains.R45.Agent1
