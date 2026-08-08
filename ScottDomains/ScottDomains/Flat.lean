import ScottDomains.Domain
-- `Set.countable_univ`, for `K(X⊥)` countable once `X⊥` is.
import Mathlib.Data.Set.Countable

/-!
# The flat cpo `X⊥`

Gunter & Scott, *Semantic Domains* (Handbook of Theoretical Computer Science
Vol. B, 1990), §2.1, quoted from the source PDF rather than paraphrased:

> Given any set `S`, we may form a cpo `S⊥` by adding a new element `⊥` to `S`
> and taking the ordering in which `x ⊑ y` if and only if `x = ⊥` or `x = y`.
> Such a cpo is said to be **flat**.

The paper's two running instances of the construction are `N⊥` (§2.1 onward: the
flat naturals, the meaning of a partial function from `N` to `N`) and `T` (the
three-point cpo of truth values `{⊥, true, false}`, §6's opening
counterexample). Both are named at the end of this file.

## Why a new type and not `WithBot X`

`WithBot X` adjoins a bottom, which is half the construction, but it takes the
order on `X` as given: `WithBot ℕ` and `WithBot Bool` carry `ℕ`'s and `Bool`'s
**linear** orders, under which `↑0 ≤ ↑1`. The flat order is the *discrete* order
on `X` with a bottom adjoined, and Mathlib has no discrete-order type synonym to
feed `WithBot`. Declaring `LE X := Eq` locally would be a second, non-defeq `LE`
instance on `ℕ` — the incoherence `IdealCompletion` and `Hoare.Pf` were made
synonyms to avoid.

So `Flat X` is an `inductive` with its own two constructors. That is the cheapest
option that (a) cannot pick up an unwanted instance from `Option X` or `X`, and
(b) gives the two-case recursor every proof below runs on. `ScottDomains.Lift`
(`WithBot` as a cpo, §4.4's `D⊥`) is a *different* operator — it lifts a cpo and
keeps its order — and the two do not overlap: `Lift` needs
`[CompletePartialOrder X]`, `Flat` needs nothing on `X` at all.

## What this file establishes

* `Flat.instPartialOrder`, `Flat.instOrderBot` — the order `x ⊑ y ↔ x = ⊥ ∨ x = y`.
* `Flat.instCompletePartialOrder` — a directed set in a flat cpo has a *greatest*
  element, so its least upper bound is that element; the case split in `flatSup`
  is on whether any non-`⊥` element is present.
* `Flat.isCompactElement` — **every** element of a flat cpo is compact, hence
  `Flat.compacts_eq_univ`: `K(X⊥) = X⊥`. This is the sentence §5.2 opens its
  `(N⊥)♭` computation with, and it is what makes the powerdomain calculations of
  `Flat/Powerdomain.lean` finite combinatorics on `Pf(N⊥)` rather than on a
  proper subset of it.
* `Flat.instDomain` for `[Countable X]` and `Flat.instBoundedComplete`
  unconditionally.
* A **non-degeneracy witness**: `Flat Bool` is the paper's `T`, and
  `Flat.Truth.forall_eq`, `Flat.bot_lt_up`, `Flat.not_up_le_up` pin it as a
  genuine three-point poset with an incomparable pair — not a chain, and not a
  one-point order that would satisfy every class in `Domain.lean` vacuously.
-/

namespace ScottDomains

universe u

/-- The **flat cpo** `X⊥` over a set `X`: the elements of `X`, pairwise
incomparable, with a new least element adjoined (Gunter & Scott §2.1). -/
inductive Flat (X : Type u) : Type u where
  /-- The adjoined least element. -/
  | bot : Flat X
  /-- An element of `X`, read into `X⊥`. -/
  | up (x : X) : Flat X
  deriving DecidableEq

namespace Flat

variable {X : Type u}

/-! ### The order -/

/-- The flat order: `x ⊑ y` iff `x = ⊥` or `x = y`. Written as a match rather
than that disjunction so each of the three cases reduces definitionally. -/
protected def le : Flat X → Flat X → Prop
  | .bot, _ => True
  | .up _, .bot => False
  | .up a, .up b => a = b

instance instLE : LE (Flat X) := ⟨Flat.le⟩

@[simp] theorem bot_le' (y : Flat X) : (Flat.bot : Flat X) ≤ y := trivial

@[simp] theorem not_up_le_bot {a : X} : ¬ (up a : Flat X) ≤ Flat.bot := id

@[simp] theorem up_le_up_iff {a b : X} : (up a : Flat X) ≤ up b ↔ a = b := Iff.rfl

/-- The disjunctive reading of the order, which is the paper's own sentence. -/
theorem le_iff {x y : Flat X} : x ≤ y ↔ x = Flat.bot ∨ x = y := by
  cases x with
  | bot => simp
  | up a =>
    cases y with
    | bot => simp
    | up b => simp [up_le_up_iff, Flat.up.injEq]

instance instPartialOrder : PartialOrder (Flat X) where
  le := (· ≤ ·)
  le_refl x := by cases x with
    | bot => trivial
    | up a => rfl
  le_trans x y z hxy hyz := by
    cases x with
    | bot => trivial
    | up a =>
      cases y with
      | bot => exact absurd hxy not_up_le_bot
      | up b =>
        cases z with
        | bot => exact absurd hyz not_up_le_bot
        | up c => exact (up_le_up_iff.mp hxy).trans (up_le_up_iff.mp hyz)
  le_antisymm x y hxy hyx := by
    cases x with
    | bot =>
      cases y with
      | bot => rfl
      | up b => exact absurd hyx not_up_le_bot
    | up a =>
      cases y with
      | bot => exact absurd hxy not_up_le_bot
      | up b => exact congrArg up (up_le_up_iff.mp hxy)

instance instOrderBot : OrderBot (Flat X) where
  bot := Flat.bot
  bot_le := bot_le'

@[simp] theorem bot_eq : (Flat.bot : Flat X) = ⊥ := rfl

@[simp] theorem up_ne_bot {a : X} : (up a : Flat X) ≠ ⊥ := fun h =>
  not_up_le_bot (le_of_eq h)

theorem bot_lt_up (a : X) : (⊥ : Flat X) < up a :=
  lt_of_le_of_ne bot_le (fun h => up_ne_bot h.symm)

/-- Distinct points of `X` are **incomparable** in `X⊥`. This is the whole
difference between `Flat X` and `WithBot X`, and it is why the construction could
not be `WithBot` over `ℕ` or `Bool`. -/
theorem not_up_le_up {a b : X} (h : a ≠ b) : ¬ (up a : Flat X) ≤ up b :=
  fun hle => h (up_le_up_iff.mp hle)

/-- An element above a non-`⊥` element is that element. Used four times below,
each time to collapse a directedness or upper-bound witness. -/
theorem eq_of_up_le {a : X} {y : Flat X} (h : (up a : Flat X) ≤ y) : y = up a := by
  cases y with
  | bot => exact absurd h not_up_le_bot
  | up b => exact congrArg up (up_le_up_iff.mp h).symm

/-! ### Countability -/

/-- `X⊥` read into `Option X`. Not the *definition* of `Flat X` — see the module
docstring — but an injection, which is all countability needs. -/
def toOption : Flat X → Option X
  | .bot => none
  | .up x => some x

theorem toOption_injective : Function.Injective (toOption : Flat X → Option X) := by
  intro x y h
  cases x with
  | bot => cases y with
    | bot => rfl
    | up b => exact absurd h (by simp [toOption])
  | up a => cases y with
    | bot => exact absurd h (by simp [toOption])
    | up b => exact congrArg up (Option.some_injective X h)

instance instCountable [Countable X] : Countable (Flat X) :=
  toOption_injective.countable

/-! ### The cpo structure

A directed subset of a flat cpo has a **greatest** element: two non-`⊥` members
have an upper bound in the set, and by `eq_of_up_le` that bound is each of them,
so the non-`⊥` members coincide. `flatSup` therefore only has to decide whether
any non-`⊥` member is present. As with `ScottHom`, `WithBot` and `Smash`,
`SupSet` totality forces the case split; on a directed set the branch taken is
always the correct one. -/

open Classical in
/-- Suprema in `X⊥`: the unique non-`⊥` element when the set has one, and `⊥`
otherwise. -/
noncomputable def flatSup (s : Set (Flat X)) : Flat X :=
  if h : ∃ x : X, up x ∈ s then up h.choose else ⊥

theorem flatSup_of_exists {s : Set (Flat X)} (h : ∃ x : X, up x ∈ s) :
    flatSup s = up h.choose := by
  classical simp only [flatSup, dif_pos h]

theorem flatSup_of_not_exists {s : Set (Flat X)} (h : ¬ ∃ x : X, up x ∈ s) :
    flatSup s = ⊥ := by
  classical simp only [flatSup, dif_neg h]

/-- Every member of a set with no non-`⊥` member is `⊥`; so `⊥` is an upper bound
of such a set. -/
theorem upperBounds_of_not_exists {s : Set (Flat X)} (h : ¬ ∃ x : X, up x ∈ s) :
    (⊥ : Flat X) ∈ upperBounds s := by
  intro a ha
  cases a with
  | bot => exact le_rfl
  | up x => exact absurd ⟨x, ha⟩ h

/-- **`X⊥` is a cpo.** The positive branch is where directedness is spent: the
chosen `up c ∈ s` is an *upper* bound of `s`, because any other `up d ∈ s` and it
have a common bound in `s`, and in a flat order a common bound of two non-`⊥`
elements forces them equal. -/
noncomputable instance instCompletePartialOrder : CompletePartialOrder (Flat X) :=
  { (inferInstance : PartialOrder (Flat X)),
    (inferInstance : OrderBot (Flat X)) with
    sSup := flatSup
    lubOfDirected := fun s hs => by
      by_cases h : ∃ x : X, up x ∈ s
      · rw [flatSup_of_exists h]
        have hc : (up h.choose : Flat X) ∈ s := h.choose_spec
        refine ⟨fun a ha => ?_, fun v hv => hv hc⟩
        cases a with
        | bot => exact bot_le
        | up d =>
          obtain ⟨e, he, hde, hce⟩ := hs _ ha _ hc
          rw [eq_of_up_le hce] at hde
          exact hde
      · rw [flatSup_of_not_exists h]
        exact ⟨upperBounds_of_not_exists h, fun _ _ => bot_le⟩ }

/-! ### `K(X⊥) = X⊥`

The paper states this in passing at the head of its `(N⊥)♭` computation (§5.2,
printed p. 26): *"Since `K(N⊥) = N⊥`, the lower powerdomain of `N⊥` is the set of
ideals over the pre-order `⟨P*f(N⊥), ⊢♭⟩`."* It holds of every flat cpo, so it is
proved here once. -/

/-- **Every element of a flat cpo is compact.** If `up c ⊑ ⨆s` then `s` must have
a non-`⊥` member — otherwise `⊥` bounds `s` and leastness would put `up c` below
`⊥` — and that member is `up c` itself. -/
theorem isCompactElement (a : Flat X) : IsCompactElement a := by
  intro s u hne hd hlub hau
  cases a with
  | bot =>
    obtain ⟨w, hw⟩ := hne
    exact ⟨w, hw, bot_le⟩
  | up c =>
    by_cases h : ∃ x : X, up x ∈ s
    · obtain ⟨e, he⟩ := h
      have h1 : e = c := by
        have := hlub.1 he
        rw [eq_of_up_le hau] at this
        exact up_le_up_iff.mp this
      exact ⟨up e, he, by rw [h1]⟩
    · exact absurd (hau.trans (hlub.2 (upperBounds_of_not_exists h))) not_up_le_bot

/-- `K(X⊥) = X⊥`, in set form — the sentence §5.2 opens with. -/
theorem compacts_eq_univ : compacts (Flat X) = Set.univ :=
  Set.eq_univ_of_forall isCompactElement

/-- A flat cpo is algebraic, by `isAlgebraic_of_forall_isCompactElement` — whose
docstring already anticipated this case. -/
instance instIsAlgebraic : IsAlgebraic (Flat X) :=
  isAlgebraic_of_forall_isCompactElement isCompactElement

/-- **`X⊥` is a domain when `X` is countable.** Countability of the basis is
countability of the whole cpo, since the basis is everything. -/
instance instDomain [Countable X] : Domain (Flat X) where
  __ := instIsAlgebraic
  countable_compacts := by
    rw [compacts_eq_univ]
    exact Set.countable_univ

/-- **`X⊥` is bounded complete.** A set bounded above by `⊥` sits inside `{⊥}`;
a set bounded above by `up c` has `up c` as least upper bound when `up c` is in
it, and `⊥` otherwise. No countability, and no condition on `X`. -/
instance instBoundedComplete : BoundedComplete (Flat X) where
  isLUB_sSup_of_bddAbove s hs := by
    obtain ⟨u, hu⟩ := hs
    by_cases h : ∃ x : X, up x ∈ s
    · rw [show (sSup s : Flat X) = flatSup s from rfl, flatSup_of_exists h]
      have hc : (up h.choose : Flat X) ∈ s := h.choose_spec
      have hueq : u = up h.choose := eq_of_up_le (hu hc)
      exact ⟨fun a ha => by rw [← hueq]; exact hu ha, fun v hv => hv hc⟩
    · rw [show (sSup s : Flat X) = flatSup s from rfl, flatSup_of_not_exists h]
      exact ⟨upperBounds_of_not_exists h, fun _ _ => bot_le⟩

/-! ### The paper's two instances -/

/-- `N⊥`, the flat cpo of natural numbers — the paper's running example from
§2.1 on, and the carrier of every powerdomain computation in §5.2–§5.3. -/
abbrev NatBot : Type := Flat ℕ

/-- `T`, the paper's three-point cpo of truth values `{⊥, true, false}`. It is
`T × T` whose convex powerdomain fails to be bounded complete (§6, printed
p. 29). -/
abbrev Truth : Type := Flat Bool

/-! ### The construction is nondegenerate

Three `Prop`-valued classes (`IsAlgebraic`, `Domain`, `BoundedComplete`) are
satisfied by the one-point order, so instances alone prove nothing about the
order built. `T` is the check: it has three elements, a strict inequality, and an
**incomparable pair** — the last is what distinguishes the flat order from
`WithBot Bool`'s linear one, under which `↑false ≤ ↑true`. -/

example : Domain NatBot := inferInstance

example : BoundedComplete NatBot := inferInstance

noncomputable example : CompletePartialOrder Truth := inferInstance

example : Domain Truth := inferInstance

/-- `T` has exactly the three points the paper names. -/
theorem truth_forall_eq (a : Truth) : a = ⊥ ∨ a = up true ∨ a = up false := by
  cases a with
  | bot => exact Or.inl rfl
  | up b => cases b with
    | true => exact Or.inr (Or.inl rfl)
    | false => exact Or.inr (Or.inr rfl)

/-- The three points are distinct, and the two non-`⊥` ones are **incomparable**:
`T` is not a chain. -/
theorem truth_nondegenerate :
    (⊥ : Truth) < up true ∧ (⊥ : Truth) < up false ∧
      ¬ (up true : Truth) ≤ up false ∧ ¬ (up false : Truth) ≤ up true :=
  ⟨bot_lt_up true, bot_lt_up false, not_up_le_up (by decide), not_up_le_up (by decide)⟩

/-- The basis of `N⊥` is all of it — `K(N⊥) = N⊥`, at the paper's own carrier. -/
example : compacts NatBot = Set.univ := compacts_eq_univ

end Flat

end ScottDomains
