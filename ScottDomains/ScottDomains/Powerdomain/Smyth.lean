import ScottDomains.IdealCompletion
import ScottDomains.Powerset

/-!
# The Smyth (upper) powerdomain `D♯`

Gunter & Scott, *Semantic Domains* (Handbook of Theoretical Computer Science
Vol. B, 1990), §5.2, quoted from the source PDF rather than paraphrased:

> For any set `S`, we let `Pf(S)` be the set of finite non-empty subsets of `S`.
> We write `Pf⁻(S)` for the set of all finite subsets (including the empty set).
> Given a poset `⟨A, ⊑⟩`, define a pre-ordering `⊢♯` on `Pf(A)` as follows,
>
> > `u ⊢♯ v` if and only if `(∀x ∈ u)(∃y ∈ v). x ⊒ y`.
>
> Dually, define a pre-ordering `⊢♭` on `Pf(A)` by
>
> > `u ⊢♭ v` if and only if `(∀y ∈ v)(∃x ∈ u). x ⊒ y`.
>
> And define `⊢♮` on `Pf(A)` by `u ⊢♮ v` if and only if `u ⊢♯ v` and `u ⊢♭ v`.
>
> If `D` is a domain, then let `D♮` be the domain of ideals over
> `⟨Pf(K(D)), ⊢♮⟩`. We call `D♮` the convex powerdomain of `D`. Similarly, define
> `D♯` and `D♭` to be the domains of ideals over `⟨Pf(K(D)), ⊢♯⟩` and
> `⟨Pf(K(D)), ⊢♭⟩` respectively. We call `D♯` the upper powerdomain of `D` and
> `D♭` the lower powerdomain of `D`.

This file builds `D♯`, the upper powerdomain, also called the **Smyth
powerdomain** after Smyth [Smy78] — the paper names him in §5.1.

## Orientation of `⊢♯`

The paper's `⊢` runs opposite to Mathlib's `≤`: *it is conventional to think of
the relation `a ⊢ b` as indicating that `a` is "larger" than `b`*. So the paper's
`u ⊢♯ v` is Mathlib's `v ≤ u`. Substituting and renaming turns

> `u ⊢♯ v` iff `(∀x ∈ u)(∃y ∈ v). x ⊒ y`

into

> `u ≤ v` iff `(∀b ∈ v)(∃a ∈ u). a ≤ b`,

which is `Smyth.finsetLE` below: **`u ≤ v` when every element of `v` is above
some element of `u`.** `IdealCompletion.lean` records the same reversal for
Theorem 11, and every statement here uses Mathlib's orientation throughout.

Reading the definition informationally: moving up in `≤` means *discarding*
possible outcomes, and every outcome that survives is at least as defined as one
that was already there. That is the total-correctness reading the paper gives
`D♯` in §5.1.

## `Pf` is the *non-empty* finite subsets, and that settles the empty set

The paper defines `Pf(S)` as the finite **non-empty** subsets and uses `Pf(K(D))`
for all three powerdomains; the empty set lives in the separate `Pf⁻(S)`. So the
carrier here is `Basis D`, a `Finset ↥(compacts D)` bundled with a proof that it
is nonempty, and the empty set is not a point of the pre-order at all.

The exclusion is not cosmetic, and this is where the three powerdomains genuinely
differ. Over `Pf⁻` the Smyth order makes `∅` a **top**, not a bottom
(`finsetLE_empty`: `u ≤ ∅` holds vacuously for every `u`, while
`not_finsetLE_empty` shows `∅ ≤ {⊥}` fails), which is the exact opposite of the
Hoare order, where `∅` is the least element. So `OrderBot` for Smyth cannot be
`∅` however the carrier is chosen. It is instead `{⊥}` — `bot_eq_singleton_bot`
below — and it is a least element for a reason that has to be supplied: `⊥` is
compact (`isCompactElement_bot`), so `{⊥}` is a legal point of `Pf(K(D))`.

## What is built

Theorem 11 (`IdealCompletion.instDomain`) supplies everything once the pre-order
is in place, so the content of this file is the pre-order, its three instances,
and the transport:

* `Smyth.finsetLE` — the relation, with `Preorder`, `OrderBot`, `Countable` on
  `Smyth.Basis D`;
* `Smyth.Powerdomain D` — `D♯`, the ideals over `⟨Pf(K(D)), ⊢♯⟩`;
* `Smyth.powerdomain_isDomain` — `D♯` is a domain and `K(D♯)` is the set of
  principal ideals.

`Basis D` is a `structure`, not a type synonym for `{u : Finset _ // u.Nonempty}`:
the subtype already carries `Subtype.preorder` over `Finset`'s `⊆`, and a second
`Preorder` on the same type is an incoherence. `Powerdomain D` is by contrast an
`abbrev` — nothing competes for instances on `IdealCompletion (Basis D)`, so
reducibility is what makes Theorem 11's `CompletePartialOrder`, `IsAlgebraic` and
`Domain` instances apply without restating them.
-/

namespace ScottDomains.Smyth

universe u

/-! ### The Smyth relation on finite sets

Stated for an arbitrary pre-order `α`, since nothing about it needs `α` to be
`K(D)`. The empty-set lemmas are stated here, on bare `Finset α`, because `∅` is
excluded from the carrier `Basis D` and so cannot be spoken about there. -/

section Rel

variable {α : Type u} [Preorder α]

/-- The paper's `⊢♯` in Mathlib's orientation: `u ≤ v` when every element of `v`
is above some element of `u`. See the module docstring for the reversal. -/
def finsetLE (u v : Finset α) : Prop := ∀ b ∈ v, ∃ a ∈ u, a ≤ b

theorem finsetLE_refl (u : Finset α) : finsetLE u u := fun b hb => ⟨b, hb, le_rfl⟩

theorem finsetLE_trans {u v w : Finset α} (huv : finsetLE u v) (hvw : finsetLE v w) :
    finsetLE u w := by
  intro c hc
  obtain ⟨b, hb, hbc⟩ := hvw c hc
  obtain ⟨a, ha, hab⟩ := huv b hb
  exact ⟨a, ha, hab.trans hbc⟩

/-- `∅` is a **top** for the Smyth relation: there is no element of `∅` to place a
lower bound under, so the condition is vacuous. This is why the empty set cannot
serve as the bottom of `D♯`, and it is the opposite of its role in the Hoare
order. -/
theorem finsetLE_empty (u : Finset α) : finsetLE u (∅ : Finset α) := by
  intro b hb
  exact absurd hb (Finset.notMem_empty b)

/-- `∅` is not below a nonempty set: witness the failure at any `b ∈ v`, where the
required `a ∈ ∅` does not exist. Together with `finsetLE_empty` this pins `∅` as a
top and not a bottom, unconditionally — no nontriviality hypothesis on `α`. -/
theorem not_finsetLE_empty {v : Finset α} (hv : v.Nonempty) :
    ¬ finsetLE (∅ : Finset α) v := by
  intro h
  obtain ⟨b, hb⟩ := hv
  obtain ⟨a, ha, -⟩ := h b hb
  exact absurd ha (Finset.notMem_empty a)

/-- A least element of the Smyth relation: `{⊥}` sits below everything, since `⊥`
is a lower bound of every element. -/
theorem singleton_bot_finsetLE [OrderBot α] (u : Finset α) :
    finsetLE ({⊥} : Finset α) u :=
  fun _ _ => ⟨⊥, Finset.mem_singleton_self ⊥, bot_le⟩

end Rel

/-! ### `Pf(K(D))` as a pre-order -/

variable {D : Type u} [CompletePartialOrder D]

/-- `Pf(K(D))`, the paper's finite **non-empty** subsets of the basis `K(D)`.

A `structure` rather than `{u : Finset ↥(compacts D) // u.Nonempty}`: the subtype
inherits `Subtype.preorder` over `Finset`'s `⊆`, and the Smyth pre-order is a
different relation on the same carrier. -/
structure Basis (D : Type u) [CompletePartialOrder D] : Type u where
  /-- The underlying finite set of compact elements. -/
  toFinset : Finset ↥(compacts D)
  /-- The paper's `Pf` excludes the empty set. -/
  nonempty' : toFinset.Nonempty

namespace Basis

@[ext] theorem ext {u v : Basis D} (h : u.toFinset = v.toFinset) : u = v := by
  cases u; cases v; cases h; rfl

theorem toFinset_injective : Function.Injective (Basis.toFinset (D := D)) :=
  fun _ _ h => ext h

/-- The Smyth pre-order on `Pf(K(D))`. Reflexivity and transitivity are
`finsetLE_refl` and `finsetLE_trans`; antisymmetry fails, which is exactly why
Theorem 11 is stated for a *pre-order* — see `exists_le_le_ne`. -/
instance instPreorder : Preorder (Basis D) where
  le u v := finsetLE u.toFinset v.toFinset
  le_refl u := finsetLE_refl u.toFinset
  le_trans _ _ _ := finsetLE_trans

theorem le_def {u v : Basis D} : u ≤ v ↔ ∀ b ∈ v.toFinset, ∃ a ∈ u.toFinset, a ≤ b :=
  Iff.rfl

/-- The least element of `⟨Pf(K(D)), ⊢♯⟩` is `{⊥}`, not `∅`.

Two facts are spent, and both are specific to the upper ordering. `⊥` is a
compact element of `D` (`isCompactElement_bot`, via the `OrderBot ↥(compacts D)`
instance of `IdealCompletion.lean`), so `{⊥}` is a point of `Pf(K(D))`; and it is
nonempty, which the carrier requires. The paper's Theorem 11 hypothesis — *there
is an element `⊥ ∈ A` such that `x ⊢ ⊥` for each `x ∈ A`* — is discharged here. -/
instance instOrderBot : OrderBot (Basis D) where
  bot := ⟨{⊥}, Finset.singleton_nonempty ⊥⟩
  bot_le u := singleton_bot_finsetLE u.toFinset

@[simp] theorem bot_toFinset : (⊥ : Basis D).toFinset = {(⊥ : ↥(compacts D))} := rfl

theorem bot_eq_singleton_bot : (⊥ : Basis D) = ⟨{⊥}, Finset.singleton_nonempty ⊥⟩ := rfl

/-- `Pf(K(D))` is countable when `D` is a domain — this is the countability half
of `Domain D`, which is exactly what Theorem 11 asks of the pre-order it
completes. The injection is `toFinset` into `Finset ↥(compacts D)`, countable
because `K(D)` is. -/
instance instCountable [Domain D] : Countable (Basis D) :=
  toFinset_injective.countable

/-- The singleton `{k}`, the image of a compact element in `Pf(K(D))`. -/
def singleton (k : ↥(compacts D)) : Basis D := ⟨{k}, Finset.singleton_nonempty k⟩

@[simp] theorem singleton_toFinset (k : ↥(compacts D)) :
    (singleton k).toFinset = {k} := rfl

/-- The singleton map is an order **embedding**, not a reversal: `{a} ⊑ {b}` iff
`a ⊑ b`. This is the check that the orientation of `finsetLE` was transcribed the
right way round — had `⊢♯` been read as Mathlib's `≤` directly, this iff would
have come out reversed. -/
@[simp] theorem singleton_le_singleton {a b : ↥(compacts D)} :
    singleton a ≤ singleton b ↔ a ≤ b := by
  constructor
  · intro h
    obtain ⟨c, hc, hcb⟩ := h b (Finset.mem_singleton_self b)
    rw [singleton_toFinset, Finset.mem_singleton] at hc
    exact hc ▸ hcb
  · intro h b hb
    rw [singleton_toFinset, Finset.mem_singleton] at hb
    exact ⟨a, Finset.mem_singleton_self a, hb ▸ h⟩

open Classical in
/-- The Smyth order is a genuine pre-order and not a poset: any two distinct
comparable compacts `a ⊑ b` give `{a}` and `{a, b}` equivalent but unequal, since
`b` is covered by `a` on the left and by itself on the right. The paper makes the
same observation for `⊢♭` in its computation of `(N⊥)♭`. -/
theorem exists_le_le_ne {a b : ↥(compacts D)} (hab : a ≤ b) (hne : a ≠ b) :
    ∃ u v : Basis D, u ≤ v ∧ v ≤ u ∧ u ≠ v := by
  refine ⟨singleton a, ⟨{a, b}, ⟨a, Finset.mem_insert_self a {b}⟩⟩, ?_, ?_, ?_⟩
  · intro c hc
    rcases Finset.mem_insert.mp hc with rfl | hc
    · exact ⟨c, Finset.mem_singleton_self c, le_rfl⟩
    · rw [Finset.mem_singleton] at hc
      exact ⟨a, Finset.mem_singleton_self a, hc ▸ hab⟩
  · intro c hc
    rw [singleton_toFinset, Finset.mem_singleton] at hc
    exact ⟨a, Finset.mem_insert_self a {b}, hc ▸ le_rfl⟩
  · intro h
    have hb : b ∈ (singleton a).toFinset := by
      rw [h]
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self b)
    rw [singleton_toFinset, Finset.mem_singleton] at hb
    exact hne hb.symm

end Basis

/-! ### `D♯`, the upper powerdomain -/

/-- **`D♯`, the Smyth (upper) powerdomain of `D`**: the domain of ideals over the
pre-order `⟨Pf(K(D)), ⊢♯⟩` (Gunter & Scott §5.2).

An `abbrev`, so Theorem 11's `PartialOrder`, `OrderBot`, `SupSet`,
`CompletePartialOrder` and `IsAlgebraic` instances on `IdealCompletion` apply
here without restatement. Nothing else claims instances on
`IdealCompletion (Basis D)`, so no incoherence is possible — unlike the type
synonym `IdealCompletion` itself, which exists precisely to keep two `SupSet`s
apart. -/
abbrev Powerdomain (D : Type u) [CompletePartialOrder D] : Type u :=
  IdealCompletion (Basis D)

/-- The unit `η : K(D) → D♯`, sending a compact element to the principal ideal of
its singleton — the one-point "set of outcomes". -/
def unit (k : ↥(compacts D)) : Powerdomain D :=
  IdealCompletion.principal (Basis.singleton k)

theorem unit_mono : Monotone (unit : ↥(compacts D) → Powerdomain D) :=
  fun _ _ h => IdealCompletion.principal_mono (Basis.singleton_le_singleton.mpr h)

/-- `D♯` is a domain, by Theorem 11: `⟨Pf(K(D)), ⊢♯⟩` is a countable pre-order
with least element `{⊥}`. -/
instance instDomain [Domain D] : Domain (Powerdomain D) :=
  IdealCompletion.instDomain

/-- `K(D♯)` is the set of principal ideals over `⟨Pf(K(D)), ⊢♯⟩` — the second half
of Theorem 11's conclusion, read off at no cost. -/
theorem compacts_eq_range_principal :
    compacts (Powerdomain D) =
      Set.range (IdealCompletion.principal : Basis D → Powerdomain D) :=
  IdealCompletion.compacts_eq_range_principal (A := Basis D)

/-- **The Smyth powerdomain is a domain.** Both conjuncts are Theorem 11 applied
to `⟨Pf(K(D)), ⊢♯⟩`; the work of this file is the three instances that make the
hypotheses hold — `Preorder` from `finsetLE_refl`/`finsetLE_trans`, `OrderBot`
from compactness of `⊥`, and `Countable` from `Domain.countable_compacts`. -/
theorem powerdomain_isDomain (D : Type u) [CompletePartialOrder D] [Domain D] :
    Domain (Powerdomain D) ∧
      compacts (Powerdomain D) =
        Set.range (IdealCompletion.principal : Basis D → Powerdomain D) :=
  ⟨inferInstance, compacts_eq_range_principal⟩

/-! ### A concrete witness

`Set ℕ` is a domain with a nontrivial basis — its compacts are the finite subsets
(`Powerset.lean`) — so `(P N)♯` exercises the construction on an order in which
`K(D)` is a proper part, not the degenerate case where every element is compact. -/

example : Domain (Powerdomain (Set ℕ)) := inferInstance

noncomputable example : CompletePartialOrder (Powerdomain (Set ℕ)) := inferInstance

end ScottDomains.Smyth

/- Axiom audit, by `#print axioms` (run, then removed so the build emits no
`info` lines). Every declaration depends only on the three standard axioms; none
depends on `sorryAx`.

  ScottDomains.Smyth.powerdomain_isDomain            [propext, Classical.choice, Quot.sound]
  ScottDomains.Smyth.compacts_eq_range_principal     [propext, Classical.choice, Quot.sound]
  ScottDomains.Smyth.instDomain                      [propext, Classical.choice, Quot.sound]
  ScottDomains.Smyth.Basis.instCountable             [propext, Classical.choice, Quot.sound]
  ScottDomains.Smyth.Basis.exists_le_le_ne           [propext, Classical.choice, Quot.sound]
  ScottDomains.Smyth.Basis.instPreorder              [propext, Quot.sound]
  ScottDomains.Smyth.Basis.instOrderBot              [propext, Quot.sound]
  ScottDomains.Smyth.Basis.singleton_le_singleton    [propext, Quot.sound]
  ScottDomains.Smyth.finsetLE_empty                  [propext, Quot.sound]
  ScottDomains.Smyth.not_finsetLE_empty              [propext, Quot.sound]
  ScottDomains.Smyth.singleton_bot_finsetLE          [propext, Quot.sound]
  ScottDomains.Smyth.unit_mono                       [propext, Quot.sound]

The pre-order itself is choice-free: `finsetLE` is a first-order condition and
its refl/trans proofs are direct. `Classical.choice` enters only downstream —
through `IdealCompletion`'s `dite` on the undecidable `Order.IsIdeal`, through
`Countable ↥(compacts D)` (`Set.Countable.to_subtype`), and through the
`open Classical` that gives `Finset` insert a `DecidableEq` in
`exists_le_le_ne`. -/
