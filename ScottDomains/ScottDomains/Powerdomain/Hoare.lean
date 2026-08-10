import ScottDomains.IdealCompletion
-- `Finset.countable`: a `Finset` of a countable type is countable. This is the
-- only reason the module is imported; it is not reachable from `ScottDomains.Domain`.
import Mathlib.Logic.Equiv.List

/-!
# The Hoare (lower) powerdomain `D♭`

Gunter & Scott, *Semantic Domains* (Handbook of Theoretical Computer Science
Vol. B, 1990), §5.2, quoted from the source PDF rather than paraphrased:

> For any set `S`, we let `Pf(S)` be the set of finite non-empty subsets of `S`.
> … Given a poset `⟨A, ⊑⟩`, define a pre-ordering `⊢♯` on `Pf(A)` as follows,
>
> > `u ⊢♯ v` if and only if `(∀x ∈ u)(∃y ∈ v). x ⊒ y`.
>
> Dually, define a pre-ordering `⊢♭` on `Pf(A)` by
>
> > `u ⊢♭ v` if and only if `(∀y ∈ v)(∃x ∈ u). x ⊒ y`.
>
> … If `D` is a domain, then let `D♮` be the domain of ideals over
> `⟨Pf(K(D)), ⊢♮⟩`. … Similarly, define `D♯` and `D♭` to be the domains of ideals
> over `⟨Pf(K(D)), ⊢♯⟩` and `⟨Pf(K(D)), ⊢♭⟩` respectively. We call `D♯` the
> **upper powerdomain** of `D` and `D♭` the **lower powerdomain** of `D`.

`D♭` is also called the **Hoare powerdomain**, after the paper's own remark that
it "corresponds to the partial correctness interpretation of programs" and that
Hoare popularized that study.

This module defines `⟨Pf(K(D)), ⊢♭⟩` and `D♭`; the upper (Smyth) and convex
(Plotkin) orderings are defined elsewhere. Everything here lives in
`ScottDomains.Hoare` so the three constructions cannot collide on a shared name.

## Orientation of `⊢♭` in Mathlib's convention

The paper writes `a ⊢ b` for "`a` is larger than `b`"; Mathlib writes the same
relation as `b ≤ a` (`IdealCompletion.lean` states this and every declaration
below follows it). Transcribing:

    paper:   u ⊢♭ v  ↔  ∀ y ∈ v, ∃ x ∈ u, x ⊒ y
    Mathlib: v ≤  u  ↔  ∀ y ∈ v, ∃ x ∈ u, y ≤ x

and renaming the two bound sets so the smaller one is on the left,

    u ≤ v  ↔  ∀ x ∈ u, ∃ y ∈ v, x ≤ y

which is `Pf.le_def` verbatim: *every element of `u` is below some element of
`v`*. Note that the paper's `⊒` inside the definition is the **poset order of
`A`**, not `⊢♭`; only the outer relation flips.

## What this costs

Nothing beyond Theorem 11. `IdealCompletion.instDomain` (`IdealCompletion.lean`)
turns a `Preorder`, an `OrderBot` and a `Countable` on a pre-order into a
`Domain` on its ideal completion, so the whole content of this file is those
three instances on `Pf ↥(compacts D)`:

* `Preorder` — reflexivity and transitivity of `⊑♭`, two lines each;
* `OrderBot` — the least element is `{⊥}`, using that `⊥` is compact
  (`isCompactElement_bot`, via the `OrderBot ↥(compacts D)` instance);
* `Countable` — `Finset.countable` over `Domain.countable_compacts`.

`Pf A` is a type synonym for `{u : Finset A // u.Nonempty}` rather than that
subtype itself, for the same reason `IdealCompletion` is a synonym for
`Order.Ideal`: the subtype already carries a `PartialOrder` inherited from
`Finset`'s `⊆`, and `⊑♭` is a different — and strictly coarser — relation.
Declaring `⊑♭` on the bare subtype would be a second, non-defeq order instance on
one type.

`Powerdomain` is by contrast an `abbrev`, because here no instance is meant to
differ: `D♭` *is* the ideal completion of `⟨Pf(K(D)), ⊑♭⟩`, and it should inherit
that cpo, that `OrderBot` and that `Domain` unchanged.

## Statements

* `Pf.le_def` — the Hoare ordering.
* `Pf.instPreorder`, `Pf.instOrderBot`, `Pf.instCountable` — the three
  hypotheses of Theorem 11.
* `Pf.not_isPartialOrder` — `⊑♭` really is only a pre-order, which is why
  Theorem 11 is stated for pre-orders and not posets.
* `Powerdomain` — `D♭`, and `thm11_hoare`: it is a domain whose compact elements
  are exactly the principal ideals over `⟨Pf(K(D)), ⊑♭⟩`.
-/

namespace ScottDomains.Hoare

universe u

variable {A : Type u}

/-! ### `Pf(A)`: the finite non-empty subsets

The paper is explicit that `Pf(S)` excludes the empty set (it reserves the barred
`Pf(S)` for "all finite subsets, including the empty set") and it is `Pf`, the
non-empty one, that the three pre-orderings are defined on. The exclusion is not
cosmetic: with `∅` admitted, `∅ ⊑♭ v` holds vacuously for every `v`, so `∅` would
be a second least element below `{⊥}` and the ideal completion would acquire an
extra point at the bottom. -/

/-- `Pf(A)`, the set of **finite non-empty** subsets of `A`, as a type carrying
the Hoare (lower) pre-order of §5.2 rather than `⊆`. See the module docstring for
why this is a synonym and not the bare subtype. -/
def Pf (A : Type u) : Type u := {u : Finset A // u.Nonempty}

namespace Pf

/-- The underlying finite set. -/
def toFinset (u : Pf A) : Finset A := u.1

/-- Read a non-empty `Finset` as a point of `Pf(A)`. -/
def ofFinset (u : Finset A) (h : u.Nonempty) : Pf A := ⟨u, h⟩

@[simp] theorem toFinset_ofFinset (u : Finset A) (h : u.Nonempty) :
    (ofFinset u h).toFinset = u := rfl

theorem toFinset_nonempty (u : Pf A) : u.toFinset.Nonempty := u.2

instance : Membership A (Pf A) := ⟨fun u a => a ∈ u.toFinset⟩

@[simp] theorem mem_def {a : A} {u : Pf A} : a ∈ u ↔ a ∈ u.toFinset := Iff.rfl

/-- Two points of `Pf(A)` are equal exactly when their underlying finite sets
are. -/
@[ext] theorem ext {u v : Pf A} (h : u.toFinset = v.toFinset) : u = v := Subtype.ext h

/-! ### The Hoare (lower) pre-order -/

section Preorder

variable [Preorder A]

/-- The **Hoare (lower) ordering** on `Pf(A)`: `u ⊑♭ v` iff every element of `u`
is below some element of `v`. This is the paper's `v ⊢♭ u`, transcribed into
Mathlib's orientation as the module docstring sets out.

Reflexive because `x` witnesses itself, and transitive by composing the two
witnesses with `le_trans`. It is **not** antisymmetric — see
`not_isPartialOrder` — which is exactly why Theorem 11 completes a *pre-order*. -/
instance instPreorder : Preorder (Pf A) where
  le u v := ∀ x ∈ u, ∃ y ∈ v, x ≤ y
  le_refl u x hx := ⟨x, hx, le_rfl⟩
  le_trans u v w huv hvw x hx := by
    obtain ⟨y, hy, hxy⟩ := huv x hx
    obtain ⟨z, hz, hyz⟩ := hvw y hy
    exact ⟨z, hz, hxy.trans hyz⟩

theorem le_def {u v : Pf A} : u ≤ v ↔ ∀ x ∈ u, ∃ y ∈ v, x ≤ y := Iff.rfl

end Preorder

/-! ### The least element

Theorem 11 asks for an element `⊥` of the pre-order with `x ⊢ ⊥` for every `x` —
in Mathlib's orientation, an `OrderBot`. For `⟨Pf(A), ⊑♭⟩` it is the singleton
`{⊥}`: `{⊥} ⊑♭ v` says only that `⊥` is below *some* element of `v`, and `v` is
non-empty. This is where the non-emptiness clause of `Pf` is spent. -/

section OrderBot

variable [Preorder A] [OrderBot A]

instance instOrderBot : OrderBot (Pf A) where
  bot := ofFinset {⊥} (Finset.singleton_nonempty ⊥)
  bot_le v := le_def.mpr fun x hx => by
    obtain ⟨y, hy⟩ := v.toFinset_nonempty
    refine ⟨y, hy, ?_⟩
    rw [show x = ⊥ from Finset.mem_singleton.mp hx]
    exact bot_le

@[simp] theorem mem_bot {a : A} : a ∈ (⊥ : Pf A) ↔ a = ⊥ := Finset.mem_singleton

end OrderBot

/-! ### Countability -/

/-- `Pf(A)` is countable when `A` is: `Finset.countable` makes `Finset A`
countable and a subtype of a countable type is countable. Applied to
`A = K(D)`, whose countability is `Domain.countable_compacts`, this is the third
hypothesis of Theorem 11. -/
instance instCountable [Countable A] : Countable (Pf A) :=
  inferInstanceAs (Countable {u : Finset A // u.Nonempty})

/-! ### `⊑♭` is a pre-order and not a partial order

Three `Prop`-valued hypotheses discharged by short proofs invite the suspicion
that the relation defined is the wrong one — in particular that it collapses to
`⊆`, under which `Pf` *would* be a poset and the whole appeal to Theorem 11's
pre-order generality would be unnecessary. It does not: in `Pf ℕ` the sets
`{0, 1}` and `{1}` are equivalent under `⊑♭` (each element of either is below
`1`, which lies in both) and distinct. -/

/-- `⊑♭` is not antisymmetric, so `⟨Pf(A), ⊑♭⟩` is a genuine pre-order. The
witness is in `Pf ℕ`. -/
theorem not_isPartialOrder : ∃ u v : Pf ℕ, u ≤ v ∧ v ≤ u ∧ u ≠ v := by
  refine ⟨ofFinset {0, 1} ⟨0, by decide⟩, ofFinset {1} ⟨1, by decide⟩, ?_, ?_, ?_⟩
  · exact le_def.mpr (by decide)
  · exact le_def.mpr (by decide)
  · intro h
    have : ({0, 1} : Finset ℕ) = {1} := congrArg toFinset h
    exact absurd this (by decide)

end Pf

/-! ### The Hoare powerdomain -/

section Powerdomain

variable (D : Type u) [CompletePartialOrder D] [Domain D]

/-- The **Hoare (lower) powerdomain** `D♭` of a domain `D`: the domain of ideals
over the pre-order `⟨Pf(K(D)), ⊢♭⟩` (Gunter & Scott §5.2).

An `abbrev`, not a synonym: `D♭` is meant to carry exactly the cpo, `OrderBot`
and `Domain` structure that `IdealCompletion` gives it, so nothing is gained by
hiding them behind a new name.

The instance arguments are the paper's hypotheses on `D`, spelled out:
`CompletePartialOrder D` and `Domain D` together are its "`D` is a domain", and
the `Domain D` half is load-bearing twice over — `K(D)` must be countable for
`Pf(K(D))` to be countable, and `D` must have a least element for `{⊥}` to be
the least element of `Pf(K(D))`. -/
abbrev Powerdomain : Type u := IdealCompletion (Pf ↥(compacts D))

/-- **Theorem 11 instantiated at the Hoare ordering.** `D♭` is a domain, and its
basis `K(D♭)` is the set of principal ideals over `⟨Pf(K(D)), ⊑♭⟩` — that is,
the sets `↓u = {v ∈ Pf(K(D)) | v ⊑♭ u}` for `u` a finite non-empty set of compact
elements of `D`.

The proof is `IdealCompletion.thm11` applied to `Pf ↥(compacts D)`; the three
instances above are its whole cost. -/
theorem theorem_11_hoare :
    Domain (Powerdomain D) ∧
      compacts (Powerdomain D) =
        Set.range (IdealCompletion.principal : Pf ↥(compacts D) → Powerdomain D) :=
  IdealCompletion.thm11 (Pf ↥(compacts D))

alias thm11_hoare := theorem_11_hoare

omit [Domain D] in
/-- An element of `D♭` is compact exactly when it is a principal ideal
`↓u` for some finite non-empty `u ⊆ K(D)`. The second conjunct of `thm11_hoare`
in membership form. Countability of `K(D)` is not needed for this half — the
characterization of the compact ideals holds over any pre-order with a least
element — so `[Domain D]` is omitted. -/
theorem isCompactElement_iff {I : Powerdomain D} :
    IsCompactElement I ↔ ∃ u : Pf ↥(compacts D), I = IdealCompletion.principal u :=
  IdealCompletion.isCompactElement_iff_exists_eq_principal

end Powerdomain

/-! ### The instances resolve

A `Domain` instance that is never demanded is never checked. `Prop` is the
cheapest domain in the development (`ScottDomains.Domain`), so `Prop♭` forces
typeclass resolution to run the whole chain: `Domain Prop` → `Countable ↥(compacts Prop)`
→ `Countable (Pf ↥(compacts Prop))` → `Domain (IdealCompletion (Pf ↥(compacts Prop)))`. -/

example : Domain (Powerdomain Prop) := inferInstance

-- `noncomputable` because `IdealCompletion`'s `sSup` branches on
-- `Order.IsIdeal`, an undecidable predicate; these two carry data, unlike the
-- `Prop`-valued `Domain` above.
noncomputable example : CompletePartialOrder (Powerdomain Prop) := inferInstance

noncomputable example : OrderBot (Powerdomain Prop) := inferInstance

end ScottDomains.Hoare

/- Axiom audit, by `#print axioms` (run, then removed so the build emits no
`info` lines). Every declaration depends only on the three standard axioms; none
depends on `sorryAx`.

  ScottDomains.Hoare.Pf                            [propext, Quot.sound]
  ScottDomains.Hoare.Pf.ext                        [propext, Quot.sound]
  ScottDomains.Hoare.Pf.instPreorder               [propext, Quot.sound]
  ScottDomains.Hoare.Pf.le_def                     [propext, Quot.sound]
  ScottDomains.Hoare.Pf.instOrderBot               [propext, Quot.sound]
  ScottDomains.Hoare.Pf.mem_bot                    [propext, Quot.sound]
  ScottDomains.Hoare.Pf.instCountable              [propext, Classical.choice, Quot.sound]
  ScottDomains.Hoare.Pf.not_isPartialOrder         [propext, Classical.choice, Quot.sound]
  ScottDomains.Hoare.Powerdomain                   [propext, Quot.sound]
  ScottDomains.Hoare.thm11_hoare                   [propext, Classical.choice, Quot.sound]
  ScottDomains.Hoare.isCompactElement_iff          [propext, Classical.choice, Quot.sound]

The three instances that Theorem 11 consumes split cleanly: `instPreorder` and
`instOrderBot` are choice-free, and `Classical.choice` enters `instCountable`
only through `Denumerable`/`Encodable` machinery behind `Finset.countable`.
`thm11_hoare` inherits choice from `IdealCompletion`'s `sSup`, whose `dite`
branches on the undecidable `Order.IsIdeal`. `not_isPartialOrder`'s use is the
`Finset` decidability instances discharged by `decide`. -/
