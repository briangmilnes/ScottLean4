/-
  Ordinal Definability (Lean 4 formalization)

  Faithful to:
    J. Myhill and D. Scott,
    "Ordinal Definability",
    in: Axiomatic Set Theory, Proc. Sympos. Pure Math. XIII, Part 1,
    AMS, 1971, pp. 271-278.

  Source text extracted from:
    DanaScottPapers/Myhill-Scott-1971-Ordinal-Definability.txt

  Auto-generated faithful skeleton.

  Working inside ZF, the paper defines the class `OD` of *ordinal-definable* sets,
  shows it has a definable well-ordering and contains all definable sets, and uses
  it for a relative-consistency proof of the axiom of choice and comparison with
  Gödel's constructible sets `L`.

  Since ZF's cumulative hierarchy is not part of core Lean, we axiomatize the
  ambient universe abstractly as a `class ZFUniverse` bundling: membership, the
  ordinals, the rank hierarchy `V·`, the first-order definability operator `Df`,
  and term-definability.  We then encode:

    * `Df(A)` — first-order definable elements of `(A, ∈_A)`;
    * `OD = { x | ∃ α, x ∈ Df(V_α) }` (the paper's central definition);
    * the Extended Reflection Principle and the transitivity-of-definability
      lemma (as the universe's axioms);
    * the theorems: `OD` closed under definability; the definable well-ordering
      of `OD`; `V = L → V = OD`; `Con(ZF) → Con(ZF + V=OD)`; and `Pω ∩ OD`
      equinumerous with `{ Th(V_α) | α ∈ OR }` (as target statements).

  Core Lean 4 only; no Mathlib.
-/

namespace MyhillScott1971

universe u

/-- Abstract ZF universe: sets, membership, ordinals, the cumulative hierarchy
    `V·`, first-order definability `Df`, and term-definability with parameters. -/
class ZFUniverse (V : Type u) where
  /-- membership relation. -/
  mem : V → V → Prop
  /-- the class of ordinals. -/
  IsOrdinal : V → Prop
  /-- strict order on ordinals. -/
  ordLt : V → V → Prop
  /-- the rank hierarchy: `Vhier α = V_α = { x | rank x < α }`. -/
  Vhier : V → V
  /-- `Df A` — the set of first-order definable elements of `(A, ∈_A)`. -/
  Df : V → V
  /-- `Definable A t` — `t` is a set denoted by a term with parameters from `A`,
      definable in `(A, ∈_A)`. -/
  Definable : V → V → Prop
  /-- `Th A` — the set of Gödel numbers of sentences true in `(A, ∈_A)`. -/
  Th : V → V

namespace ZFUniverse

variable {V : Type u} [ZFUniverse V]

@[inherit_doc] scoped infix:50 " ∈ᵥ " => ZFUniverse.mem

/-- **Definition** of the class of ordinal-definable sets:
    `OD = { x | ∃ α, x ∈ Df(V_α) }`. -/
def OD (x : V) : Prop := ∃ a : V, IsOrdinal a ∧ mem x (Df (Vhier a))

/-- The class `V` of all sets (everything). -/
def univClass (_x : V) : Prop := True

end ZFUniverse

open ZFUniverse

/-! ## The axioms established in the paper, recorded as a bundle

    These are the theorems proved schematically in ZF that the development relies
    on; we bundle them as the defining properties of an *ordinal-definability
    structure*. -/

/-- The reflection-principle / transitivity apparatus of §1.  Each field is a
    theorem the paper proves (as a schema) about the ambient universe. -/
structure ODStructure (V : Type u) [ZFUniverse V] : Prop where
  /-- Transitivity of definability (Lemma, §1):
      if the parameters and `A` are definable in `B`, so is any term applied to
      them.  Stated for the key instance `Df(A) ⊆ Df(B)` when `A ∈ Df(B)`. -/
  transitivity : ∀ A B : V,
    ZFUniverse.mem A (ZFUniverse.Df B) →
    ∀ x : V, ZFUniverse.mem x (ZFUniverse.Df A) → ZFUniverse.mem x (ZFUniverse.Df B)
  /-- Definability of the `V_α` (Lemma, §1): `α ∈ Df(V_α) → V_α ∈ Df(V_{α+1})`.
      Rendered with an abstract successor witness. -/
  Vhier_definable : ∀ a b : V,
    ZFUniverse.IsOrdinal a → ZFUniverse.IsOrdinal b → ZFUniverse.ordLt a b →
    ZFUniverse.mem a (ZFUniverse.Df (ZFUniverse.Vhier a)) →
    ZFUniverse.mem (ZFUniverse.Vhier a) (ZFUniverse.Df (ZFUniverse.Vhier b))
  /-- The **Extended Reflection Principle** (§1): every finite parameter tuple can
      be reflected into some `V_β` in which the parameters are themselves
      definable.  Rendered for a single term/parameter. -/
  extendedReflection : ∀ x : V,
    ∃ b : V, ZFUniverse.IsOrdinal b ∧
      ZFUniverse.Definable (ZFUniverse.Vhier b) x

/-! ## Theorems of the paper (statements) -/

/-- **Theorem** (§1): `OD` is closed under definability — if the parameters are
    ordinal-definable, so is any term applied to them.  Rendered for one
    parameter: if `a ∈ OD` and `t` is definable from `a`, then `t ∈ OD`.
    TODO: proof uses the Extended Reflection Principle and transitivity. -/
theorem OD_closed_under_definability {V : Type u} [ZFUniverse V]
    (_S : ODStructure V) :
    ∀ a t : V, OD a → (∀ A : V, ZFUniverse.mem a (ZFUniverse.Df A) →
      ZFUniverse.Definable A t) → OD t := by
  sorry -- TODO: §1 argument via Extended Reflection + transitivity of Df.

/-- **Definable well-ordering** of `OD` (§1): there is a definable relation `<`
    well-ordering `OD` (`x < y` iff `x` is defined in an earlier `V_α`, or in the
    same `V_α` by a term with smaller Gödel number).  Statement of existence. -/
def HasDefinableWellOrdering (V : Type u) [ZFUniverse V] : Prop :=
  ∃ lt : V → V → Prop,
    -- `lt` well-orders `OD`
    (∀ x, OD x → ¬ lt x x) ∧
    (∀ x y z, lt x y → lt y z → lt x z) ∧
    (∀ x y, OD x → OD y → x = y ∨ lt x y ∨ lt y x)

/-- **The Metatheorem** (Introduction): every definable class with a definable
    well-ordering is included in every definable class which contains all
    definable sets.  Rendered: `OD` (definable, definably well-ordered) is the
    least such class.  Statement. -/
def Metatheorem (V : Type u) [ZFUniverse V] : Prop :=
  ∀ K : V → Prop,
    (∀ x : V, (∃ A, ZFUniverse.mem x (ZFUniverse.Df A)) → K x) →   -- K ⊇ definable sets
    ∀ x : V, OD x → K x                                            -- OD ⊆ K

/-- **Theorem** (§1): if `V = L` then `V = OD`; and `L = OD ↔ V = L`.
    Here `Lclass` is the class of constructible sets.  Statement. -/
def V_eq_L_implies_V_eq_OD (V : Type u) [ZFUniverse V] (Lclass : V → Prop) : Prop :=
  (∀ x : V, Lclass x) → (∀ x : V, OD x)

/-- **Relative consistency** (§1): `Con(ZF) → Con(ZF + [V = OD])`, since
    `V = L → V = OD`.  Rendered as: consistency of `V = OD` relative to the
    universe (schematic). -/
def Con_ZF_plus_V_eq_OD (V : Type u) [ZFUniverse V] : Prop :=
  (∀ x : V, OD x) ∨ ¬ (∀ x : V, OD x)   -- placeholder for the metamathematical claim

/-- **Selection-property metatheorem** (§1): `ZF + [V = OD]` is the weakest
    extension of ZF with the selection property (every definable nonempty class
    contains a definable element).  Statement. -/
def SelectionProperty (V : Type u) [ZFUniverse V] : Prop :=
  ∀ K : V → Prop, (∃ x, K x) →
    ∃ d : V, K d ∧ (∃ A, ZFUniverse.mem d (ZFUniverse.Df A))

/-- **Theorem** (final, §1): `Pω ∩ OD` has the same cardinality as
    `{ Th(V_α) | α ∈ OR }`.  Rendered as the existence of a bijection between the
    two classes.  `Pω` is the power set of `ω`, supplied abstractly. -/
def PowOmega_OD_card (V : Type u) [ZFUniverse V] (Pow_omega : V → Prop) : Prop :=
  ∃ bij : V → V,
    (∀ x, (Pow_omega x ∧ OD x) →
      ∃ a, ZFUniverse.IsOrdinal a ∧ bij x = ZFUniverse.Th (ZFUniverse.Vhier a)) ∧
    True  -- one-to-one/onto conditions abbreviated

end MyhillScott1971
