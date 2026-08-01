/-
  Categorical Axiomatization of Modeloids (Lean 4 formalization)

  Faithful to:
    L. Tiemens, D. S. Scott, C. Benzmüller and M. Benda,
    "Categorical Axiomatization of Modeloids",
    2019 (arXiv:1902.09443).

  Source text extracted from:
    DanaScottPapers/Tiemens-Scott-Benzmuller-Benda-2019-Categorical-Axiomatization-of-Modeloids.txt

  Auto-generated faithful skeleton.

  The paper generalizes M. Benda's modeloids (certain sets of partial bijections)
  first to inverse-semigroup language and then to inverse categories, using the
  free-logic axiomatization of category theory of Benzmüller–Scott (which this
  module imports and reuses).

  We encode:
    * modeloids as sets of partial bijections closed under composition, inverses,
      restriction, and containing the identity (Definition 2);
    * inverse semigroups (Definition 4) with the idempotent lemma `e ∗ e = e` for
      `e = x ∗ x⁻¹` proved from the axioms;
    * the natural partial order (Definition 6) and semimodeloids (Definition 7);
    * inverse categories over the free-logic category (Definition 10) and the
      categorical modeloid axioms (Definition 13);
    * the derivative operation (Definition 3).

  Core Lean 4 only; no Mathlib.  To keep this file independently compile-checkable
  we re-declare the minimal free-logic category signature (`FreeCat`, existence `E`,
  Kleene equality `≂`) rather than importing the Benzmüller–Scott module.
-/

namespace TiemensScott2019

/-! ## Free-logic category signature (imported concept from Benzmüller–Scott 2016)

    Re-declared locally so this module compiles on its own. -/

/-- Free-logic categorical signature: existence `E`, `dom`, `cod`, composition. -/
class FreeCat (M : Type u) where
  E    : M → Prop
  dom  : M → M
  cod  : M → M
  comp : M → M → M

namespace FreeCat
variable {M : Type u} [FreeCat M]

/-- Kleene equality `x ≂ y ≡ (E x ∨ E y) → x = y`. -/
def KlEq (x y : M) : Prop := (E x ∨ E y) → x = y

@[inherit_doc] scoped infix:56 " ≂ " => FreeCat.KlEq
end FreeCat

/-! ## Section 2.  Modeloids as sets of partial bijections

    We keep the algebra of partial bijections `F(Σ)` abstract: a type `F` with
    composition `∘`, inverse `⁻¹`, an identity, and a "is-a-restriction-of"
    relation `≤` (used for the inclusion property `f|_A`, Definition 2 (3)). -/

/-- Abstract algebra of partial bijections `F(Σ)` (Section 2). -/
class PBijAlg (F : Type u) where
  /-- partial composition `g ∘ f`. -/
  comp : F → F → F
  /-- inverse `f⁻¹`. -/
  inv : F → F
  /-- the identity partial bijection `id_Σ`. -/
  id : F
  /-- `restr g f` means `g` is a restriction of `f` (`g ≤ f`). -/
  restr : F → F → Prop

namespace PBijAlg
@[inherit_doc] scoped infixl:70 " ∘' " => PBijAlg.comp
@[inherit_doc] scoped postfix:max "⁻¹'" => PBijAlg.inv
end PBijAlg

open PBijAlg

/-- **Modeloid** (Definition 2).  `M ⊆ F(Σ)` closed under composition and
    inverses, downward closed under restriction, and containing the identity. -/
structure Modeloid {F : Type u} [PBijAlg F] (M : F → Prop) : Prop where
  /-- (1) closure of composition. -/
  closure_comp : ∀ f g, M f → M g → M (comp f g)
  /-- (2) closure under inverses. -/
  closure_inv : ∀ f, M f → M (inv f)
  /-- (3) inclusion property (`A ⊂ dom f ⇒ f|_A ∈ M`). -/
  inclusion : ∀ f g, M f → restr g f → M g
  /-- (4) identity. -/
  identity : M id

/-- **Derivative** of a modeloid (Definition 3), stated over an abstract
    "one-point extension" relation `ext`: `ext a f g` reads "`g` extends `f` by the
    single pair `(a, ·)`" (domain side); `ext' a f g` is the range side.  Then
    `f ∈ D(M)` iff `f` can be extended by every point of `Sigma` in either
    coordinate.  `Sigma` is the abstract point set. -/
def Derivative {F : Type u} [PBijAlg F] (Sigma : Type v)
    (ext ext' : Sigma → F → F → Prop) (M : F → Prop) (f : F) : Prop :=
  (∀ a : Sigma, ∃ g : F, ext a f g ∧ M g) ∧
  (∀ a : Sigma, ∃ g : F, ext' a f g ∧ M g)

/-! ## Section 3.  Inverse semigroups (Definition 4) -/

/-- An **inverse semigroup** `(S, ⁻¹, ∗)` (Definition 4). -/
class InverseSemigroup (S : Type u) where
  /-- associative binary operation. -/
  op : S → S → S
  /-- unary inverse. -/
  inv : S → S
  /-- (1) associativity. -/
  assoc : ∀ x y z, op (op x y) z = op x (op y z)
  /-- (2) `x ∗ x⁻¹ ∗ x = x`. -/
  invAbsorb : ∀ x, op (op x (inv x)) x = x
  /-- (3) `(x⁻¹)⁻¹ = x`. -/
  invInv : ∀ x, inv (inv x) = x
  /-- (4) idempotents commute: `x x⁻¹ y y⁻¹ = y y⁻¹ x x⁻¹`. -/
  idemComm : ∀ x y,
    op (op (op x (inv x)) y) (inv y) = op (op (op y (inv y)) x) (inv x)

namespace InverseSemigroup

variable {S : Type u} [InverseSemigroup S]

@[inherit_doc] scoped infixl:70 " ∗ " => InverseSemigroup.op

/-- `x ∗ x⁻¹` is idempotent — proved from Definition 4, axioms (1)–(3).
    `(x x⁻¹)(x x⁻¹) = x (x⁻¹ x x⁻¹) = x x⁻¹`, using `(x⁻¹)⁻¹ = x` in `invAbsorb`
    instantiated at `x⁻¹`. -/
theorem invMul_idempotent (x : S) :
    op (op x (inv x)) (op x (inv x)) = op x (inv x) := by
  -- axiom (2) at `x⁻¹`, rewritten by `(x⁻¹)⁻¹ = x`:  x⁻¹ ∗ x ∗ x⁻¹ = x⁻¹
  have hInner : op (op (inv x) x) (inv x) = inv x := by
    have h := invAbsorb (inv x)
    rw [invInv] at h
    exact h
  calc
    op (op x (inv x)) (op x (inv x))
        = op x (op (inv x) (op x (inv x))) := by rw [assoc]
      _ = op x (op (op (inv x) x) (inv x)) := by rw [assoc]
      _ = op x (inv x) := by rw [hInner]

/-- **Natural partial order** (Definition 6): `s ≤ t ⇔ s = t ∗ e` for some
    idempotent `e`. -/
def le (s t : S) : Prop := ∃ e : S, op e e = e ∧ s = op t e

end InverseSemigroup

/-! ### Semimodeloids (Definition 7)

    Over an inverse monoid with neutral element `e` and zero element `0`. -/

/-- **Semimodeloid** (Definition 7): `M` in an inverse monoid, closed under `∗`,
    inverses, downward closed under the natural partial order, containing the
    neutral element. -/
structure Semimodeloid {S : Type u} [InverseSemigroup S] (neutral : S)
    (M : S → Prop) : Prop where
  /-- (1) `x, y ∈ M ⇒ x ∗ y ∈ M`. -/
  closure_op : ∀ x y, M x → M y → M (InverseSemigroup.op x y)
  /-- (2) `x ∈ M ⇒ x⁻¹ ∈ M`. -/
  closure_inv : ∀ x, M x → M (InverseSemigroup.inv x)
  /-- (3) `x ≤ y, y ∈ M ⇒ x ∈ M`. -/
  downward : ∀ x y, InverseSemigroup.le x y → M y → M x
  /-- (4) the neutral (identity) element is in `M`. -/
  neutral_mem : M neutral

/-! ## Section 4.  Inverse categories and categorical modeloids

    We extend the free-logic category with a generalized inverse.  Kleene
    equality `≂` and existence `E` come from the `FreeCat` signature above. -/

/-- An **inverse category** (Definition 10): a free-logic category with a unary
    inverse `inv` such that `s ≂ s · ŝ · s` and `ŝ ≂ ŝ · s · ŝ` (Kleene equality). -/
class InverseCategory (M : Type u) extends FreeCat M where
  /-- the generalized inverse `ŝ` of a morphism `s`. -/
  invM : M → M
  /-- `s ≂ s · ŝ · s`. -/
  inv1 : ∀ s : M, FreeCat.KlEq s (FreeCat.comp (FreeCat.comp s (invM s)) s)
  /-- `ŝ ≂ ŝ · s · ŝ`. -/
  inv2 : ∀ s : M, FreeCat.KlEq (invM s) (FreeCat.comp (FreeCat.comp (invM s) s) (invM s))

/-- **Idempotence** in a small category (Definition 11): `e · e ≂ e`. -/
def Idempotent {M : Type u} [FreeCat M] (e : M) : Prop :=
  FreeCat.KlEq (FreeCat.comp e e) e

/-- **Categorical modeloid** (Definition 13): `M ⊆ C` on an inverse category with
    all zero elements, closed under composition and inverses, downward closed
    under the categorical natural partial order `le`, and containing every object.

    `le` and `IsObject` are supplied abstractly (Definitions 12 and the object
    notion `X ≂ dom X ≂ cod X`). -/
structure CategoricalModeloid {M : Type u} [InverseCategory M]
    (le : M → M → Prop) (IsObject : M → Prop) (Mem : M → Prop) : Prop where
  /-- (1) `a, b ∈ M ⇒ a · b ∈ M`. -/
  closure_comp : ∀ a b, Mem a → Mem b → Mem (FreeCat.comp a b)
  /-- (2) `a ∈ M ⇒ a⁻¹ ∈ M`. -/
  closure_inv : ∀ a, Mem a → Mem (InverseCategory.invM a)
  /-- (3) `a ≤ b, b ∈ M ⇒ a ∈ M`. -/
  downward : ∀ a b, le a b → Mem b → Mem a
  /-- (4) every object is in `M`. -/
  objects_mem : ∀ X, IsObject X → Mem X

end TiemensScott2019
