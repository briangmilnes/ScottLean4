/-
  Category Theory in Isabelle/HOL as a Basis for Meta-logical Investigation
  (Lean 4 formalization)

  Faithful to:
    J. Bayer, A. Gonus, C. Benzmüller and D. S. Scott,
    "Category Theory in Isabelle/HOL as a Basis for Meta-logical Investigation",
    2023.

  Source text extracted from:
    DanaScottPapers/Bayer-Gonus-Benzmuller-Scott-2023-Category-Theory-in-Isabelle-HOL.txt

  Auto-generated faithful skeleton.

  This paper builds on the free-logic axiomatization of category theory of
  Benzmüller–Scott (and Tiemens' inverse categories) and develops functors,
  natural transformations and elementary-topos notions.  We encode:

    * the three notions of equality with existence (Definition 1): existing
      identity `≃`, Kleene equality `≂`, and directed equality `≥`;
    * the free-logic category (Scott's axiom system) with the extra axiom that
      `D` strictly contains `E` (an explicit non-existent object);
    * functors (Definition 2);
    * natural transformations, both formulations (Definitions 3 and 4);
    * elementary categorical notions: monomorphism, epimorphism, isomorphism,
      initial and terminal objects (Section 3).

  Core Lean 4 only; no Mathlib.  Self-contained (the free-logic signature is
  re-declared locally).
-/

namespace BayerGonusScott2023

universe u v

/-! ## Free-logic signature and the three equalities (Definition 1) -/

/-- Free-logic categorical signature: existence `E`, `dom`, `cod`, composition. -/
class Category (M : Type u) where
  E    : M → Prop
  dom  : M → M
  cod  : M → M
  comp : M → M → M
  /-- Scott's `S1`–`S6` axioms (Benzmüller–Scott Axiom Set V), phrased with the
      Kleene and existing-identity equalities defined below via their unfoldings. -/
  S1 : ∀ x : M, E (dom x) → E x
  S2 : ∀ y : M, E (cod y) → E y
  S3 : ∀ x y : M, E (comp x y) ↔ (E (dom x) ∧ E (cod y) ∧ dom x = cod y)
  S4 : ∀ x y z : M, (E (comp x (comp y z)) ∨ E (comp (comp x y) z)) →
        comp x (comp y z) = comp (comp x y) z
  S5 : ∀ x : M, (E (comp x (dom x)) ∨ E x) → comp x (dom x) = x
  S6 : ∀ y : M, (E (comp (cod y) y) ∨ E y) → comp (cod y) y = y
  /-- Extra axiom (Section 2.2): `D` is a strict superset of `E` — an explicit
      non-existent object exists. -/
  nonexistent : ∃ x : M, ¬ E x

namespace Category

variable {M : Type u} [Category M]

scoped infixl:70 " ∙ " => Category.comp

/-- Existing identity `x ≃ y ≡ x = y ∧ E x ∧ E y` (Definition 1.1). -/
def ExId (x y : M) : Prop := x = y ∧ E x ∧ E y

/-- Kleene equality `x ≂ y ≡ (E x ∨ E y) → x = y` (Definition 1.2). -/
def KlEq (x y : M) : Prop := (E x ∨ E y) → x = y

/-- Directed equality `x ≥ y ≡ E x → x = y` (Definition 1.3). -/
def DirEq (x y : M) : Prop := E x → x = y

@[inherit_doc] scoped infix:56 " ≂ " => Category.KlEq
@[inherit_doc] scoped infix:56 " ≃≃ " => Category.ExId
@[inherit_doc] scoped infix:56 " ⪰ " => Category.DirEq

/-- Kleene equality is reflexive. -/
theorem KlEq.refl (x : M) : KlEq x x := fun _ => rfl

/-- An identity/object: `x ≂ dom x` and `x ≂ cod x`. -/
def IsObject (x : M) : Prop := KlEq x (dom x) ∧ KlEq x (cod x)

end Category

open Category

/-! ## Functors (Definition 2)

    A functor `F : C → D` between two (free-logic) categories. -/

/-- **Functor** `F : C → D` (Definition 2). -/
structure Functor (C : Type u) (D : Type v) [Category C] [Category D] where
  /-- underlying map on morphisms. -/
  obj : C → D
  /-- (1) `E x → E (F x)` (preserves existence). -/
  presE : ∀ x : C, Category.E x → Category.E (obj x)
  /-- (2) `¬ E x → ¬ E (F x)` (reflects existence). -/
  reflE : ∀ x : C, ¬ Category.E x → ¬ Category.E (obj x)
  /-- (3) `F (dom_C x) ≂ dom_D (F x)`. -/
  presDom : ∀ x : C, Category.KlEq (obj (Category.dom x)) (Category.dom (obj x))
  /-- (4) `F (cod_C x) ≂ cod_D (F x)`. -/
  presCod : ∀ x : C, Category.KlEq (obj (Category.cod x)) (Category.cod (obj x))
  /-- (5) `F (x ·_C y) ≥ F x ·_D F y` (directed equality). -/
  presComp : ∀ x y : C,
    Category.DirEq (obj (Category.comp x y)) (Category.comp (obj x) (obj y))

/-! ## Natural transformations (Definitions 3 and 4) -/

/-- **Natural transformation** `η` between functors `F, G : C → D`
    (Definition 3, the morphism-based formulation). -/
structure NatTrans {C : Type u} {D : Type v} [Category C] [Category D]
    (F G : Functor C D) where
  /-- underlying component map. -/
  eta : C → D
  presE : ∀ x : C, Category.E x → Category.E (eta x)
  reflE : ∀ x : C, ¬ Category.E x → ¬ Category.E (eta x)
  presDom : ∀ x : C, Category.KlEq (Category.dom (eta x)) (Category.dom (F.obj x))
  presCod : ∀ x : C, Category.KlEq (Category.cod (eta x)) (Category.cod (F.obj x))
  /-- naturality: `E (x·y) → η(x) ·_D F(y) ≃ G(x) ·_D η(y)`. -/
  natural : ∀ x y : C, Category.E (Category.comp x y) →
    Category.ExId (Category.comp (eta x) (F.obj y)) (Category.comp (G.obj x) (eta y))

/-- **Natural transformation through identities** (Definition 4): assigns to each
    object `A` a component and satisfies the square
    `G(x) ·_D η(dom x) ≂ η(cod x) ·_D F(x)`. -/
structure NatTransId {C : Type u} {D : Type v} [Category C] [Category D]
    (F G : Functor C D) where
  eta : C → D
  square : ∀ x : C,
    Category.KlEq
      (Category.comp (G.obj x) (eta (Category.dom x)))
      (Category.comp (eta (Category.cod x)) (F.obj x))

/-! ## Section 3.  Elementary categorical notions

    Standard free-logic renderings of monomorphism, epimorphism, isomorphism, and
    initial/terminal objects. -/

/-- **Monomorphism**: left-cancellable. `m ∙ f ≂ m ∙ g → f ≂ g` for existing `f,g`
    with matching (co)domains. -/
def IsMono {M : Type u} [Category M] (m : M) : Prop :=
  ∀ f g : M, Category.E f → Category.E g →
    Category.KlEq (Category.comp m f) (Category.comp m g) → Category.KlEq f g

/-- **Epimorphism**: right-cancellable. -/
def IsEpi {M : Type u} [Category M] (e : M) : Prop :=
  ∀ f g : M, Category.E f → Category.E g →
    Category.KlEq (Category.comp f e) (Category.comp g e) → Category.KlEq f g

/-- **Isomorphism**: a morphism `s` with a two-sided inverse `t`. -/
def IsIso {M : Type u} [Category M] (s : M) : Prop :=
  ∃ t : M, Category.E t ∧
    Category.KlEq (Category.comp s t) (Category.cod s) ∧
    Category.KlEq (Category.comp t s) (Category.dom s)

/-- **Initial object**: an object `i` from which every object has a unique
    morphism. -/
def IsInitial {M : Type u} [Category M] (i : M) : Prop :=
  Category.IsObject i ∧ Category.E i ∧
  ∀ b : M, Category.IsObject b → Category.E b →
    ∃ f : M, (Category.E f ∧
      Category.KlEq (Category.dom f) i ∧ Category.KlEq (Category.cod f) b) ∧
      ∀ g : M, (Category.E g ∧
        Category.KlEq (Category.dom g) i ∧ Category.KlEq (Category.cod g) b) → g = f

/-- **Terminal (final) object**: an object `t` to which every object has a unique
    morphism. -/
def IsTerminal {M : Type u} [Category M] (t : M) : Prop :=
  Category.IsObject t ∧ Category.E t ∧
  ∀ a : M, Category.IsObject a → Category.E a →
    ∃ f : M, (Category.E f ∧
      Category.KlEq (Category.dom f) a ∧ Category.KlEq (Category.cod f) t) ∧
      ∀ g : M, (Category.E g ∧
        Category.KlEq (Category.dom g) a ∧ Category.KlEq (Category.cod g) t) → g = f

end BayerGonusScott2023
