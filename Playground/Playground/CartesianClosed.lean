import Mathlib.Tactic

/-!
# A category, and a cartesian closed category specializing it

A small, self-contained development (not Mathlib's `CategoryTheory`), written to
be *read*. We define:

1. `Category` — objects, hom-types, identities, composition, and the three laws.
2. `CartesianClosed` — a class **extending** `Category` with a terminal object,
   binary products, and exponentials (function objects), each given by its
   universal property.

`Type` is exhibited as an instance of both: it is the prototype cartesian closed
category (`Set` in Lambek–Scott), where the exponential `B^A` is the function type
`A → B`, `eval` is application, and `curry` is λ-abstraction. That last line is the
Curry–Howard–Lambek correspondence made concrete: the currying isomorphism
`Hom (Z × A) B ≃ Hom Z (B^A)` *is* the typing rule `Γ, x:A ⊢ t:B  ⟺  Γ ⊢ λx.t : A ⇒ B`.

Composition is written **diagrammatically**: `comp f g` (`f ⨟ g`) is "`f` then `g`",
matching Mathlib's `≫`.
-/

namespace Playground.CCC

universe u v

/-- A (locally small) category. `comp f g` is "first `f`, then `g`". -/
class Category (Obj : Type u) where
  /-- Morphisms from `X` to `Y`. -/
  Hom : Obj → Obj → Type v
  /-- The identity morphism on `X`. -/
  id : (X : Obj) → Hom X X
  /-- Diagrammatic composition: `comp f g` is `f` followed by `g`. -/
  comp : {X Y Z : Obj} → Hom X Y → Hom Y Z → Hom X Z
  /-- Left identity law. -/
  id_comp : ∀ {X Y : Obj} (f : Hom X Y), comp (id X) f = f
  /-- Right identity law. -/
  comp_id : ∀ {X Y : Obj} (f : Hom X Y), comp f (id Y) = f
  /-- Associativity of composition. -/
  assoc : ∀ {W X Y Z : Obj} (f : Hom W X) (g : Hom X Y) (h : Hom Y Z),
            comp (comp f g) h = comp f (comp g h)

namespace Category
@[inherit_doc] scoped infixr:60 " ⨟ " => Category.comp
end Category

/-- **`Type` is a category**: objects are types, morphisms are functions, identity
is `fun x => x`, composition is function composition. All three laws hold by `rfl`. -/
instance : Category (Type u) where
  Hom X Y := X → Y
  id _ := fun x => x
  comp f g := fun x => g (f x)
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-- A **cartesian closed category**: a `Category` with a terminal object, binary
products, and exponentials, each specified by its universal property. -/
class CartesianClosed (Obj : Type u) extends Category Obj where
  -- ### Terminal object
  /-- The terminal object `⊤`. -/
  term : Obj
  /-- The unique morphism into `⊤`. -/
  toTerm : (X : Obj) → Hom X term
  /-- Uniqueness: any morphism into `⊤` is `toTerm`. -/
  toTerm_unique : ∀ {X : Obj} (f : Hom X term), f = toTerm X
  -- ### Binary products
  /-- The product object `X × Y`. -/
  prod : Obj → Obj → Obj
  /-- First projection. -/
  fst : {X Y : Obj} → Hom (prod X Y) X
  /-- Second projection. -/
  snd : {X Y : Obj} → Hom (prod X Y) Y
  /-- The mediating morphism `⟨f, g⟩ : Z → X × Y`. -/
  pair : {Z X Y : Obj} → Hom Z X → Hom Z Y → Hom Z (prod X Y)
  /-- `⟨f, g⟩` followed by `fst` is `f`. -/
  pair_fst : ∀ {Z X Y : Obj} (f : Hom Z X) (g : Hom Z Y), comp (pair f g) fst = f
  /-- `⟨f, g⟩` followed by `snd` is `g`. -/
  pair_snd : ∀ {Z X Y : Obj} (f : Hom Z X) (g : Hom Z Y), comp (pair f g) snd = g
  /-- Uniqueness of the mediating morphism (product η). -/
  pair_unique : ∀ {Z X Y : Obj} (h : Hom Z (prod X Y)),
                  pair (comp h fst) (comp h snd) = h
  -- ### Exponentials (function objects)
  /-- The exponential object `B^A` (a.k.a. the internal hom `A ⇒ B`). -/
  exp : Obj → Obj → Obj
  /-- Evaluation `B^A × A → B` (function application). -/
  eval : {A B : Obj} → Hom (prod (exp A B) A) B
  /-- Currying: transpose a map `Z × A → B` to `Z → B^A` (λ-abstraction). -/
  curry : {Z A B : Obj} → Hom (prod Z A) B → Hom Z (exp A B)
  /-- β for exponentials: `⟨fst ⨟ curry f, snd⟩ ⨟ eval = f`
      — the shadow of `ev ∘ ⟨curry f, 𝟙⟩ = f`. -/
  curry_eval : ∀ {Z A B : Obj} (f : Hom (prod Z A) B),
                 comp (pair (comp fst (curry f)) snd) eval = f
  /-- Uniqueness of the transpose (η for exponentials). -/
  curry_unique : ∀ {Z A B : Obj} (f : Hom (prod Z A) B) (g : Hom Z (exp A B)),
                   comp (pair (comp fst g) snd) eval = f → g = curry f

/-- **`Type` is cartesian closed** — the prototype (`Set`).
`⊤ = PUnit`, `X × Y` is the product type, and `B^A = A → B` with `eval` the
application and `curry` the λ-abstraction. -/
instance : CartesianClosed (Type u) where
  term := PUnit
  toTerm _ := fun _ => PUnit.unit
  toTerm_unique _ := rfl
  prod X Y := X × Y
  fst := fun p => p.1
  snd := fun p => p.2
  pair f g := fun z => (f z, g z)
  pair_fst _ _ := rfl
  pair_snd _ _ := rfl
  pair_unique _ := rfl
  exp A B := A → B
  eval := fun p => p.1 p.2
  curry f := fun z => fun a => f (z, a)
  curry_eval _ := rfl
  curry_unique f g hyp := by
    funext z a
    exact congrFun hyp (z, a)

/-! ## A derived fact, proved once for every cartesian closed category

From the product's universal property alone, `⟨fst, snd⟩ = 𝟙` — the "surjective
pairing"/η law for products. -/

open Category CartesianClosed in
example {Obj : Type u} [CartesianClosed Obj] (X Y : Obj) :
    pair (fst : Hom (prod X Y) X) (snd : Hom (prod X Y) Y) = Category.id (prod X Y) := by
  have h := pair_unique (Category.id (prod X Y))
  simpa [Category.id_comp] using h

end Playground.CCC
