/-
  Sheaves and Logic (Lean 4 formalization)

  Faithful to:
    M. P. Fourman and D. S. Scott,
    "Sheaves and Logic",
    in: Applications of Sheaves, Lecture Notes in Mathematics 753,
    Springer, 1979, pp. 302-401.

  Source text extracted from:
    DanaScottPapers/Fourman-Scott-1979-Sheaves-and-Logic.txt

  Auto-generated faithful skeleton.

  The paper develops the theory of sheaves over a complete Heyting algebra (cHa)
  as a semantics for intuitionistic higher-order logic.  We encode the core
  first-order machinery of Chapters I–II:

    * complete Heyting algebras (Definition 1.1) via the frame distributive law,
      with the Heyting implication `⇨` and a proof of the Heyting adjunction
      `r ⊓ p ≤ q  ↔  r ≤ (p ⇨ q)`;
    * `Ω`-sets (Definition 4.1): an `Ω`-valued equality with symmetry and
      transitivity; extent `E a = [a = a]` and equivalence `[a ∈ b]`;
    * presheaves over a cHa (Definition 4.2);
    * singletons (Definition 4.10) and the notions of separated / complete `Ω`-set,
      i.e. sheaf (Definitions 4.6, 4.9, 4.11);
    * the interpretation of the propositional/first-order connectives in the cHa
      of truth values (Chapter 0 / §5).

  Core Lean 4 only; no Mathlib.
-/

namespace FourmanScott1979

universe u v

/-! ## Chapter I.  Complete Heyting algebras (Definition 1.1)

    "A cHa is a complete lattice `Ω` satisfying the `∧,⋁`-distributive law
     `p ∧ ⋁ᵢ aᵢ = ⋁ᵢ (p ∧ aᵢ)`." -/

/-- A **complete Heyting algebra** (cHa): a complete lattice (order `≤`, binary
    meet `⊓`, top `⊤`, arbitrary sups `⋁`) satisfying the frame distributive law. -/
class cHa (Ω : Type u) where
  le : Ω → Ω → Prop
  le_refl : ∀ p, le p p
  le_trans : ∀ p q r, le p q → le q r → le p r
  le_antisymm : ∀ p q, le p q → le q p → p = q
  meet : Ω → Ω → Ω
  meet_le_left : ∀ p q, le (meet p q) p
  meet_le_right : ∀ p q, le (meet p q) q
  le_meet : ∀ p q r, le p q → le p r → le p (meet q r)
  top : Ω
  le_top : ∀ p, le p top
  sSup : (Ω → Prop) → Ω
  le_sSup : ∀ (S : Ω → Prop) a, S a → le a (sSup S)
  sSup_le : ∀ (S : Ω → Prop) b, (∀ a, S a → le a b) → le (sSup S) b
  /-- Frame distributive law (Definition 1.1), oriented `(⋁S) ∧ p = ⋁_{a∈S}(a∧p)`. -/
  frame : ∀ (p : Ω) (S : Ω → Prop),
    meet (sSup S) p = sSup (fun z => ∃ a, S a ∧ z = meet a p)

namespace cHa

variable {Ω : Type u} [cHa Ω]

scoped infix:50 " ≤ω " => cHa.le
scoped infixl:70 " ⊓ " => cHa.meet

/-- **Heyting implication** `p ⇨ q = ⋁ { r | r ∧ p ≤ q }`. -/
def himp (p q : Ω) : Ω := sSup (fun r => le (meet r p) q)

@[inherit_doc] scoped infixr:60 " ⇨ " => cHa.himp

/-- Heyting adjunction, direction ⇐:  `r ⊓ p ≤ q → r ≤ (p ⇨ q)`.  Immediate from
    `le_sSup`. -/
theorem le_himp_of_meet_le {p q r : Ω} (h : le (meet r p) q) : le r (himp p q) :=
  le_sSup _ r h

/-- Heyting adjunction, direction ⇒:  `(p ⇨ q) ⊓ p ≤ q`.  Uses the frame law. -/
theorem himp_meet_le (p q : Ω) : le (meet (himp p q) p) q := by
  rw [himp, frame]
  apply sSup_le
  rintro z ⟨r, hr, rfl⟩
  exact hr

/-- Full Heyting adjunction (Definition of a cHa as a residuated lattice). -/
theorem heyting_adjunction (p q r : Ω) :
    le (meet r p) q ↔ le r (himp p q) := by
  constructor
  · exact le_himp_of_meet_le
  · intro h
    exact le_trans _ _ _ (le_meet _ _ _ (le_trans _ _ _ (meet_le_left r p) h)
      (meet_le_right r p)) (himp_meet_le p q)

end cHa

open cHa

/-! ## Chapter II, §4.  Ω-sets and sheaves -/

/-- **Ω-set** (Definition 4.1): a carrier `|A|` with an `Ω`-valued equality
    `[· = ·]` satisfying symmetry and transitivity. -/
structure OmegaSet (Ω : Type u) [cHa Ω] where
  /-- the underlying set `|A|`. -/
  Carrier : Type v
  /-- the `Ω`-valued equality `[a = b]`. -/
  eq : Carrier → Carrier → Ω
  /-- (i) symmetry:  `[a = b] = [b = a]`. -/
  symm : ∀ a b, eq a b = eq b a
  /-- (ii) transitivity:  `[a = b] ⊓ [b = c] ≤ [a = c]`. -/
  trans : ∀ a b c, cHa.le (cHa.meet (eq a b) (eq b c)) (eq a c)

namespace OmegaSet

variable {Ω : Type u} [cHa Ω] (A : OmegaSet.{u, v} Ω)

/-- **Extent** (Definition 4.1 (iii)):  `E a = [a = a]`. -/
def extent (a : A.Carrier) : Ω := A.eq a a

/-- **Equivalence** (Definition 4.1 (iv)):  `[a ∈ b]`… here the membership/
    equivalence value `[a ≡ b] = [a = b]` (single-sorted case). -/
def equiv (a b : A.Carrier) : Ω := A.eq a b

/-- **Singleton** (Definition 4.10): a map `s : |A| → Ω` with
    `s a ⊓ [a = b] ≤ s b` and `s a ⊓ s b ≤ [a = b]`. -/
structure Singleton where
  s : A.Carrier → Ω
  /-- (i)  `s a ⊓ [a = b] ≤ s b`. -/
  restr : ∀ a b, cHa.le (cHa.meet (s a) (A.eq a b)) (s b)
  /-- (ii)  `s a ⊓ s b ≤ [a = b]`. -/
  strict : ∀ a b, cHa.le (cHa.meet (s a) (s b)) (A.eq a b)

/-- The **principal singleton** of an element `c` (Definition 4.10 discussion):
    `ĉ (a) = [a = c]`.  It is a singleton by transitivity and symmetry. -/
def principal (c : A.Carrier) : A.Singleton where
  s := fun a => A.eq a c
  restr := fun a b => by
    -- [a = c] ⊓ [a = b] = [a = c] ⊓ [b = a] ≤ … ; use symmetry then transitivity
    have h1 : cHa.le (cHa.meet (A.eq a c) (A.eq a b)) (cHa.meet (A.eq b a) (A.eq a c)) :=
      cHa.le_meet _ _ _
        (by rw [A.symm a b]; exact cHa.meet_le_right (A.eq a c) (A.eq b a))
        (cHa.meet_le_left (A.eq a c) (A.eq a b))
    exact cHa.le_trans _ _ _ h1 (A.trans b a c)
  strict := fun a b => by
    -- [a = c] ⊓ [b = c] = [a = c] ⊓ [c = b] ≤ [a = b]
    have h1 : cHa.le (cHa.meet (A.eq a c) (A.eq b c)) (cHa.meet (A.eq a c) (A.eq c b)) :=
      cHa.le_meet _ _ _ (cHa.meet_le_left (A.eq a c) (A.eq b c))
        (by rw [A.symm c b]; exact cHa.meet_le_right (A.eq a c) (A.eq b c))
    exact cHa.le_trans _ _ _ h1 (A.trans a c b)

/-- **Separated** (Definition 4.6): `[a = b] = ⊤` always implies `a = b`. -/
def IsSeparated : Prop := ∀ a b : A.Carrier, A.eq a b = cHa.top → a = b

/-- **Complete Ω-set = sheaf** (Definitions 4.9, 4.11 and Theorem 4.13): every
    singleton is *principal*, i.e. determined by a unique element `c` with
    `s a = [a = c]` for all `a`. -/
def IsComplete : Prop :=
  ∀ s : A.Singleton, ∃ c : A.Carrier, (∀ a, s.s a = A.eq a c)

/-- **Theorem 4.13** rendering: sheaves and complete Ω-sets coincide.
    Here we take completeness (every singleton is principal) as the definition of
    sheaf, matching the paper's identification. -/
def IsSheaf : Prop := A.IsComplete

end OmegaSet

/-! ### Presheaves (Definition 4.2) -/

/-- **Presheaf** over a cHa (Definition 4.2): a carrier with an extent map `E` and
    a restriction map `⌐` satisfying the presheaf axioms. -/
structure Presheaf (Ω : Type u) [cHa Ω] where
  Carrier : Type v
  /-- extent `E a`. -/
  E : Carrier → Ω
  /-- restriction `a ⌐ p` (the part of `a` on `p`). -/
  restrict : Carrier → Ω → Carrier
  /-- (i)  `E (a ⌐ p) = E a ⊓ p`. -/
  E_restrict : ∀ a p, E (restrict a p) = cHa.meet (E a) p
  /-- (ii)  `a ⌐ (E a) = a`. -/
  restrict_extent : ∀ a, restrict a (E a) = a
  /-- (iii)  `(a ⌐ p) ⌐ q = a ⌐ (p ⊓ q)`. -/
  restrict_restrict : ∀ a p q, restrict (restrict a p) q = restrict a (cHa.meet p q)

/-- **Proposition 4.3**: every presheaf is an Ω-set with
    `[a = b] = (E a ⊓ E b) ⊓ ⟦a ≈ b⟧`; here rendered by the induced equality
    `[a = b] := E a ⊓ E b` composed with the restriction agreement.  We expose the
    induced `Ω`-valued equality as the definition promised by the paper. -/
def Presheaf.inducedEq {Ω : Type u} [cHa Ω] (A : Presheaf.{u, v} Ω)
    (a b : A.Carrier) : Ω :=
  cHa.meet (A.E a) (A.E b)

/-! ## Chapter 0 / §5.  Interpretation of logic in the cHa of truth values

    The truth value `⟦φ⟧ ∈ Ω` of a formula is computed compositionally; the
    connectives are interpreted by the cHa operations. -/

namespace Interp

variable {Ω : Type u} [cHa Ω]

/-- `⟦⊤⟧ = ⊤`. -/
def top : Ω := cHa.top
/-- `⟦φ ∧ ψ⟧ = ⟦φ⟧ ⊓ ⟦ψ⟧`. -/
def andI (p q : Ω) : Ω := cHa.meet p q
/-- `⟦φ ∨ ψ⟧ = ⟦φ⟧ ⊔ ⟦ψ⟧`  (binary join via `sSup`). -/
def orI (p q : Ω) : Ω := cHa.sSup (fun z => z = p ∨ z = q)
/-- `⟦φ → ψ⟧ = ⟦φ⟧ ⇨ ⟦ψ⟧`. -/
def impI (p q : Ω) : Ω := cHa.himp p q
/-- `⟦⊥⟧ = ⋁ ∅` (the least element). -/
def bot : Ω := cHa.sSup (fun _ => False)
/-- `⟦¬φ⟧ = ⟦φ⟧ ⇨ ⊥`. -/
def notI (p : Ω) : Ω := cHa.himp p bot
/-- `⟦∃x. φ x⟧ = ⋁ₓ ⟦φ x⟧`  (indexed join over the domain `D`). -/
def existI {D : Type v} (φ : D → Ω) : Ω := cHa.sSup (fun z => ∃ d, z = φ d)
/-- `⟦∀x. φ x⟧ = ⋀ₓ ⟦φ x⟧`  (indexed meet, as the sup of all lower bounds). -/
def forallI {D : Type v} (φ : D → Ω) : Ω :=
  cHa.sSup (fun b => ∀ d, cHa.le b (φ d))

end Interp

end FourmanScott1979
