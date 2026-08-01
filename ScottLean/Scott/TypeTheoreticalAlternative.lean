/-
  A Type-Theoretical Alternative to ISWIM, CUCH, OWHY (Lean 4 formalization, pilot)

  Faithful to:
    D. Scott, "A Type-Theoretical Alternative to ISWIM, CUCH, OWHY",
    Theoretical Computer Science 121(1-2):411-440, 1993 (written 1969).
    (The original 1969 manuscript proposing LCF.)

  Source text extracted from:
    DanaScottPapers/Scott-1993-A-Type-Theoretical-Alternative-to-ISWIM-CUCH-OWHY.pdf

  This file transcribes the core of Sections 1-2 ("Types" and "Interpretation"):
    * The type symbols: two ground types  ι (individuals) and  o (truth values),
      closed under function-space formation  (α β)  (Church's notation).
    * Typed expressions X : α with variables, application and abstraction.
    * The interpretation: each type α is assigned a domain D_α partially ordered
      by  ≤  ("is less or equally defined as"), with an undefined element Ω_α as
      least element; D_o is the flat three-element domain {⊤, ⊥, Ω_o}.
    * Monotonicity of the intended functionals and the least-fixed-point operator
      Y (the recursion / least-fixed-point combinator).

  Core Lean 4 only; no Mathlib.
-/

namespace TypeTheoreticalAlternative

/-! ## Type symbols

    "Two 'logical' types represented by ι and o.  ι stands for the type of all
     individuals ... o is the type of the truth values.  If α and β are types,
     then so is (αβ): the type of functions from objects of type α to those of
     type β."  (Church's type notation.) -/
inductive Ty where
  | iota : Ty                 -- ι, individuals
  | omicron : Ty              -- o, truth values
  | arrow : Ty → Ty → Ty      -- (α β), functions from α to β
  deriving DecidableEq, Repr

infixr:30 " ⇒ " => Ty.arrow

/-! ## Typed expressions

    "Each expression will have a (unique) type, and I write X : α to mean that the
     expression X is of type α."  Expressions are built from typed variables by
     application and (typed) λ-abstraction, giving a typed λ-calculus presentation
     of Scott's typed combinator system.

    We use intrinsically-typed de Bruijn terms over a context `Ctx = List Ty`. -/
abbrev Ctx := List Ty

/-- `Var Γ α` : a de Bruijn index selecting a variable of type `α` from `Γ`. -/
inductive Var : Ctx → Ty → Type where
  | zero {Γ : Ctx} {α : Ty} : Var (α :: Γ) α
  | succ {Γ : Ctx} {α β : Ty} : Var Γ α → Var (β :: Γ) α

/-- `Tm Γ α` : a well-typed expression of type `α` in context `Γ`.

    * `var`   — a variable  x : α
    * `app`   — application  (X : α ⇒ β)(Y : α) : β
    * `lam`   — abstraction  (λ x:α. X : β) : α ⇒ β
    * `Y`     — the least-fixed-point operator  Y : ((α ⇒ α) ⇒ α)  (Scott's
                recursion operator / least-fixed-point combinator).
    * `omega` — the "undefined" constant Ω_α of every type. -/
inductive Tm : Ctx → Ty → Type where
  | var {Γ α}   : Var Γ α → Tm Γ α
  | app {Γ α β} : Tm Γ (α ⇒ β) → Tm Γ α → Tm Γ β
  | lam {Γ α β} : Tm (α :: Γ) β → Tm Γ (α ⇒ β)
  | Yc  {Γ α}   : Tm Γ ((α ⇒ α) ⇒ α)          -- least-fixed-point operator Y
  | omega {Γ α} : Tm Γ α                        -- Ω_α, the undefined element

/-! ## Interpretation: domains D_α ordered by "is less or equally defined as"

    "Assign to each type α a domain D_α, where D_ι is a given domain of
     individuals, D_o is the domain of two truth values (⊤, ⊥) with an adjoined
     undefined element Ω_o, and D_(αβ) is the domain of all [monotone] functions
     from D_α to D_β.  We adjoin a 'fictitious' element Ω and create a relation ≤
     ('is less or equally defined as') with Ω ≤ x for all x."

    We model the truth-value domain D_o as the flat domain with least element. -/

/-- The flat domain of truth values `D_o = {⊤, ⊥, Ω_o}` with Ω_o least. -/
inductive DBool where
  | undef : DBool     -- Ω_o, the undefined truth value (bottom)
  | tt : DBool        -- ⊤ (true)
  | ff : DBool        -- ⊥ in Scott's text is "false"; kept distinct from Ω_o
  deriving DecidableEq, Repr

/-- The information order `≤` ("less or equally defined as") on `D_o`:
    "a reasonable assumption is Ω ≤ x for all x; but x ≤ y implies x = y for
     x, y ≠ Ω."  Hence D_o is *flat*: Ω_o below the two total values, which are
     incomparable. -/
def DBool.le : DBool → DBool → Prop
  | .undef, _        => True          -- Ω_o ≤ everything
  | .tt,    .tt      => True
  | .ff,    .ff      => True
  | _,      _        => False

infix:50 " ≤ᵒ " => DBool.le

/-- Reflexivity of the information order on `D_o`. -/
theorem DBool.le_refl : ∀ b : DBool, b ≤ᵒ b := by
  intro b; cases b <;> trivial

/-- Ω_o is the least element: "Ω ≤ x for all x". -/
theorem DBool.undef_least : ∀ b : DBool, DBool.undef ≤ᵒ b := by
  intro b; trivial

/-- "x ≤ y implies x = y for x ≠ Ω": totality above bottom (the flatness law). -/
theorem DBool.flat {x y : DBool} (hx : x ≠ DBool.undef) (h : x ≤ᵒ y) : x = y := by
  cases x <;> cases y <;> first | rfl | (exact absurd rfl hx) | (cases h)

/-! ## Domain assignment ⟦α⟧ and the information order

    `Dom α` is the Lean type interpreting `D_α`.  Following Scott, `D_(αβ)` is a
    function space; here we interpret it as the full Lean function space and carry
    the pointwise "less-or-equally-defined" order separately.  Individuals `D_ι`
    are interpreted (schematically) as `DBool`'s flat pattern lifted to `Option`;
    the essential structure Scott needs is only that every `D_α` has a least
    element Ω_α and a monotone order, which we record abstractly below. -/
def Dom : Ty → Type
  | .iota      => Option Nat        -- a flat domain of individuals (none = Ω_ι)
  | .omicron   => DBool
  | .arrow α β => Dom α → Dom β

/-- The information order `⊑` on every domain `D_α`
    ("is less or equally defined as"), by recursion on the type:
    flat on ground types, pointwise on function types. -/
def leD : (α : Ty) → Dom α → Dom α → Prop
  | .iota,      x, y => x = none ∨ x = y
  | .omicron,   x, y => x ≤ᵒ y
  | .arrow _ β, f, g => ∀ x, leD β (f x) (g x)

/-- The least ("wholly undefined") element Ω_α of each domain `D_α`. -/
def omegaD : (α : Ty) → Dom α
  | .iota      => none
  | .omicron   => DBool.undef
  | .arrow _ β => fun _ => omegaD β

/-- Ω_α is the least element of `D_α` in the information order (by induction on α):
    "Ω ≤ x for all x." -/
theorem omegaD_least : ∀ (α : Ty) (x : Dom α), leD α (omegaD α) x := by
  intro α
  induction α with
  | iota => intro x; exact Or.inl rfl
  | omicron => intro x; trivial
  | arrow α β _ ihβ => intro f; intro x; exact ihβ (f x)

/-- The information order is reflexive on every `D_α`. -/
theorem leD_refl : ∀ (α : Ty) (x : Dom α), leD α x x := by
  intro α
  induction α with
  | iota => intro x; exact Or.inr rfl
  | omicron => intro x; exact DBool.le_refl x
  | arrow α β _ ihβ => intro f x; exact ihβ (f x)

/-! ## The least-fixed-point operator (Scott's recursion operator Y)

    Scott's system has "a recursion operator (the least fixed-point operator)".
    Its intended meaning: for a monotone/continuous `f : D_α → D_α`, `Y f` is the
    least `x` with `f x = x`.  We record the two defining properties as target
    statements (their construction needs the continuity/ω-completeness of the
    D_α, developed in the paper). -/

/-- `f : D_α → D_α` is monotone in the information order. -/
def Monotone (α : Ty) (f : Dom α → Dom α) : Prop :=
  ∀ x y, leD α x y → leD α (f x) (f y)

/-- Specification of the least-fixed-point operator `Y` at type `α`:
    `Y f` is a fixed point, and it is the least among all pre-fixed points. -/
structure IsLeastFixedPoint (α : Ty) (f : Dom α → Dom α) (p : Dom α) : Prop where
  isFixed : f p = p
  isLeast : ∀ q, leD α (f q) q → leD α p q

/-- Target theorem (Scott's recursion operator): every monotone/continuous `f`
    over a domain `D_α` has a least fixed point.  Signature recorded for the pilot;
    the witness is `⋃ₙ fⁿ(Ω_α)` as in the Pω development. -/
def Y_gives_least_fixed_point : Prop :=
  ∀ (α : Ty) (f : Dom α → Dom α), Monotone α f →
    ∃ p, IsLeastFixedPoint α f p

end TypeTheoreticalAlternative
