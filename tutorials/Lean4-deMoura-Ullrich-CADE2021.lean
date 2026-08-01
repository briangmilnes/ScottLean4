/-
Code extracted from:
  Leonardo de Moura and Sebastian Ullrich,
  "The Lean 4 Theorem Prover and Programming Language",
  CADE-28, LNAI 12699, pp. 625-635, 2021.
  https://doi.org/10.1007/978-3-030-79876-5_37   (Open Access, CC-BY 4.0)

The paper's canonical, compiling source is at
  https://github.com/leanprover/lean4/blob/cade2021/doc/BoolExpr.lean

NOTE: this is a faithful transcription of the listings AS PRINTED in the paper,
in order. It is for reading, not a clean build: the paper shows two alternative
definitions of `or`, and some proofs are elided in the paper with `...`. Those
spots are marked below.
-/

-- The Boolean `or`, defined by pattern-matching on the first argument.
def or (a b : Bool) :=
  match a with
  | true => true
  | false => b

#check or true false -- Bool (this is a comment in Lean)
#eval or true false -- true

-- Alternative definition of `or` using the match-macro sugar (paper shows both;
-- commented out here because it would clash with the definition above).
-- def or : Bool → Bool → Bool
--   | true, _ => true
--   | false, b => b

-- A theorem is a definition whose result type is a proposition.
theorem or_true (b : Bool) : or true b = true :=
  rfl

theorem or_self : ∀ (b : Bool), or b b = b
  | true => rfl
  | false => rfl

-- A recursive datatype for Boolean expressions.
inductive BoolExpr where
  | var (name : String)
  | val (b : Bool)
  | or (p q : BoolExpr)
  | not (p : BoolExpr)

-- A bottom-up "simplifier" with local auxiliary functions via `where`.
def simplify : BoolExpr → BoolExpr
  | BoolExpr.or p q => mkOr (simplify p) (simplify q)
  | BoolExpr.not p => mkNot (simplify p)
  | e               => e
  where
    mkOr : BoolExpr → BoolExpr → BoolExpr
      | p, BoolExpr.val true  => BoolExpr.val true
      | p, BoolExpr.val false => p
      | BoolExpr.val true, p  => BoolExpr.val true
      | BoolExpr.val false, p => p
      | p, q                  => BoolExpr.or p q

    mkNot : BoolExpr → BoolExpr
      | BoolExpr.val b => BoolExpr.val (not b)
      | p              => BoolExpr.not p

-- A denotation (evaluator) using an association list as the context.
abbrev Context := AssocList String Bool

def denote (ctx : Context) : BoolExpr → Bool
  | BoolExpr.or p q => denote ctx p || denote ctx q
  | BoolExpr.not p => !denote ctx p
  | BoolExpr.val b => b
  | BoolExpr.var x => if let some b := ctx.find? x then b else false

-- Correctness of the simplifier (proofs abbreviated with `...` in the paper).
@[simp] theorem denote_mkOr (ctx : Context) (p q : BoolExpr)
        : denote ctx (simplify.mkOr p q) = denote ctx (or p q) :=
  sorry -- `...` in the paper

def denote_simplify (ctx : Context) (p : BoolExpr)
    : denote ctx (simplify p) = denote ctx p :=
  by induction p with
  | or p q ih1 ih2 => simp [ih1, ih2]
  | not p ih          => simp [ih]
  | _                 => rfl

-- Typeclasses: the standard `Inhabited` class and instances.
class Inhabited (α : Sort u) where
  default : α

def arbitrary [Inhabited α] : α :=
  Inhabited.default

instance : Inhabited BoolExpr where
  default := BoolExpr.val false

instance [Inhabited α] [Inhabited β] : Inhabited (α × β) where
  default := (arbitrary, arbitrary)

-- Deriving decidable equality.
deriving instance DecidableEq for BoolExpr

#eval decide (BoolExpr.val true = BoolExpr.val false) -- false

-- Notation / macros (progressively lower levels of the abstraction tower).
infix:50 "⊢" => denote

notation:50 Γ "⊢" p:50 => denote Γ p

macro:50 Γ:term "⊢" p:term:50 : term => `(denote $Γ $p)

syntax:50 term "⊢" term:50 : term
macro_rules
  | `($Γ ⊢ $e) => `(denote $Γ $e)

-- An embedded DSL for building BoolExpr objects.
syntax "`[BExpr|" term "]" : term
macro_rules
  | `(`[BExpr| true])     => `(BoolExpr.val true)
  | `(`[BExpr| false])    => `(BoolExpr.val false)
  | `(`[BExpr| $x:ident]) => `(BoolExpr.var $(quote x.getId.toString))
  | `(`[BExpr| $p ∨ $q]) => `(BoolExpr.or `[BExpr| $p] `[BExpr| $q])
  | `(`[BExpr| ¬ $p])     => `(BoolExpr.not `[BExpr| $p])

#check `[BExpr| p ∨ true]
-- BoolExpr.or (BoolExpr.var "p") (BoolExpr.val true) : BoolExpr

-- A context as a comma-separated sequence of `var ↦ value` entries.
syntax entry := ident " ↦ " term:max
syntax entry,* "⊢" term : term
macro_rules
  | `( $[$xs:ident ↦ $vs:term],* ⊢ $p:term ) =>
    let xs := xs.map fun x => quote x.getId.toString
    `(denote (List.toAssocList [$[( $xs , $vs )],*]) `[BExpr| $p])

#eval a ↦ false, b ↦ true ⊢ b ∨ a -- true

-- Functional-but-in-place example: mapping over a list.
def map : (α → β) → List α → List β
  | f, []    => []
  | f, a::as => f a :: map f as
