/-
  PILOT — Practical Foundations for Programming Languages (PFPL), 2nd ed.
  Robert Harper, Cambridge University Press, 2016.
  Rendered from the author-authorized free "Abbreviated online edition"
  (https://www.cs.cmu.edu/~rwh/pfpl/abbrev.pdf).

  Source: Part II "Statics and Dynamics", Chapter 4 "Statics",
          Sections 4.1 (Syntax) and 4.2 (Type System) — the language E.
          Typing rules (4.1a)–(4.1h), book pp. 35–37.

  STATUS: pilot / proof-of-concept only. This renders the abstract syntax
  and the statics (typing judgment) of E. It deliberately does NOT cover the
  dynamics (Ch. 5) or type safety (Ch. 6), and is not part of the ScottLean
  Lake library — it stands alone on core Lean 4 (no Mathlib).

  Modelling choices vs. the book:
  * Harper uses abstract binding trees with a generic hypothetical judgment
    `X | Γ ⊢ e : τ`. Here we use concrete named variables (`String`) and a
    typing context `Ctx = List (String × Ty)`, which is the standard first
    approximation. The α-conversion / freshness side condition on `let`
    (rule 4.1h) is handled informally by context lookup, exactly as a
    beginner rendering; a de Bruijn version would remove the informality.
-/

namespace PFPL.Ch4.LanguageE

/-- Types of E (Section 4.1). Two sorts of value: numbers and strings.
    `Typ τ ::= num | str`. -/
inductive Ty where
  | num
  | str
  deriving DecidableEq, Repr

/-- Expressions of E (Section 4.1), following the syntax chart on p.36.
    `Exp e ::= x | num[n] | str[s] | plus(e1;e2) | times(e1;e2)
             | cat(e1;e2) | len(e) | let(e1; x.e2)`. -/
inductive Exp where
  | var   (x : String)                         -- x            variable
  | num   (n : Nat)                            -- num[n]       numeral
  | str   (s : String)                         -- str[s]       literal
  | plus  (e1 e2 : Exp)                        -- plus(e1;e2)  addition
  | times (e1 e2 : Exp)                        -- times(e1;e2) multiplication
  | cat   (e1 e2 : Exp)                        -- cat(e1;e2)   concatenation
  | len   (e : Exp)                            -- len(e)       length
  | letE  (e1 : Exp) (x : String) (e2 : Exp)   -- let(e1;x.e2) definition
  deriving Repr

/-- A typing context Γ: hypotheses `x : τ`, one per variable. -/
abbrev Ctx := List (String × Ty)

/-- The statics of E: the generic hypothetical judgment `Γ ⊢ e : τ`,
    inductively defined by rules (4.1a)–(4.1h) on pp. 36–37.
    The rules are syntax-directed — exactly one per expression form. -/
inductive HasType : Ctx → Exp → Ty → Prop where
  /-- (4.1a) variable: `Γ, x : τ ⊢ x : τ`. Here: `x : τ ∈ Γ`. -/
  | var   {Γ x τ}      (h : (x, τ) ∈ Γ) :
      HasType Γ (.var x) τ
  /-- (4.1c) `Γ ⊢ num[n] : num`. -/
  | num   {Γ n} :
      HasType Γ (.num n) .num
  /-- (4.1b) `Γ ⊢ str[s] : str`. -/
  | str   {Γ s} :
      HasType Γ (.str s) .str
  /-- (4.1d) `Γ ⊢ e1 : num   Γ ⊢ e2 : num   ⟹   Γ ⊢ plus(e1;e2) : num`. -/
  | plus  {Γ e1 e2} (h1 : HasType Γ e1 .num) (h2 : HasType Γ e2 .num) :
      HasType Γ (.plus e1 e2) .num
  /-- (4.1e) `Γ ⊢ e1 : num   Γ ⊢ e2 : num   ⟹   Γ ⊢ times(e1;e2) : num`. -/
  | times {Γ e1 e2} (h1 : HasType Γ e1 .num) (h2 : HasType Γ e2 .num) :
      HasType Γ (.times e1 e2) .num
  /-- (4.1f) `Γ ⊢ e1 : str   Γ ⊢ e2 : str   ⟹   Γ ⊢ cat(e1;e2) : str`. -/
  | cat   {Γ e1 e2} (h1 : HasType Γ e1 .str) (h2 : HasType Γ e2 .str) :
      HasType Γ (.cat e1 e2) .str
  /-- (4.1g) `Γ ⊢ e : str   ⟹   Γ ⊢ len(e) : num`. -/
  | len   {Γ e} (h : HasType Γ e .str) :
      HasType Γ (.len e) .num
  /-- (4.1h) `Γ ⊢ e1 : τ1   Γ, x : τ1 ⊢ e2 : τ2   ⟹   Γ ⊢ let(e1;x.e2) : τ2`.
      (Book assumes `x` fresh for `Γ`, met by α-renaming.) -/
  | letE  {Γ e1 x e2 τ1 τ2}
      (h1 : HasType Γ e1 τ1) (h2 : HasType ((x, τ1) :: Γ) e2 τ2) :
      HasType Γ (.letE e1 x e2) τ2

@[inherit_doc] notation:50 Γ " ⊢ " e " : " τ => HasType Γ e τ

/-! ### Sanity checks (not part of the book; confirm the rendering type-checks) -/

/-- `⊢ len("abc") + 2 : num`, using rules (4.1d), (4.1g), (4.1b), (4.1c). -/
example : ([] : Ctx) ⊢ (.plus (.len (.str "abc")) (.num 2)) : .num :=
  .plus (.len .str) .num

/-- `⊢ let x be 3 in x + x : num`, using (4.1h), (4.1a), (4.1d), (4.1c). -/
example :
    ([] : Ctx) ⊢ (.letE (.num 3) "x" (.plus (.var "x") (.var "x"))) : .num :=
  .letE .num (.plus (.var (by simp)) (.var (by simp)))

end PFPL.Ch4.LanguageE
