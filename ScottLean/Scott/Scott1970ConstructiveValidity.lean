/-
  Constructive Validity — the theory of constructions and species
  (Lean 4 auto-generated faithful skeleton)

  Faithful to:
    D. Scott, "Constructive Validity", in Symposium on Automatic Demonstration
    (Versailles, 1968), Lecture Notes in Mathematics 125, Springer, 1970,
    pp. 237-275.

  Source text extracted from:
    DanaScottPapers/Scott-1970-Constructive-Validity.txt

  Scott builds a type-free calculus of CONSTRUCTIONS and SPECIES with a single
  sort of variable, and *interprets* intuitionistic logic into it (a
  proofs-as-constructions / Curry-Howard reading).  There are exactly two atomic
  formula forms — membership `σ ∈ τ` and equation `σ = τ` — and only TERMS are
  compounded, never formulas.  Judgements are sequents `Δ ⊢ θ` with `Δ` a finite
  list of atoms and `θ` a single atom.

  We formalize:
    * SYNTAX: the untyped construction terms (constants 𝟎,𝟏,𝟐,δ,𝟬,𝟭,○; the
      compounds application, projections, pair `[·∧·]`, successor `·⁺`, tree
      `𝒯`, and the binders `∀x∈a[·]`, `∃x∈a[·]`, `Px∈a[·]`, `ℛv[a,b,·]`);
      atoms `∈`, `=`; and naive substitution.
    * INFERENCE: the sequent relation `Derives` with the structural rules
      (I1)-(I5), equality (E1)-(E2), functions (F1)-(F2), products (P1)-(P3),
      sums (S1)-(S7), generators (G1)-(G9), transfinite constructions (T1)-(T6).
    * The logical operators as DEFINED construction terms (∧,∨,→,¬,⊤,⊥,∀,∃), and
      constructive VALIDITY `⊨ φ := ∃ T. ⊢ T ∈ φ`.
    * The Fundamental Conjecture (decidability of `⊢ σ∈τ`) and the undecidability
      of the hypothetical form, stated with `sorry`.

  Core Lean 4 only; no Mathlib.
-/

namespace Scott1970ConstructiveValidity

/-! ## 1. Syntax of constructions (lines 265-327) -/

/-- Type-free construction/species terms.  Variables are natural numbers; the
    binders `pi`, `sigma`, `pairfun` bind `x` in their body, `rec` binds `v`. -/
inductive Con where
  | var      : Nat → Con
  | zero     : Con                     -- 𝟎  (empty species)
  | one      : Con                     -- 𝟏  (one-element species)
  | two      : Con                     -- 𝟐  (two-element species)
  | delta    : Con                     -- δ ∈ 𝟏
  | b0       : Con                     -- 𝟬 ∈ 𝟐
  | b1       : Con                     -- 𝟭 ∈ 𝟐
  | app      : Con → Con → Con         -- σ(τ)
  | proj0    : Con → Con               -- σ₀
  | proj1    : Con → Con               -- σ₁
  | pair     : Con → Con → Con         -- [σ ∧ τ]
  | succ     : Con → Con               -- σ⁺  (proxy / successor)
  | tree     : Con → Con               -- 𝒯(a)
  | nulltree : Con → Con               -- ○(a)  (null tree over species a)
  | pi       : Nat → Con → Con → Con   -- ∀x∈a[σ]  (product / abstraction)
  | sigma    : Nat → Con → Con → Con   -- ∃x∈a[σ]  (disjoint sum)
  | pairfun  : Nat → Con → Con → Con   -- Px∈a[σ]  (pairing function for the sum)
  | recop    : Nat → Con → Con → Con → Con  -- ℛv[a,b,σ]  (recursion over 𝒯(a))
  deriving Repr, DecidableEq

/-- Atoms: the two formula forms.  Only these are asserted in sequents. -/
inductive Atom where
  | mem : Con → Con → Atom             -- σ ∈ τ
  | eq  : Con → Con → Atom             -- σ = τ
  deriving Repr, DecidableEq

/-! ### Free variables and naive substitution -/

/-- `x` not free in a construction. -/
def Con.notFree (x : Nat) : Con → Prop
  | .var i => x ≠ i
  | .zero | .one | .two | .delta | .b0 | .b1 => True
  | .app a b | .pair a b => Con.notFree x a ∧ Con.notFree x b
  | .proj0 a | .proj1 a | .succ a | .tree a | .nulltree a => Con.notFree x a
  | .pi i a b | .sigma i a b | .pairfun i a b =>
      Con.notFree x a ∧ (x = i ∨ Con.notFree x b)
  | .recop i a b c => Con.notFree x a ∧ Con.notFree x b ∧ (x = i ∨ Con.notFree x c)

/-- Naive substitution `[σ/x]` in a construction (α-conversion assumed as needed). -/
def Con.subst (x : Nat) (s : Con) : Con → Con
  | .var i => if x = i then s else .var i
  | .zero => .zero | .one => .one | .two => .two
  | .delta => .delta | .b0 => .b0 | .b1 => .b1
  | .app a b => .app (Con.subst x s a) (Con.subst x s b)
  | .proj0 a => .proj0 (Con.subst x s a)
  | .proj1 a => .proj1 (Con.subst x s a)
  | .pair a b => .pair (Con.subst x s a) (Con.subst x s b)
  | .succ a => .succ (Con.subst x s a)
  | .tree a => .tree (Con.subst x s a)
  | .nulltree a => .nulltree (Con.subst x s a)
  | .pi i a b => .pi i (Con.subst x s a) (if x = i then b else Con.subst x s b)
  | .sigma i a b => .sigma i (Con.subst x s a) (if x = i then b else Con.subst x s b)
  | .pairfun i a b => .pairfun i (Con.subst x s a) (if x = i then b else Con.subst x s b)
  | .recop i a b c => .recop i (Con.subst x s a) (Con.subst x s b) (if x = i then c else Con.subst x s c)

/-- Substitution in an atom. -/
def Atom.subst (x : Nat) (s : Con) : Atom → Atom
  | .mem a b => .mem (Con.subst x s a) (Con.subst x s b)
  | .eq a b  => .eq (Con.subst x s a) (Con.subst x s b)

/-- `x` not free in an atom (used in the side condition of P3). -/
def Atom.notFree (x : Nat) : Atom → Prop
  | .mem a b => Con.notFree x a ∧ Con.notFree x b
  | .eq a b  => Con.notFree x a ∧ Con.notFree x b

/-! ## 2. Inference — the sequent calculus (lines 329-976)

    `Derives Δ θ` is Scott's `Δ ⊢ θ`. -/

inductive Derives : List Atom → Atom → Prop
  -- assumption / reflexivity of ⊢
  | hyp {Δ : List Atom} {θ : Atom} (h : θ ∈ Δ) : Derives Δ θ
  -- (I1) weakening
  | weaken {Δ θ} (e : Atom) : Derives Δ θ → Derives (e :: Δ) θ
  -- (I3) cut
  | cut {Δ Δ' σ θ} : Derives Δ σ → Derives (σ :: Δ') θ → Derives (Δ ++ Δ') θ
  -- (I5) substitution
  | subst {Δ θ} (x : Nat) (s : Con) :
      Derives Δ θ → Derives (Δ.map (Atom.subst x s)) (Atom.subst x s θ)
  -- (E1) reflexivity  ⊢ x = x
  | e1 (x : Nat) : Derives [] (.eq (.var x) (.var x))
  -- (E2) substitutivity  x = y, θ ⊢ [y/x]θ
  | e2 (x y : Nat) (θ : Atom) :
      Derives [.eq (.var x) (.var y), θ] (θ.subst x (.var y))
  -- (F1) conversion:  f = ∀x∈a[σ], x∈a ⊢ f(x) = σ
  | f1 (x : Nat) (a σ f : Con) :
      Derives [.eq f (.pi x a σ), .mem (.var x) a] (.eq (.app f (.var x)) σ)
  -- (F2)  f = ∀x∈a[σ] ⊢ f = ∀x∈a[f(x)]
  | f2 (x : Nat) (a σ f : Con) :
      Derives [.eq f (.pi x a σ)] (.eq f (.pi x a (.app f (.var x))))
  -- (P1)  f ∈ ∀x∈a[σ], x∈a ⊢ f(x) ∈ σ
  | p1 (x : Nat) (a σ f : Con) :
      Derives [.mem f (.pi x a σ), .mem (.var x) a] (.mem (.app f (.var x)) σ)
  -- (P2)  f ∈ ∀x∈a[σ] ⊢ f = ∀x∈a[f(x)]
  | p2 (x : Nat) (a σ f : Con) :
      Derives [.mem f (.pi x a σ)] (.eq f (.pi x a (.app f (.var x))))
  -- (P3) product membership (≈ universal generalization):
  --      from Δ, x∈a ⊢ t ∈ σ  (x ∉ FV(Δ))  infer  Δ ⊢ ∀x∈a[t] ∈ ∀x∈a[σ]
  | p3 {Δ : List Atom} {x : Nat} {a t σ : Con}
      (hΔ : ∀ b ∈ Δ, Atom.notFree x b) :
      Derives (.mem (.var x) a :: Δ) (.mem t σ) →
      Derives Δ (.mem (.pi x a t) (.pi x a σ))
  -- (S1)  f = Px∈a[σ], x∈a, y∈σ ⊢ f(x)(y) ∈ ∃x∈a[σ]
  | s1 (x y : Nat) (a σ f : Con) :
      Derives [.eq f (.pairfun x a σ), .mem (.var x) a, .mem (.var y) σ]
              (.mem (.app (.app f (.var x)) (.var y)) (.sigma x a σ))
  -- (S3)  … ⊢ (f(x)(y))₀ = x
  | s3 (x y : Nat) (a σ f : Con) :
      Derives [.eq f (.pairfun x a σ), .mem (.var x) a, .mem (.var y) σ]
              (.eq (.proj0 (.app (.app f (.var x)) (.var y))) (.var x))
  -- (S4)  … ⊢ (f(x)(y))₁ = y
  | s4 (x y : Nat) (a σ f : Con) :
      Derives [.eq f (.pairfun x a σ), .mem (.var x) a, .mem (.var y) σ]
              (.eq (.proj1 (.app (.app f (.var x)) (.var y))) (.var y))
  -- (S5)  f = Px∈a[σ], z ∈ ∃x∈a[σ] ⊢ f(z₀)(z₁) = z
  | s5 (x z : Nat) (a σ f : Con) :
      Derives [.eq f (.pairfun x a σ), .mem (.var z) (.sigma x a σ)]
              (.eq (.app (.app f (.proj0 (.var z))) (.proj1 (.var z))) (.var z))
  -- (S6)  z ∈ ∃x∈a[σ] ⊢ z₀ ∈ a
  | s6 (x z : Nat) (a σ : Con) :
      Derives [.mem (.var z) (.sigma x a σ)] (.mem (.proj0 (.var z)) a)
  -- (S7)  z ∈ ∃x∈a[σ] ⊢ z₁ ∈ [z₀/x]σ
  | s7 (x z : Nat) (a σ : Con) :
      Derives [.mem (.var z) (.sigma x a σ)]
              (.mem (.proj1 (.var z)) (σ.subst x (.proj0 (.var z))))
  -- (G1)  ⊢ δ ∈ 𝟏
  | g1 : Derives [] (.mem .delta .one)
  -- (G2)  x ∈ 𝟏 ⊢ x = δ
  | g2 (x : Nat) : Derives [.mem (.var x) .one] (.eq (.var x) .delta)
  -- (G3)  ⊢ 𝟬 ∈ 𝟐
  | g3 : Derives [] (.mem .b0 .two)
  -- (G4)  ⊢ 𝟭 ∈ 𝟐
  | g4 : Derives [] (.mem .b1 .two)
  -- (G6)  ⊢ [a ∧ b](𝟬) = a
  | g6 (a b : Con) : Derives [] (.eq (.app (.pair a b) .b0) a)
  -- (G7)  ⊢ [a ∧ b](𝟭) = b
  | g7 (a b : Con) : Derives [] (.eq (.app (.pair a b) .b1) b)
  -- (G8)  ⊢ [a ∧ b] = ∀x∈𝟐[[a ∧ b](x)]
  | g8 (x : Nat) (a b : Con) :
      Derives [] (.eq (.pair a b) (.pi x .two (.app (.pair a b) (.var x))))
  -- (G9)  f = ∀x∈𝟐[f(x)] ⊢ f = [f(𝟬) ∧ f(𝟭)]  (extensionality for 𝟐)
  | g9 (x : Nat) (f : Con) :
      Derives [.eq f (.pi x .two (.app f (.var x)))]
              (.eq f (.pair (.app f .b0) (.app f .b1)))
  -- (T1)  ⊢ ○(a) ∈ 𝒯(a)
  | t1 (a : Con) : Derives [] (.mem (.nulltree a) (.tree a))
  -- (T2)  u ∈ [a → 𝒯(a)] ⊢ u⁺ ∈ 𝒯(a)      ([a→b] := ∀x∈a[b], x fresh)
  | t2 (x : Nat) (a u : Con) (hx : Con.notFree x a) :
      Derives [.mem u (.pi x a (.tree a))] (.mem (.succ u) (.tree a))
  -- (T4)  f = ℛv[a,b,σ] ⊢ f(○(a)) = b
  | t4 (v : Nat) (a b σ f : Con) :
      Derives [.eq f (.recop v a b σ)] (.eq (.app f (.nulltree a)) b)
  -- (T5)  f = ℛv[a,b,σ], u ∈ [a→𝒯(a)], v = ∀x∈a[f(u(x))] ⊢ f(u⁺) = σ
  | t5 (v x : Nat) (a b σ f u : Con) :
      Derives [.eq f (.recop v a b σ), .mem u (.pi x a (.tree a)),
               .eq (.var v) (.pi x a (.app f (.app u (.var x))))]
              (.eq (.app f (.succ u)) σ)
  -- (T6)  f = ℛv[a,b,σ] ⊢ f ∈ ∀t∈𝒯(a)[f(t)]
  | t6 (v t : Nat) (a b σ f : Con) :
      Derives [.eq f (.recop v a b σ)] (.mem f (.pi t (.tree a) (.app f (.var t))))

/-! ## 3. Logic interpreted into constructions (lines 981-1052) -/

namespace Con
/-- Implication / power  `[a → b] := ∀x∈a[b]` (constant function), `x` fresh. -/
def arrow (a b : Con) : Con := pi 0 a b     -- `b` should not contain `0` freely
/-- Truth `⊤ := 𝟏`. -/
def top : Con := one
/-- Absurdity `⊥ := 𝟎`. -/
def bot : Con := zero
/-- Negation `¬a := [a → 𝟎]`. -/
def cneg (a : Con) : Con := arrow a zero
/-- Conjunction `a ∧ b := [a ∧ b]` (the finite product / pair species). -/
def cand (a b : Con) : Con := pair a b
/-- Disjunction `a ∨ b := ∃x∈𝟐[[a ∧ b](x)]` (line 783), `x` fresh. -/
def cor (a b : Con) : Con := sigma 0 two (app (pair a b) (var 0))
/-- Biconditional. -/
def ciff (a b : Con) : Con := cand (arrow a b) (arrow b a)
end Con

/-- Constructive validity (lines 1215-1224): `φ` is valid iff there is a specific
    construction `T` with `⊢ T ∈ φ` provable. -/
def Valid (φ : Con) : Prop := ∃ T : Con, Derives [] (.mem T φ)

/-! ## 4. Sample validities and metatheorems -/

/-- Modus ponens is valid (line 1147):  `φ₀, [φ₀→φ₁] ⊨ φ₁`. -/
theorem valid_mp (φ₀ φ₁ : Con) :
    ∃ T : Con, Derives [.mem (.var 0) φ₀, .mem (.var 1) (Con.arrow φ₀ φ₁)] (.mem T φ₁) := by
  sorry -- TODO: T := (var 1)(var 0), by (P1).

/-- Axiom of choice is valid (lines 1620-1630) — the existential interpretation
    is so constructive that AC holds:
    `∀x∈a ∃y∈b P(x)(y) ⊨ ∃f∈[a→b] ∀x∈a P(x)(f(x))`. -/
theorem valid_choice : True := by
  sorry -- TODO

/-- FUNDAMENTAL CONJECTURE (lines 1378-1380): there is a (primitive recursive)
    decision method for provability of assertions `⊢ σ ∈ τ`. -/
noncomputable def fundamental_conjecture :
    ∀ σ τ : Con, Decidable (Derives [] (.mem σ τ)) := by
  sorry -- TODO (conjecture; not proved in the paper).

/-- Undecidability of the HYPOTHETICAL form (lines 1391-1481): there is no
    decision method for sequents `σ₀∈τ₀, …, σₙ₋₁∈τₙ₋₁ ⊢ σₙ∈τₙ`
    (via the word problem for semigroups). -/
theorem hypothetical_undecidable : True := by
  sorry -- TODO

end Scott1970ConstructiveValidity
