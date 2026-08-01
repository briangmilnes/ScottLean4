/-
  Algebras of Sets Binumerable in Complete Extensions of Arithmetic
  (Lean 4 faithful skeleton)

  Faithful to:
    Dana Scott, "Algebras of Sets Binumerable in Complete Extensions of
    Arithmetic", in: Recursive Function Theory (Proc. Sympos. Pure Math. V),
    Amer. Math. Soc., 1962, pp. 117-121.

  Source text extracted from:
    DanaScottPapers/Scott-1962-Algebras-of-Sets-Binumerable.txt

  This is an auto-generated faithful skeleton.  It transcribes the core formal
  objects of the paper, which characterizes exactly which denumerable Boolean
  algebras of sets arise as the binumerable sets of a complete extension of
  first-order arithmetic:

    * Complete (consistent) extensions `T` of Peano arithmetic `P`
      (a set of sentences, deductively closed, complete).
    * A set `S` of integers *numerable* in `T` (`n ∈ S ↔ B(n) ∈ T`) and
      *binumerable* (both `S` and its complement numerable); `𝔅[T]`, the Boolean
      algebra of binumerable sets, and `𝔉[T]` the class of their characteristic
      functions in `2^ω` (p. 117-118).
    * Finite {0,1}-sequences `2^n`, restriction, the coding `‖s‖`; *trees* as
      restriction-closed sets of finite sequences; *paths*; a tree *recursive
      within* a class `H ⊆ 2^ω` (p. 118).
    * MAIN THEOREM (p. 118): `H = 𝔉[T]` for some complete extension `T` iff
      (i) `H` is a denumerable subclass of `2^ω`, and
      (ii) every infinite tree recursive within `H` has a path belonging to `H`.
    * The independence Lemma (p. 118-119) used for the sufficiency direction.

  Core Lean 4 only; no Mathlib.  Recursiveness and provability are stated
  abstractly.  Deep theorems are `sorry` with `-- TODO`.
-/

namespace Scott1962

/-! ## Finite {0,1}-sequences, trees, paths -/

/-- A point of `2^ω`: an infinite binary sequence (a set of integers via its
    characteristic function). -/
abbrev Point := Nat → Bool

/-- A finite {0,1}-sequence of length `n`: an element of `2^n`. -/
abbrev FinSeq (n : Nat) := Fin n → Bool

/-- Restriction `f ↾ n` of an infinite sequence to `{0,…,n-1}`. -/
def restrict (f : Point) (n : Nat) : FinSeq n := fun i => f i.val

/-- A *tree* (p. 118): a set of finite sequences (of arbitrary lengths, packaged
    as dependent pairs `(n, s)`) closed under restriction — if `s ∈ 𝒯` has
    length `m` and `n ≤ m`, then `s ↾ n ∈ 𝒯`.  We represent membership by a
    predicate on `(n : Nat) × FinSeq n` and require restriction-closure. -/
structure Tree where
  mem        : (n : Nat) → FinSeq n → Prop
  restr_closed : ∀ (m : Nat) (s : FinSeq m) (n : Nat) (h : n ≤ m),
                   mem m s → mem n (fun i => s ⟨i.val, Nat.lt_of_lt_of_le i.isLt h⟩)

/-- A *path* of a tree (p. 118): an infinite sequence all of whose finite
    restrictions lie in the tree. -/
def Tree.IsPath (𝒯 : Tree) (f : Point) : Prop :=
  ∀ n, 𝒯.mem n (restrict f n)

/-- A tree is *infinite* if it has members of every length. -/
def Tree.Infinite (𝒯 : Tree) : Prop :=
  ∀ n, ∃ s : FinSeq n, 𝒯.mem n s

/-- Well-known fact (p. 118): every infinite tree has at least one path
    (König's lemma for the binary tree). -/
theorem infinite_tree_hasPath (𝒯 : Tree) (_h : 𝒯.Infinite) :
    ∃ f : Point, 𝒯.IsPath f := by
  sorry -- TODO König's lemma for the binary tree

/-- A tree is *recursive within* a class `H ⊆ 2^ω` (p. 118) if the set of codes
    `‖s‖` of its members is recursive in some finite number of functions drawn
    from `H`.  We keep recursiveness abstract via a relation
    `RecIn : Tree → (Fin k → Point) → Prop`. -/
structure Recursiveness where
  RecIn : {k : Nat} → Tree → (Fin k → Point) → Prop

/-- `𝒯` is recursive within `H` (there is a finite tuple of members of `H`
    relative to which `𝒯` is recursive). -/
def RecursiveWithin (rec : Recursiveness) (𝒯 : Tree) (H : Point → Prop) : Prop :=
  ∃ (k : Nat) (fs : Fin k → Point), (∀ i, H (fs i)) ∧ rec.RecIn 𝒯 fs

/-! ## Complete extensions of arithmetic and binumerable sets -/

/-- The formulas of first-order arithmetic with one free variable, abstractly,
    together with substitution of the `n`-th numeral `Δ_n`. -/
structure ArithLanguage where
  Sentence   : Type
  Formula1   : Type                          -- formulas with one free variable
  subst      : Formula1 → Nat → Sentence     -- B ↦ B(Δ_n)
  neg        : Formula1 → Formula1           -- ¬B(x)

/-- A *complete (consistent) extension* `T` of arithmetic (p. 117): a set of
    sentences, deductively closed and complete (for each sentence, it or an
    opposite belongs).  We abstract "opposite of a sentence" via `sneg`. -/
structure CompleteExtension (Lang : ArithLanguage) where
  mem        : Lang.Sentence → Prop
  sneg       : Lang.Sentence → Lang.Sentence
  complete   : ∀ A, mem A ∨ mem (sneg A)
  consistent : ∀ A, ¬ (mem A ∧ mem (sneg A))

/-- A set `S ⊆ ω` is *numerable* in `T` via `B` (p. 117): `n ∈ S ↔ B(Δ_n) ∈ T`. -/
def Numerable {Lang : ArithLanguage} (T : CompleteExtension Lang)
    (S : Nat → Prop) (B : Lang.Formula1) : Prop :=
  ∀ n, S n ↔ T.mem (Lang.subst B n)

/-- A set is *binumerable* in `T` (p. 117): it is numerable, and (via `¬B`) so is
    its complement.  For a complete `T` numerability already gives binumerability;
    we record the definition directly. -/
def Binumerable {Lang : ArithLanguage} (T : CompleteExtension Lang)
    (S : Nat → Prop) : Prop :=
  ∃ B : Lang.Formula1, Numerable T S B ∧ Numerable T (fun n => ¬ S n) (Lang.neg B)

/-- `𝔉[T]` (p. 118): the class of characteristic functions in `2^ω` of the sets
    binumerable in `T`. -/
def FClass {Lang : ArithLanguage} (T : CompleteExtension Lang) : Point → Prop :=
  fun f => Binumerable T (fun n => f n = true)

/-! ## The main theorem -/

/-- MAIN THEOREM (p. 118).  For a class `H ⊆ 2^ω` there exists a complete
    extension `T` of arithmetic with `H = 𝔉[T]` **iff**
      (i)  `H` is a denumerable subclass of `2^ω`, and
      (ii) every infinite tree recursive within `H` has a path belonging to `H`.

    `Denumerable H` is captured by a surjection `Nat → {f // H f}` (an
    enumeration of `H`). -/
theorem characterization
    (Lang : ArithLanguage) (rec : Recursiveness) (H : Point → Prop)
    (Denumerable : (Point → Prop) → Prop) :
    (∃ T : CompleteExtension Lang, ∀ f, H f ↔ FClass T f) ↔
      (Denumerable H ∧
       ∀ 𝒯 : Tree, 𝒯.Infinite → RecursiveWithin rec 𝒯 H →
          ∃ f, 𝒯.IsPath f ∧ H f) := by
  sorry -- TODO Main Theorem (both directions; sufficiency uses the independence Lemma)

/-- The independence Lemma (p. 118-119).  Given finitely many formulas
    `A₀,…,A_{k-1}` one can effectively find a formula `B(x)` independent of them:
    no consistent assumption about the instances of the `Aᵢ` decides any relation
    among the instances of `B`.  Stated as existence of such a `B` for every
    finite list of formulas. -/
theorem independence_lemma (Lang : ArithLanguage)
    (Independent : Lang.Formula1 → List Lang.Formula1 → Prop)
    (As : List Lang.Formula1) :
    ∃ B : Lang.Formula1, Independent B As := by
  sorry -- TODO Independence Lemma (effective construction of an independent formula)

end Scott1962
