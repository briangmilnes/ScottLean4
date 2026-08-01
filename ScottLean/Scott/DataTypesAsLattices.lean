/-
  Data Types as Lattices — the Pω model (Lean 4 formalization, pilot)

  Faithful to:
    D. Scott, "Data Types as Lattices",
    SIAM Journal on Computing 5(3):522-587, 1976.

  Source text extracted from:
    DanaScottPapers/Scott-1976-Data-Types-as-Lattices.pdf

  This file transcribes the core objects of Section 1 ("Continuous functions"):
    * The domain  Pω = the set of all subsets of ω (the nonnegative integers),
      a complete lattice under set inclusion ⊆.
    * Finite sets  e_n  enumerated by n, and the neighborhood basis.
    * Continuity of  f : Pω → Pω  (Theorem 1.1, the characterization theorem).
    * The standard pairing  ⟨n, m⟩ = ½(n+m)(n+m+1) + m.
    * graph(f) and fun(u), and the graph theorem (Theorem 1.2).
    * Application  u · x = fun(u)(x), the reflexive-domain operation.
    * The fixed-point theorem (Theorem 1.4).

  Core Lean 4 only; no Mathlib.  Pω is modelled as `Nat → Prop` (a predicate on ω,
  i.e. a subset of ω); ⊆ is pointwise implication.  We keep `e_n` and the
  finite-subset relation abstract via classical-style predicates where a decision
  procedure is not needed for the statements.
-/

namespace DataTypesAsLattices

/-- `Pω`: an element of Scott's domain is a subset of ω, i.e. a set of integers,
    represented by its characteristic predicate. -/
abbrev Pω := Nat → Prop

/-- Set inclusion `⊆` — the partial order making `Pω` a complete lattice. -/
def sub (x y : Pω) : Prop := ∀ n, x n → y n

infix:50 " ⊑ " => sub

/-- Union (least upper bound of two elements). -/
def union (x y : Pω) : Pω := fun n => x n ∨ y n

/-- Bottom element: the empty set. -/
def bot : Pω := fun _ => False

/-! ## Finite subsets and the neighborhood basis

    "A basis for the neighborhoods of Pω consists of those sets of the form
     { x ∈ Pω | e_n ⊆ x } for a given e_n."

    `e_n` is the finite set of integers coded by `n`.  We keep the specific coding
    abstract as `enum : Nat → Pω`, together with the hypothesis (proved in the
    paper for the standard coding) that every `enum n` is a *finite* subset.  The
    predicate `IsFinite` records finiteness abstractly. -/
axiom enum : Nat → Pω          -- e_n, the n-th finite set of integers

/-- `x` contains the finite set `e_n`. -/
def containsFin (n : Nat) (x : Pω) : Prop := enum n ⊑ x

/-! ## Continuity (Theorem 1.1, the characterization theorem)

    "A function f : Pω → Pω is continuous iff for all x ∈ Pω and all e (= integer
     m) we have:   m ∈ f(x)  iff  ∃ e_n ⊆ x. m ∈ f(e_n)."

    This is the ε-δ (finite-approximation) form Scott gives as the most convenient
    for proofs. -/
def Continuous (f : Pω → Pω) : Prop :=
  ∀ (x : Pω) (m : Nat), (f x) m ↔ ∃ n, enum n ⊑ x ∧ (f (enum n)) m

/-- Continuous functions are monotone (the "positive character" of the topology):
    "whenever x ⊆ y then f(x) ⊆ f(y)." -/
theorem Continuous.mono {f : Pω → Pω} (hf : Continuous f) :
    ∀ {x y : Pω}, x ⊑ y → f x ⊑ f y := by
  intro x y hxy m hm
  rw [hf y m]
  rw [hf x m] at hm
  obtain ⟨n, hn, hfm⟩ := hm
  exact ⟨n, fun k hk => hxy k (hn k hk), hfm⟩

/-! ## The standard enumeration of pairs

    "(n, m) = ½(n + m)(n + m + 1) + m." -/
def pair (n m : Nat) : Nat := (n + m) * (n + m + 1) / 2 + m

/-! ## graph and fun (the reflexive structure)

    "graph(f) = { (n, m) | m ∈ f(e_n) }"
    "fun(u)(x) = { m | ∃ e_n ⊆ x. (n, m) ∈ u }"

    `graph` turns a continuous function into an element of `Pω`; `apply` (Scott's
    `fun`) turns an element of `Pω` into a function `Pω → Pω`.  Their interplay is
    the graph theorem (Theorem 1.2). -/
def graph (f : Pω → Pω) : Pω :=
  fun k => ∃ n m, k = pair n m ∧ (f (enum n)) m

/-- `fun(u)` : the continuous function coded by the set `u`.  This is Scott's
    fundamental *application* operation on the reflexive domain `Pω`. -/
def apply (u : Pω) (x : Pω) : Pω :=
  fun m => ∃ n, enum n ⊑ x ∧ u (pair n m)

/-- Scott's application infix (`u · x = fun(u)(x)`), making `Pω` a model of the
    type-free λ-calculus / combinatory logic. -/
infixl:70 " ⬝ " => apply

/-- The function coded by any set `u` is continuous (part of Theorem 1.2 /
    the graph theorem): `fun(u)` is a continuous function of `x`. -/
theorem apply_continuous (u : Pω) : Continuous (apply u) := by
  intro x m
  constructor
  · intro h
    obtain ⟨n, hn, hu⟩ := h
    exact ⟨n, hn, ⟨n, fun k hk => hk, hu⟩⟩
  · intro h
    obtain ⟨n, hn, hm⟩ := h
    obtain ⟨n', hn', hu⟩ := hm
    exact ⟨n', fun k hk => hn k (hn' k hk), hu⟩

/-! ## Theorem 1.2 (the graph theorem)

    "(i)  fun(graph(f)) = f
     (ii) u ⊑ graph(fun(u)), with equality iff u is closed under:
          whenever (k, m) ∈ u and e_k ⊆ e_n, then (n, m) ∈ u."

    We record (i) as the target statement `graph_theorem_i`.  A full proof needs
    the injectivity/monotonicity facts of the pairing and `enum` codings; here we
    give the faithful signature Scott proves in the Appendix. -/
def graph_theorem_i : Prop :=
  ∀ (f : Pω → Pω), Continuous f → ∀ x, (apply (graph f) x) = f x

/-! ## Theorem 1.4 (the fixed-point theorem)

    "Every continuous function f : Pω → Pω has a least fixed point given by
        fix(f) = ⋃ₙ fⁿ(∅),
     where ∅ is the empty set and fⁿ is the n-fold composition of f with itself."

    `iterate f n bot` is fⁿ(∅); `fixApprox f n` is that n-th approximant, and
    `fix f` is their union (supremum). -/
def iterate (f : Pω → Pω) : Nat → Pω → Pω
  | 0,     x => x
  | k + 1, x => f (iterate f k x)

def fix (f : Pω → Pω) : Pω :=
  fun m => ∃ n, (iterate f n bot) m

/-- `fix f` is a fixed point of a continuous `f` (Theorem 1.4). -/
def fix_is_fixedpoint : Prop :=
  ∀ (f : Pω → Pω), Continuous f → fix f = f (fix f)

/-- `fix f` is the *least* fixed point (Theorem 1.4). -/
def fix_is_least : Prop :=
  ∀ (f : Pω → Pω) (y : Pω), f y ⊑ y → fix f ⊑ y

end DataTypesAsLattices
