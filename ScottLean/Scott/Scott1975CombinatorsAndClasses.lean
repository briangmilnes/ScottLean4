/-
  Combinators and Classes (Lean 4 formalization, faithful skeleton)

  Faithful to:
    Dana Scott, "Combinators and Classes", 1975.
    (In: C. Böhm (ed.), Lambda-Calculus and Computer Science Theory,
     Lecture Notes in Computer Science 37, Springer, 1975.)

  Source text extracted from:
    DanaScottPapers/Scott-1975-Combinators-and-Classes.txt

  Auto-generated faithful skeleton.  Core Lean 4 only; no Mathlib.

  The paper studies models of the (extensional) lambda-calculus and asks how
  *class abstraction* relates to *lambda-abstraction*.  Its running technical
  vehicle is a combinatory / applicative structure with the pure combinators,
  on top of which Scott grafts a transfinite truth definition so that
  "lambda-abstraction in conjunction with the truth definition works just like
  class abstraction" -- with membership `a ∈ b` interpreted as functional
  application `b(a)`.

  This file transcribes the algebraic core that everything else rests on:

    * A `CombinatoryAlgebra`: an applicative structure with constants `S`, `K`
      satisfying `K x y = x` and `S x y z = (x z)(y z)`.
    * The derived combinators `I` and `B`, with proofs of their laws
      (`I x = x`, `B f g x = f (g x)`) from the axioms.
    * Single-variable combinatory completeness (bracket abstraction), proved
      in full: every one-variable applicative term is represented by an element
      of the algebra.
    * The class layer (`ClassModel`): the §2 truth definition abstracted to its
      characteristic biconditionals (Scott's "Lemma"), membership-as-application
      `a ∈ b = b(a)`, the class-abstraction principle, and a full proof of
      Scott's Russell truth-value gap (`r ∈ r` is neither true nor false).

  Deep results are left as `-- TODO`/`sorry` or as documented remarks: the
  existence of the transfinite truth predicate (§2), general (multi-variable)
  combinatory completeness, the universe `V` and its closure properties, and the
  functionality combinators `F`, `Π`, `Z` (§4).
-/

namespace Scott1975

/-! ## Applicative structure with combinators (§ "The Laws of λ-Calculus")

    Scott works in "any non-trivial model for (α),(β),(ξ)".  For the purely
    combinatory core it suffices to record an applicative structure carrying the
    Schönfinkel/Curry constants `S` and `K` with their defining identities.

    "the purpose of the combinators is to analyze the notion of functional
     dependence by producing a few basic combinators from which the others could
     be explicitly defined."

    A `CombinatoryAlgebra` bundles a carrier type, a binary application `app`,
    the constants `S K : Carrier`, and the two defining equations
        K x y      = x
        S x y z    = (x z)(y z)
    as universally quantified `Prop`-valued fields. -/
structure CombinatoryAlgebra where
  Carrier : Type
  app  : Carrier → Carrier → Carrier
  K    : Carrier
  S    : Carrier
  /-- `K x y = x`. -/
  K_ax : ∀ x y : Carrier, app (app K x) y = x
  /-- `S x y z = (x z)(y z)`. -/
  S_ax : ∀ x y z : Carrier, app (app (app S x) y) z = app (app x z) (app y z)

/-! ## The identity combinator `I`

    The standard definition `I = S K K`.  Its law `I x = x` is a genuine
    equational consequence of the two axioms, so we prove it. -/

/-- `I = S K K`. -/
def CombinatoryAlgebra.I (A : CombinatoryAlgebra) : A.Carrier :=
  A.app (A.app A.S A.K) A.K

/-- `I x = x`, proved from the `S` and `K` axioms:
    `S K K x = (K x)(K x) = x`. -/
theorem CombinatoryAlgebra.app_I (A : CombinatoryAlgebra) (x : A.Carrier) :
    A.app A.I x = x := by
  unfold CombinatoryAlgebra.I
  simp only [A.S_ax, A.K_ax]

/-- `K` really is the constant/cancellation combinator (this is exactly `K_ax`,
    recorded here under the applicative reading `K x y = x`). -/
theorem CombinatoryAlgebra.app_K (A : CombinatoryAlgebra) (x y : A.Carrier) :
    A.app (A.app A.K x) y = x :=
  A.K_ax x y

/-! ## The composition combinator `B`

    `B = S (K S) K`, satisfying `B f g x = f (g x)`.  Again a real consequence
    of the axioms. -/

/-- `B = S (K S) K`. -/
def CombinatoryAlgebra.B (A : CombinatoryAlgebra) : A.Carrier :=
  A.app (A.app A.S (A.app A.K A.S)) A.K

/-- `B f g x = f (g x)`. -/
theorem CombinatoryAlgebra.app_B (A : CombinatoryAlgebra) (f g x : A.Carrier) :
    A.app (A.app (A.app A.B f) g) x = A.app f (A.app g x) := by
  unfold CombinatoryAlgebra.B
  simp only [A.S_ax, A.K_ax]

/-! ## Combinatory completeness (bracket abstraction)

    "a foundation for logic ... an analysis of substitution and the behaviour of
     variables."

    We formalize one-variable combinatory completeness.  A `CTerm` is an
    applicative term built from a single variable, constants drawn from the
    algebra, and application.  `eval` gives its value once the variable is fixed;
    `abstr` performs bracket abstraction `[x] t`.  The theorem `abstr_spec` says
    the abstracted element applied to any argument reproduces `eval`, i.e. every
    one-variable term is *represented* by an element of the algebra.  This is a
    real proof from the `S`,`K` axioms. -/

/-- One-variable applicative terms over a carrier `α`.
    `var` is the (single) abstraction variable. -/
inductive CTerm (α : Type) where
  | var   : CTerm α
  | const : α → CTerm α
  | ap    : CTerm α → CTerm α → CTerm α

/-- Value of a term when the variable is instantiated to `v`. -/
def CTerm.eval {A : CombinatoryAlgebra} : CTerm A.Carrier → A.Carrier → A.Carrier
  | .var,      v => v
  | .const c,  _ => c
  | .ap t u,   v => A.app (t.eval v) (u.eval v)

/-- Bracket abstraction `[x] t`, the standard `I`/`K`/`S` recursion:
        `[x] x        = I`
        `[x] (const c)= K c`
        `[x] (t u)    = S ([x] t) ([x] u)`. -/
def CTerm.abstr {A : CombinatoryAlgebra} : CTerm A.Carrier → A.Carrier
  | .var      => A.I
  | .const c  => A.app A.K c
  | .ap t u   => A.app (A.app A.S t.abstr) u.abstr

/-- Combinatory completeness (one variable): the abstracted element applied to
    `v` computes the term's value.  Proof by induction on the term using the
    `S`,`K` axioms and `app_I`. -/
theorem CTerm.abstr_spec {A : CombinatoryAlgebra} :
    ∀ (t : CTerm A.Carrier) (v : A.Carrier), A.app t.abstr v = t.eval v := by
  intro t
  induction t with
  | var =>
      intro v
      simp only [CTerm.abstr, CTerm.eval, CombinatoryAlgebra.app_I]
  | const c =>
      intro v
      simp only [CTerm.abstr, CTerm.eval, A.K_ax]
  | ap t u iht ihu =>
      intro v
      simp only [CTerm.abstr, CTerm.eval, A.S_ax, iht, ihu]

/-! General (multi-variable) combinatory completeness / the abstraction theorem
    for arbitrary applicative polynomials.  The one-variable case above is the
    tractable core; the general statement is left as a TODO.

    TODO: general combinatory completeness (iterated bracket abstraction). -/

/-! ## Classes: the truth definition and membership (§2)

    "λ-abstraction in conjunction with the truth definition works just like class
     abstraction.  All we have to do is to interpret membership by functional
     application."

    Scott builds two subsets `𝒯` (true) and `ℱ` (false) of the model as the
    least fixed point of a monotone, transfinite inductive definition, and proves
    they are disjoint (no formula is both true and false).  We *do not* reconstruct
    that transfinite construction here; instead we abstract a `ClassModel` as a
    combinatory algebra together with the truth/falsity predicates and the
    characteristic biconditionals of Scott's "Lemma" (§2) plus disjointness --
    exactly the properties his construction is proved to enjoy.

    The primitive formula constructors are represented as operations:
        `Eqf a b`      for   `a = b`      (Scott: `<0,a,b>`)
        `Forallf φ`    for   `∀x. φ`      (Scott: `<1, λx.φ>`)
        `Neg u`        for   `¬ u`        (Scott: `<2,u>`)
        `Andf a b`     for   `a ∧ b`      (Scott: `<3,a,b>`)
    together with the defined `Orf` and `Existsf`.  (Scott's implication `<4>`
    is omitted here; the source's truth clause for it is not legible.)
    Membership is *not* primitive: `a ∈ b = b(a)`. -/
structure ClassModel where
  A : CombinatoryAlgebra
  /-- The subset `𝒯` of "true" elements/formulas. -/
  Tru : A.Carrier → Prop
  /-- The subset `ℱ` of "false" elements/formulas. -/
  Fls : A.Carrier → Prop
  -- Primitive formula constructors.
  Eqf     : A.Carrier → A.Carrier → A.Carrier
  Neg     : A.Carrier → A.Carrier
  Andf    : A.Carrier → A.Carrier → A.Carrier
  Orf     : A.Carrier → A.Carrier → A.Carrier
  Forallf : (A.Carrier → A.Carrier) → A.Carrier
  Existsf : (A.Carrier → A.Carrier) → A.Carrier
  /-- Negation is itself a combinator of the model (connectives as combinators):
      `neg u = negComb · u`. -/
  negComb : A.Carrier
  neg_app : ∀ u, A.app negComb u = Neg u
  -- §2: `𝒯` and `ℱ` are disjoint -- "no formula can be both true and false".
  disjoint : ∀ u, ¬ (Tru u ∧ Fls u)
  -- Scott's "Lemma": the characteristic biconditionals of the truth definition.
  tru_eq     : ∀ a b, Tru (Eqf a b) ↔ a = b
  fls_eq     : ∀ a b, Fls (Eqf a b) ↔ a ≠ b
  tru_neg    : ∀ u, Tru (Neg u) ↔ Fls u
  fls_neg    : ∀ u, Fls (Neg u) ↔ Tru u
  tru_and    : ∀ a b, Tru (Andf a b) ↔ Tru a ∧ Tru b
  fls_and    : ∀ a b, Fls (Andf a b) ↔ Fls a ∨ Fls b
  tru_or     : ∀ a b, Tru (Orf a b) ↔ Tru a ∨ Tru b
  fls_or     : ∀ a b, Fls (Orf a b) ↔ Fls a ∧ Fls b
  tru_forall : ∀ φ, Tru (Forallf φ) ↔ ∀ a, Tru (φ a)
  fls_forall : ∀ φ, Fls (Forallf φ) ↔ ∃ a, Fls (φ a)
  tru_exists : ∀ φ, Tru (Existsf φ) ↔ ∃ a, Tru (φ a)
  fls_exists : ∀ φ, Fls (Existsf φ) ↔ ∀ a, Fls (φ a)

/-- Membership interpreted by functional application: `a ∈ b = b(a)`. -/
def ClassModel.mem (M : ClassModel) (a b : M.A.Carrier) : M.A.Carrier :=
  M.A.app b a

/-- Scott's Lemma clause for membership is definitional:
    `𝒯 (a ∈ b)  iff  𝒯 (b a)`. -/
theorem ClassModel.tru_mem (M : ClassModel) (a b : M.A.Carrier) :
    M.Tru (M.mem a b) ↔ M.Tru (M.A.app b a) := Iff.rfl

/-- Class abstraction via λ works like class abstraction:
    if `c` represents the predicate `φ` (i.e. `c x = φ x` for all `x`), then
    `𝒯 (a ∈ c) iff 𝒯 (φ a)`.  This is Scott's
    "`𝒯 a ∈ λx.φ  iff  𝒯 φ[a/x]`". -/
theorem ClassModel.class_abstraction (M : ClassModel)
    (φ : M.A.Carrier → M.A.Carrier) (c : M.A.Carrier)
    (h : ∀ x, M.A.app c x = φ x) (a : M.A.Carrier) :
    M.Tru (M.mem a c) ↔ M.Tru (φ a) := by
  unfold ClassModel.mem
  rw [h a]

/-! ### The Russell truth-value gap

    "r = λx. ¬ x ∈ x ... r ∈ r has no truth value."

    We realize Russell's abstract as an element `russell` of the algebra via
    bracket abstraction of `¬ (x ∈ x)`, then prove that `r ∈ r` is neither true
    nor false -- forced by disjointness together with `𝒯(¬u) ↔ ℱ u`. -/

/-- Russell's class `r = λx. ¬ (x ∈ x)`, realized as an algebra element. -/
def ClassModel.russell (M : ClassModel) : M.A.Carrier :=
  (CTerm.ap (CTerm.const M.negComb) (CTerm.ap CTerm.var CTerm.var)).abstr

/-- The defining reduction of Russell's class: `r x = ¬ (x ∈ x)`. -/
theorem ClassModel.russell_app (M : ClassModel) (x : M.A.Carrier) :
    M.A.app M.russell x = M.Neg (M.A.app x x) := by
  unfold ClassModel.russell
  rw [CTerm.abstr_spec]
  simp only [CTerm.eval]
  rw [M.neg_app]

/-- Scott's Russell truth-value gap: `r ∈ r` is neither true nor false.
    "true and false are exclusive; hence, `r ∈ r` has no truth value." -/
theorem ClassModel.russell_gap (M : ClassModel) :
    ¬ M.Tru (M.mem M.russell M.russell) ∧ ¬ M.Fls (M.mem M.russell M.russell) := by
  have hrr : M.A.app M.russell M.russell
      = M.Neg (M.A.app M.russell M.russell) := M.russell_app M.russell
  -- `mem r r` is definitionally `app r r = ¬ (app r r)`, so truth flips to falsity.
  have key : M.Tru (M.A.app M.russell M.russell)
      ↔ M.Fls (M.A.app M.russell M.russell) := by
    constructor
    · intro h
      rw [hrr] at h
      exact (M.tru_neg _).mp h
    · intro h
      rw [hrr]
      exact (M.tru_neg _).mpr h
  refine ⟨?_, ?_⟩
  · intro h; exact M.disjoint _ ⟨h, key.mp h⟩
  · intro h; exact M.disjoint _ ⟨key.mpr h, h⟩

/-! ## Further class theory (§4): documented as TODO

    The paper goes on to the universe of "definite" classes and the type/
    functionality combinators.  These rest on the transfinite truth definition
    and are recorded here only as statements to be developed.

        V   = λa. ∀x [ x ∈ a  ∨  ¬ x ∈ a ]          (the semi-type of all types)
        Fab = λf. ∀x [ ¬ x ∈ a  ∨  f(x) ∈ b ]       (function space)
        Πab = λf. ∀x [ ¬ x ∈ a  ∨  f(x) ∈ b(x) ]    (cartesian product)
        Zab = λu. ∃x ∃y [ x ∈ a ∧ y ∈ b(x) ∧ u = ⟨x,y⟩ ]

    with closure laws such as `a ∈ V, b ∈ V ⊢ Fab ∈ V` and the functionality
    laws for `I`, `K`, `S` (e.g. `a ∈ V ⊢ I ∈ F a a`). -/
-- TODO: existence of the transfinite truth predicate (§2 fixed point).
-- TODO: the universe combinator `V`, definiteness, and closure properties (§4).
-- TODO: the functionality combinators `F`, `Π`, `Z` and their rules (§4).

end Scott1975
