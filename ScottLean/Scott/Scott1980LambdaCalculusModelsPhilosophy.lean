/-
  Lambda Calculus: Some Models, Some Philosophy (Lean 4 formalization, pilot)

  Auto-generated faithful skeleton of:
    D. Scott, "Lambda Calculus: Some Models, Some Philosophy",
    in: J. Barwise, H. J. Keisler and K. Kunen, eds., The Kleene Symposium,
    North-Holland Publishing Company (1980), pp. 223-265.

  Source text extracted from:
    DanaScottPapers/Scott-1980-Lambda-Calculus-Some-Models-Some-Philosophy.txt

  This file transcribes the core formal content:
    * The untyped λ-calculus of terms (de Bruijn indices) with β-reduction and
      conversion, and the standard combinators I, K, S, B and the paradoxical
      combinator Y.
    * The notion of a λ-MODEL as a *reflexive object*: a carrier `D` together
      with a retraction  D → [D → D],  i.e. maps  `Fun : D → (D → D)`  and
      `Graph : (D → D) → D`  satisfying the retraction law  `Fun ∘ Graph = id`.
      (Section 5 of the paper builds such a retraction as the limit `D∞` of the
      maps `D₀ = λX.X`, `D_{n+1} = λF λX. D_n(F(D_n(X)))`.)
    * The induced application, and a proof that `Fun/Graph` make the model into a
      combinatory algebra (the K- and S-identities are *proved* from the
      retraction law).
    * The interpretation of λ-terms in a model, with β-soundness stated as a
      theorem (interpretation-level β is proved; the full syntactic substitution
      lemma is left as a `sorry`/TODO).
    * Plotkin's / Scott's GRAPH MODEL Pω: the powerset of ℕ with application
      given by Scott's set-theoretic formula (2) of Section 3.
    * The Appendix's axiom list, recorded as a section comment.

  Core Lean 4 only; no Mathlib.

  Convention: throughout, `C` (⊆) is Scott's primitive; here we work with plain
  equality where the paper works up to conversion, and record the inclusion laws
  of the appendix as documentation.
-/

namespace Scott1980Lambda

/-! ## §1-3.  λ-terms (de Bruijn indices)

    Scott discusses application `X(Y)` and abstraction `λX. τ[X]` (Section 3,
    formulae (1),(2)).  We present the untyped λ-calculus syntactically with de
    Bruijn indices `Nat` for variables, so that `α`-conversion is definitional
    and the binder `lam` needs no variable name. -/
inductive Term where
  | var : Nat → Term            -- a de Bruijn index
  | app : Term → Term → Term    -- application  X(Y)
  | lam : Term → Term           -- abstraction  λ. τ
  deriving Repr, DecidableEq

/-- `shiftAbove c t` increments every free index `≥ c` in `t` by one.  Used to
    move a term underneath one extra binder without capture. -/
def shiftAbove : Nat → Term → Term
  | c, .var n => if c ≤ n then .var (n + 1) else .var n
  | c, .app t u => .app (shiftAbove c t) (shiftAbove c u)
  | c, .lam t => .lam (shiftAbove (c + 1) t)

/-- Capture-avoiding substitution `subst j s t` replaces the free index `j` in
    `t` by `s`, decrementing the free indices above `j` (as needed for β). -/
def subst : Nat → Term → Term → Term
  | j, s, .var n => if n = j then s else if j < n then .var (n - 1) else .var n
  | j, s, .app t u => .app (subst j s t) (subst j s u)
  | j, s, .lam t => .lam (subst (j + 1) (shiftAbove 0 s) t)

/-! ## §3.  β-reduction and conversion

    The fundamental law (β) of the paper (Section 3):
        `(λX. τ[X])(Y) = τ[Y]`.
    In de Bruijn form the redex `(λ. t) u` contracts to `t[0 := u]`. -/
inductive Step : Term → Term → Prop
  | beta (t u : Term) : Step (.app (.lam t) u) (subst 0 u t)
  | appL {t t' u : Term} : Step t t' → Step (.app t u) (.app t' u)
  | appR {t u u' : Term} : Step u u' → Step (.app t u) (.app t u')
  | under {t t' : Term} : Step t t' → Step (.lam t) (.lam t')

/-- Conversion `=` is the reflexive–symmetric–transitive closure of `Step`.
    (Church–Rosser, discussed historically in Section 1, would give it a normal
    form; not formalized here.) -/
inductive Conv : Term → Term → Prop
  | refl (t : Term) : Conv t t
  | fromStep {t u : Term} : Step t u → Conv t u
  | symm {t u : Term} : Conv t u → Conv u t
  | trans {t u v : Term} : Conv t u → Conv u v → Conv t v

/-! ## Standard combinators as λ-terms

    Church's `K` and `S` (Section 4, "we reduce all λ-definitions to the
    well-known combinators S and K"), together with `I`, `B` (Section 3,
    `B = λF λG λX. F(G(X))`) and the paradoxical combinator `Y` (Section 4). -/

/-- `I = λx. x`. -/
def I : Term := .lam (.var 0)

/-- `K = λx λy. x`  (Section 4). -/
def K : Term := .lam (.lam (.var 1))

/-- `S = λf λg λx. f x (g x)`  (Section 4, "S is the combinator for point-wise
    application of two functions", `S = λF λG λX. F(X)(G(X))`). -/
def S : Term :=
  .lam (.lam (.lam (.app (.app (.var 2) (.var 0)) (.app (.var 1) (.var 0)))))

/-- `B = λf λg λx. f (g x)`  (Section 3), composition. -/
def B : Term :=
  .lam (.lam (.lam (.app (.var 2) (.app (.var 1) (.var 0)))))

/-- Curry's paradoxical combinator `Y = λf. (λx. f (x x)) (λx. f (x x))`
    (Section 4, `Y(F) = F(Y(F))`). -/
def Y : Term :=
  .lam (.app (.lam (.app (.var 1) (.app (.var 0) (.var 0))))
             (.lam (.app (.var 1) (.app (.var 0) (.var 0)))))

/-! ## §5.  A λ-model as a reflexive object

    "Is there some (non-trivial) model in which the law (η) holds?  I gave an
     answer in 1969 ... the details (by 'retracts') as presented here are very
     much simpler."  (Section 5.)

    A λ-model is a *reflexive object* `D`: a carrier together with a retraction
    of the function space `[D → D]` onto `D`.  Concretely we bundle
        `Fun   : D → (D → D)`   (read an element as a function),
        `Graph : (D → D) → D`   (the "graph" of a function, formula (1)),
    subject to the retraction law  `Fun (Graph f) = f`.  This is exactly the
    condition that `D` be a reflexive object with `[D → D]` a retract; it makes
    every element denote a function and every (representable) function an
    element. -/
structure LambdaModel where
  /-- The carrier `D` of the model. -/
  D : Type
  /-- `Fun` reads an element of `D` as a function `D → D`. -/
  Fun : D → (D → D)
  /-- `Graph f` is the element of `D` representing the function `f`
      (Scott's `λX. f(X)`, formula (1) of Section 3). -/
  Graph : (D → D) → D
  /-- The retraction law  `Fun ∘ Graph = id`  on `[D → D]`.  This is the essence
      of a reflexive object / λ-model. -/
  Fun_Graph : ∀ f, Fun (Graph f) = f

/-- Application in the model:  `x · y = Fun x y`.
    ("we are simply going to identify continuous functions with their graphs and
      use this idea as our principal notion of function.") -/
def LambdaModel.app (M : LambdaModel) (x y : M.D) : M.D := M.Fun x y

/-- The retraction gives application on graphs:  `(Graph f) · y = f y`.
    This is the model-level β-rule and is an immediate consequence of the
    retraction law. -/
theorem LambdaModel.app_Graph (M : LambdaModel) (f : M.D → M.D) (y : M.D) :
    M.app (M.Graph f) y = f y := by
  simp only [LambdaModel.app, M.Fun_Graph]

/-! ### K, S in a model, and the combinatory identities

    We interpret `K` and `S` directly in any `LambdaModel` and *prove* the
    combinatory identities from the retraction law alone. -/

/-- `K = Graph (λx. Graph (λy. x))`  in the model. -/
def LambdaModel.Kc (M : LambdaModel) : M.D :=
  M.Graph (fun x => M.Graph (fun _ => x))

/-- `S = Graph (λx. Graph (λy. Graph (λz. (x·z)·(y·z))))`  in the model. -/
def LambdaModel.Sc (M : LambdaModel) : M.D :=
  M.Graph (fun x => M.Graph (fun y => M.Graph (fun z =>
    M.app (M.app x z) (M.app y z))))

/-- The K-identity:  `K · x · y = x`. -/
theorem LambdaModel.Kc_spec (M : LambdaModel) (x y : M.D) :
    M.app (M.app M.Kc x) y = x := by
  simp only [LambdaModel.app, LambdaModel.Kc, M.Fun_Graph]

/-- The S-identity:  `S · x · y · z = (x · z) · (y · z)`. -/
theorem LambdaModel.Sc_spec (M : LambdaModel) (x y z : M.D) :
    M.app (M.app (M.app M.Sc x) y) z = M.app (M.app x z) (M.app y z) := by
  simp only [LambdaModel.app, LambdaModel.Sc, M.Fun_Graph]

/-! ## Combinatory algebra

    "The interpretation proposed here is ... a rather direct way of showing that
     a non-trivial combinatory algebra is possible."  (Section 4.)

    A combinatory algebra is a carrier with application and elements `K`, `S`
    satisfying the two defining identities. -/
structure CombinatoryAlgebra where
  A : Type
  app : A → A → A
  K : A
  S : A
  K_ax : ∀ x y, app (app K x) y = x
  S_ax : ∀ x y z, app (app (app S x) y) z = app (app x z) (app y z)

/-- Every λ-model is a combinatory algebra (via the K/S constructed above). -/
def LambdaModel.toCombinatoryAlgebra (M : LambdaModel) : CombinatoryAlgebra where
  A := M.D
  app := M.app
  K := M.Kc
  S := M.Sc
  K_ax := M.Kc_spec
  S_ax := M.Sc_spec

/-! ## Interpretation of λ-terms in a model

    Given an environment `env : Nat → D` assigning a value to every free index,
    the interpretation `⟦t⟧_env ∈ D` is defined by:
        ⟦var n⟧      = env n
        ⟦app t u⟧    = ⟦t⟧ · ⟦u⟧
        ⟦lam t⟧      = Graph (λ d. ⟦t⟧_(d :: env))
    (Scott: the λ-abstract is the graph of the induced map on the model.) -/

/-- Extend an environment under a binder:  `(d :: env)`. -/
def LambdaModel.extend {M : LambdaModel} (env : Nat → M.D) (d : M.D) :
    Nat → M.D
  | 0 => d
  | n + 1 => env n

/-- The interpretation `⟦t⟧_env` of a term in the model. -/
def LambdaModel.interp (M : LambdaModel) : (Nat → M.D) → Term → M.D
  | env, .var n => env n
  | env, .app t u => M.app (M.interp env t) (M.interp env u)
  | env, .lam t => M.Graph (fun d => M.interp (M.extend env d) t)

/-- Model-level β:  `⟦lam t⟧ · d = ⟦t⟧_(d :: env)`.  A direct consequence of the
    retraction law — this is the semantic core of β-soundness. -/
theorem LambdaModel.interp_lam_app (M : LambdaModel) (env : Nat → M.D)
    (t : Term) (d : M.D) :
    M.app (M.interp env (.lam t)) d = M.interp (M.extend env d) t := by
  simp only [LambdaModel.interp, LambdaModel.app_Graph]

/-! ### β-soundness

    "these laws are valid ... certain obvious laws (such as (α), (β), (ξ), (ξ*))
     hold."  The soundness of the (β) law: if `t` β-reduces to `u`, then `t` and
     `u` have the same interpretation in every model under every environment.

    The full proof requires the substitution lemma
        `⟦subst 0 u t⟧_env = ⟦t⟧_(⟦u⟧_env :: env)`
    (relating syntactic substitution to environment extension), together with a
    shifting lemma for `shiftAbove`.  These are standard but nontrivial; we state
    β-soundness and leave the proof as a TODO. -/

/-- Substitution lemma (TODO): syntactic substitution corresponds to environment
    extension in the model. -/
theorem LambdaModel.interp_subst (M : LambdaModel) (env : Nat → M.D)
    (t u : Term) :
    M.interp env (subst 0 u t) = M.interp (M.extend env (M.interp env u)) t := by
  sorry -- TODO: induction on `t` with a `shiftAbove`/`extend` commutation lemma

/-- β-soundness for a single step (TODO): a β-`Step` preserves interpretation. -/
theorem LambdaModel.interp_step_sound (M : LambdaModel) (env : Nat → M.D)
    {t u : Term} (h : Step t u) :
    M.interp env t = M.interp env u := by
  sorry -- TODO: induction on `h`; base case is `interp_lam_app` + `interp_subst`

/-- β-soundness for conversion (TODO): convertible terms are equal in every
    model.  This is the model-theoretic consistency of the λ-calculus that is the
    subject of the paper. -/
theorem LambdaModel.interp_conv_sound (M : LambdaModel) (env : Nat → M.D)
    {t u : Term} (h : Conv t u) :
    M.interp env t = M.interp env u := by
  sorry -- TODO: induction on `h`, using `interp_step_sound`

/-! ## §2-3.  The graph model  Pω  (Plotkin 1972 / Scott 1976)

    "What I have called the 'graph model' was found by Gordon Plotkin ...
     Motivation ... is, it is hoped, very fully exposed in Scott (1977)."

    The carrier is `Pω`, the powerset of `ℕ`.  Application is Scott's
    set-theoretic definition (formula (2) of Section 3):
        `X(Y) = { m | ∃ ⟨n, m⟩ ∈ X.  eₙ ⊆ Y }`,
    where `n` codes the finite set `eₙ` and `⟨·,·⟩` is a pairing.  Abstraction is
    the graph (formula (1)):
        `Graph f = { ⟨n, m⟩ | m ∈ f(eₙ) }`.

    The retraction `Fun ∘ Graph = id` holds on the *continuous* maps only (see
    formula (7) and the "fullness" condition (9) of Section 2), so `Pω` is a
    combinatory / λ-model in the extended sense but is not a total reflexive
    object in the strict sense of `LambdaModel` above.  We record the concrete
    application and abstraction. -/

/-- `Pω`, the powerset of `ℕ`, represented by characteristic predicates. -/
abbrev Pω := Nat → Prop

/-- The coding data underlying the graph model: a pairing `⟨·,·⟩` on `ℕ` and an
    enumeration `fin n = eₙ` of the finite subsets of `ℕ`. -/
structure GraphCoding where
  pair : Nat → Nat → Nat        -- ⟨n, m⟩
  fin : Nat → List Nat          -- eₙ, the n-th finite subset of ℕ

/-- `eₙ` as a subset of `ℕ` (an element of `Pω`). -/
def GraphCoding.finSet (c : GraphCoding) (n : Nat) : Pω := fun k => k ∈ c.fin n

/-- Application in the graph model (Scott, formula (2)):
        `X(Y) = { m | ∃ n. ⟨n,m⟩ ∈ X  ∧  eₙ ⊆ Y }`. -/
def graphApp (c : GraphCoding) (X Y : Pω) : Pω :=
  fun m => ∃ n, X (c.pair n m) ∧ (∀ k ∈ c.fin n, Y k)

/-- Abstraction in the graph model (Scott, formula (1)):
        `Graph f = { ⟨n,m⟩ | m ∈ f(eₙ) }`. -/
def graphAbs (c : GraphCoding) (f : Pω → Pω) : Pω :=
  fun j => ∃ n m, j = c.pair n m ∧ f (c.finSet n) m

/-! ## §4.  Fixed points and Park's Theorem

    Knaster–Tarski (Section 4):  every monotone `F : Pω → Pω` has a least fixed
    point, and the continuous case is reached by iteration:
        `fix(F) = ⋃ₙ Fⁿ(∅)`   (formula (2) of Section 4).
    Park's Theorem (Section 4): in a wide class of well-behaved models the least
    fixed-point operator `fix` and the paradoxical combinator `Y` coincide,
    `fix = Y`.  We record the fixed-point property of `Y` at the syntactic level
    as a conversion (TODO). -/

/-- Monotonicity of a set operator (Section 4, formula (1)):
        `X ⊆ Y  ⟹  F(X) ⊆ F(Y)`. -/
def Monotone (F : Pω → Pω) : Prop :=
  ∀ X Y : Pω, (∀ n, X n → Y n) → (∀ n, F X n → F Y n)

/-- `Y` is a fixed-point combinator:  `Y f = f (Y f)`  (Section 4,
    `Y(F) = F(Y(F))`).  Provable by one β-step under an environment; recorded
    here as a conversion (TODO: the standard `Step`/`Conv` derivation). -/
theorem Y_fixpoint (f : Term) : Conv (.app Y f) (.app f (.app Y f)) := by
  sorry -- TODO: unfold `Y`, β-contract the self-application, close under `Conv`

/-! ## Appendix.  Some axioms (recorded verbatim from the paper)

    Scott's theory takes `⊆` (`C`) as primitive and defines `=`; laws
    strengthened by `⊆` carry an asterisk, the one weakening a minus.

        (σ*)  ∅ ⊆ X
        (ρ*)  X ⊆ X
        (τ*)  X ⊆ Y ∧ Y ⊆ Z → X ⊆ Z
        (=*)  X = Y ↔ X ⊆ Y ∧ Y ⊆ X
        (μ*)  X ⊆ Y → Z(X) ⊆ Z(Y)
        (ν*)  X ⊆ Y → X(Z) ⊆ Y(Z)
        (α)   λX. τ[X] = λY. τ[Y]                       (change of bound variable)
        (β)   (λX. τ[X])(Y) = τ[Y]
        (ξ*)  ∀X. τ[X] ⊆ σ[X]  →  λX. τ[X] ⊆ λX. σ[X]  (monotone extensionality)
        (η⁻)  P ⊆ λX. P(X)                              (weak functionality)
        (fix*) F(fix F) ⊆ fix F
        (ζ*)  P(∅) ⊆ Q(∅) ∧ ∀X.(P(X) ⊆ Q(X) → P(F X) ⊆ Q(F X))
                → P(fix F) ⊆ Q(fix F)                   (directed-complete induction)
        (fix=Y) fix = λF. (λX. F(X(X)))(λX. F(X(X)))

    The law (η) `P = λX. P(X)` ("functionality" / "strict extensionality") holds
    only in the special models of Section 5 (the `D∞`-style retracts); in the
    graph model only the weaker (η⁻) is valid. -/

end Scott1980Lambda
