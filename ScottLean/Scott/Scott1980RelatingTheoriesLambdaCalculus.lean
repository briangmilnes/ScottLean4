/-
  Relating Theories of the λ-Calculus (Lean 4 formalization, pilot)

  Auto-generated faithful skeleton of:
    D. Scott, "Relating Theories of the λ-Calculus",
    in "To H. B. Curry: Essays on Combinatory Logic, Lambda Calculus and
    Formalism" (ed. J. P. Seldin and J. R. Hindley), Academic Press (1980),
    pp. 403-450.

  Source text extracted from:
    DanaScottPapers/Scott-1980-Relating-Theories-of-the-Lambda-Calculus.txt

  Scott's essay is largely philosophical, arguing that the various models of the
  λ-calculus "group rather uniformly under a general scheme": cartesian closed
  categories (c.c.c.'s) as the theory of TYPED functions, and REFLEXIVE domains
  U -- domains for which the function space (U → U) is a RETRACT of U -- as
  interpretations of the TYPE-FREE calculus.  The bridge in both directions is
  the "method of retracts".  This file transcribes the core formal objects:

    * Untyped λ-terms (de Bruijn) with lift / substitution and the β-reduct.
    * A λ-THEORY: an equivalence relation on terms closed under the congruence
      rules and (β), (ξ)  ("§2", the equational presentation).
    * Combinatory algebras ⟨U, ·, S, K⟩ and the standard combinators I, B
      ("§5", the first-order / variable-free presentation).
    * RETRACTIONS between domains (i : A → B, j : B → A with j ∘ i = 1_A) and
      RETRACTS as idempotents (a ∘ a = a), with the retract ordering  ("§3-§4").
    * REFLEXIVE domains (U → U) ◁ U and their interpretation of type-free terms.
    * The D_∞ inverse-limit sequence  D_{n+1} = (D_n → D_n)  and its fixed point
      (D_∞ → D_∞) ≅ D_∞.
    * The MAIN "relating" theorems, stated (Scott's §6 "Summary and
      Conclusions", conclusions 1-4).

  Core Lean 4 only; no Mathlib.  Deep model-theoretic equivalences are recorded
  as theorem STATEMENTS with `sorry` and a `-- TODO`; tractable structural facts
  are proved.
-/

namespace Scott1980Relating

/-! ## §1-§3.  Untyped λ-terms (de Bruijn)

    "Let the type-free terms be constructed in the usual way from variables
     x, y, z, ... by means of application and λ-abstraction."

    We use nameless de Bruijn indices: `var n` is the variable bound by the
    n-th enclosing `lam` (0 = innermost). -/
inductive Term where
  | var : Nat → Term            -- a variable (de Bruijn index)
  | app : Term → Term → Term    -- application  σ(τ)
  | lam : Term → Term           -- abstraction  λx.τ
  deriving DecidableEq, Repr

/-- `lift d c t` increments every free variable `≥ c` in `t` by `d`
    (the de Bruijn shift used to move a term under `d` extra binders). -/
def lift (d : Nat) : Nat → Term → Term
  | c, .var k     => if k < c then .var k else .var (k + d)
  | c, .app f a   => .app (lift d c f) (lift d c a)
  | c, .lam t     => .lam (lift d (c + 1) t)

/-- `subst j s t` replaces the variable `j` in `t` by `s`, decrementing the
    free variables above `j` (they lose one binder).  This is the de Bruijn
    single-variable substitution `t[j := s]`. -/
def subst (j : Nat) (s : Term) : Term → Term
  | .var k     => if k = j then s else if k > j then .var (k - 1) else .var k
  | .app f a   => .app (subst j s f) (subst j s a)
  | .lam t     => .lam (subst (j + 1) (lift 1 0 s) t)

/-- The β-reduct of the redex `(λ.t) u`:  substitute `u` for the bound variable.
    "The type-free theory ... satisfies (α), (β)-conversion, all the rules of
     equality, and the rule (ξ)." -/
def betaReduct (t u : Term) : Term := subst 0 u t

/-- Standard combinators as closed λ-terms (the translation `·*` of §5).
    `K x y = x`. -/
def Kterm : Term := .lam (.lam (.var 1))
/-- `S u v x = u x (v x)`. -/
def Sterm : Term := .lam (.lam (.lam
  (.app (.app (.var 2) (.var 0)) (.app (.var 1) (.var 0)))))
/-- `I x = x`, here as `λx.x` (equal to `S K K` in every combinatory algebra). -/
def Iterm : Term := .lam (.var 0)

/-! ## §2.  A theory of the λ-calculus as an equational theory

    "A λ-theory is an equational theory."  Scott presents a theory as the set of
     provable equations `t = σ` between terms, closed under the usual rules of
     equality (reflexivity, symmetry, transitivity), the congruence rules for
     application and abstraction, and the conversion rules (β) and (ξ):

        t = σ                                     (ξ)
        ---------------
        λx.t = λx.σ

    We model a theory by its provability relation together with these closure
    rules as fields.  Different theories differ by which further ("non-logical")
    equations between closed terms are added. -/
structure LambdaTheory where
  /-- `Eqn s t` : "the equation `s = t` is provable in the theory". -/
  Eqn      : Term → Term → Prop
  refl     : ∀ t, Eqn t t
  symm     : ∀ {s t}, Eqn s t → Eqn t s
  trans    : ∀ {r s t}, Eqn r s → Eqn s t → Eqn r t
  /-- Congruence for application (both arguments at once). -/
  appCongr : ∀ {s s' t t'}, Eqn s s' → Eqn t t' → Eqn (.app s t) (.app s' t')
  /-- Rule (ξ): abstraction respects provable equality. -/
  xi       : ∀ {s t}, Eqn s t → Eqn (.lam s) (.lam t)
  /-- Rule (β): `(λ.t) u = t[0 := u]`. -/
  beta     : ∀ t u, Eqn (.app (.lam t) u) (betaReduct t u)

namespace LambdaTheory

variable (T : LambdaTheory)

/-- The provability relation of a theory is reflexive (an equivalence relation).
    A tractable consequence of the closure fields. -/
theorem eqn_refl : ∀ t, T.Eqn t t := T.refl

/-- One-sided congruence for application on the left argument. -/
theorem appCongrL {s s' t : Term} (h : T.Eqn s s') :
    T.Eqn (.app s t) (.app s' t) :=
  T.appCongr h (T.refl t)

/-- One-sided congruence for application on the right argument. -/
theorem appCongrR {s t t' : Term} (h : T.Eqn t t') :
    T.Eqn (.app s t) (.app s t') :=
  T.appCongr (T.refl s) h

/-- A β-redex is provably equal to any term provably equal to its reduct
    (chaining (β) with transitivity) -- a small structural fact. -/
theorem beta_trans {t u r : Term} (h : T.Eqn (betaReduct t u) r) :
    T.Eqn (.app (.lam t) u) r :=
  T.trans (T.beta t u) h

end LambdaTheory

/-! ## §5.  Combinatory algebras ⟨U, ·, S, K⟩

    "In type-free λ-calculus ... the usual plan is to use the combinators.  Let
     us ... talk in terms of first-order models.  ... A λ-model is (at least) a
     structure of the form ⟨U, ·(·), S, K⟩ ... with two distinguished constants.
     Clearly we want:  K(x)(y) = x  and  S(u)(v)(x) = u(x)(v(x))."

    We write application `x · y` for Scott's `x(y)`.  `S` and `K` are the two
    primitive constants; the two equations are Scott's characteristic axioms. -/
structure CombinatoryAlgebra where
  U    : Type
  ap   : U → U → U
  K    : U
  S    : U
  /-- `K(x)(y) = x`. -/
  Kax  : ∀ x y, ap (ap K x) y = x
  /-- `S(u)(v)(x) = u(x)(v(x))`. -/
  Sax  : ∀ u v x, ap (ap (ap S u) v) x = ap (ap u x) (ap v x)

namespace CombinatoryAlgebra

variable (A : CombinatoryAlgebra)

/-- The identity combinator `I = S K K`  ("I = S(K)(K)"). -/
def I : A.U := A.ap (A.ap A.S A.K) A.K

/-- `I(x) = x`:  `S(K)(K)(x) = K(x)(K(x)) = x`.  A fully tractable proof from the
    two characteristic axioms -- the base case of the variable-free calculus. -/
theorem I_eval (x : A.U) : A.ap A.I x = x := by
  unfold I
  rw [A.Sax A.K A.K x, A.Kax x (A.ap A.K x)]

/-- The composition combinator `B = S(K(S))(K)`  ("B = S(K(S))(K)"). -/
def B : A.U := A.ap (A.ap A.S (A.ap A.K A.S)) A.K

/-- `B(f)(g)(x) = f(g(x))`:  the defining property of `B`, established by pure
    combinatory calculation from the `S`/`K` axioms. -/
theorem B_eval (f g x : A.U) :
    A.ap (A.ap (A.ap A.B f) g) x = A.ap f (A.ap g x) := by
  unfold B
  rw [A.Sax (A.ap A.K A.S) A.K f, A.Kax A.S f, A.Sax (A.ap A.K f) g x, A.Kax f x]

end CombinatoryAlgebra

/-! ## §3-§4.  Retractions and retracts (the "method of retracts")

    "In a category, a retraction between two domains A and B is a pair of maps
     i : A → B and j : B → A where j ∘ i = 1_A.  Regard A as the 'smaller'
     domain; it is injected into B, and B is surjectively mapped onto A."

    We interpret domains as Lean types and maps as functions. -/
structure Retraction (A B : Type) where
  i  : A → B                 -- injection of the smaller domain
  j  : B → A                 -- surjection onto the smaller domain
  ji : ∀ a, j (i a) = a      -- j ∘ i = 1_A

/-- Every domain is a retract of itself (identity retraction), `1_A`. -/
def Retraction.id (A : Type) : Retraction A A where
  i  := fun a => a
  j  := fun a => a
  ji := fun _ => rfl

/-- "The use of idempotents in a category as forming a category is well known."
    A RETRACT of a domain `D` is an idempotent map  `a ∘ a = a`. -/
structure Retract (D : Type) where
  a    : D → D
  idem : ∀ x, a (a x) = a x     -- a ∘ a = a

/-- Every retraction `A ◁ B` induces a retract of `B`, namely the idempotent
    `e = i ∘ j`.  Proof: `e(e x) = i(j(i(j x))) = i((j∘i)(j x)) = i(j x) = e x`.
    This is Scott's passage from retraction pairs to idempotents. -/
def Retraction.toRetract {A B : Type} (r : Retraction A B) : Retract B where
  a    := fun x => r.i (r.j x)
  idem := by intro x; simp only [r.ji]

/-- The retract (information / definability) ordering.  `A ⊑ B` when `A` is a
    retract of `B`: there is a retraction pair injecting `A` into `B`.
    "Note that every A in the category is a retract of U." -/
def RetractLE (A B : Type) : Prop := Nonempty (Retraction A B)

/-- The retract ordering is reflexive: `A ⊑ A`. -/
theorem RetractLE.refl (A : Type) : RetractLE A A :=
  ⟨Retraction.id A⟩

/-! ## §3-§4.  Reflexive domains and the interpretation of the type-free calculus

    "We can call U 'reflexive' if (U → U) is a retract [of U]. ... Then U (as it
     sits in its category) gives us an interpretation of the type-free calculus."

    A reflexive domain packages the retraction  (D → D) ◁ D  with injection
    `i : (D → D) → D`  and surjection `j : D → (D → D)`  satisfying  j ∘ i = 1. -/
structure ReflexiveDomain where
  D       : Type
  i       : (D → D) → D            -- "fold" a function into the domain
  j       : D → (D → D)            -- "unfold" an element as a function
  retract : ∀ f, j (i f) = f       -- j ∘ i = 1_{(D→D)} : (D → D) is a retract of D

namespace ReflexiveDomain

variable (M : ReflexiveDomain)

/-- The application operation on a reflexive domain:  `x · y = (j x)(y)`.
    "The application operation f(x) on U can be defined as [ (j f)(x) ]." -/
def dapp (x y : M.D) : M.D := M.j x y

/-- The β-law in a reflexive domain:  `(i f) · y = f y`.  Because `(U → U)` is a
    retract of `U` (`j ∘ i = 1`), abstraction followed by application is the
    identity.  This is the semantic content of (β); fully provable here. -/
theorem dapp_i (f : M.D → M.D) (y : M.D) : M.dapp (M.i f) y = f y := by
  unfold dapp
  rw [M.retract]

/-- Extend an environment `env` with a new value `d` bound to index `0`
    (shifting the old bindings up by one). -/
def extend {α : Type} (d : α) (env : Nat → α) : Nat → α
  | 0     => d
  | k + 1 => env k

/-- The reflexive-domain interpretation `⟦t⟧_env` of a type-free term `t`
    under an environment `env : Nat → D` assigning values to free variables:

        ⟦var k⟧   = env k
        ⟦app f a⟧ = (j ⟦f⟧)(⟦a⟧)          -- application via the retract
        ⟦lam t⟧   = i (λ d. ⟦t⟧_(d :: env)) -- abstraction via the retract

    This is exactly Scott's interpretation "via U of the type-free calculus". -/
def interp (M : ReflexiveDomain) : (Nat → M.D) → Term → M.D
  | env, .var k   => env k
  | env, .app f a => M.j (M.interp env f) (M.interp env a)
  | env, .lam t   => M.i (fun d => M.interp (extend d env) t)

/-- The interpretation validates (β) at the semantic level:
        ⟦(λ.t) a⟧_env = ⟦t⟧_(⟦a⟧ :: env).
    A direct consequence of `retract`, requiring no reasoning about de Bruijn
    substitution.  (Agreement with the syntactic `betaReduct` is the deeper
    substitution lemma left as `sorry` below.) -/
theorem interp_beta (env : Nat → M.D) (t a : Term) :
    M.interp env (.app (.lam t) a)
      = M.interp (extend (M.interp env a) env) t := by
  simp only [interp]
  rw [M.retract]

/-- Deeper: the interpretation is sound for the syntactic β-reduct as well,
        ⟦(λ.t) a⟧_env = ⟦ t[0 := a] ⟧_env.
    This needs the de Bruijn substitution lemma relating `subst`/`lift` to
    environment extension. -/
theorem interp_betaReduct (env : Nat → M.D) (t a : Term) :
    M.interp env (.app (.lam t) a) = M.interp env (betaReduct t a) := by
  -- TODO: prove via a substitution lemma  ⟦subst 0 a t⟧_env = ⟦t⟧_(⟦a⟧::env).
  sorry

end ReflexiveDomain

/-- The theory induced by a reflexive domain `M`:  two terms are equated exactly
    when they have the same interpretation under every environment.
    "The type-free theory ... has as its assertions exactly those equations
     t = σ where [⟦t⟧ = ⟦σ⟧] in the category." -/
def ReflexiveDomain.theoryEqn (M : ReflexiveDomain) (s t : Term) : Prop :=
  ∀ env : Nat → M.D, M.interp env s = M.interp env t

/-! ## §3.  The D_∞ inverse-limit construction

    "I thought this was made very clear in the so-called D_∞-construction. ...
     Starting with any domain D_0 ... the sequence of types D_n where
     D_{n+1} = (D_n → D_n) has a certain limit D_∞ with D_0 (and all the D_n's)
     as retracts, and with (D_∞ → D_∞) not only a retract but an isomorph of
     D_∞."  -/

/-- The sequence of function-space types  `D_{n+1} = (D_n → D_n)`  over a base
    domain `D0`.  Purely the "types" side of the inverse system. -/
def Dseq (D0 : Type) : Nat → Type
  | 0     => D0
  | n + 1 => Dseq D0 n → Dseq D0 n

/-- An isomorphism of domains (a retraction that is also a section: both
    composites are the identity). -/
structure Iso (A B : Type) where
  to    : A → B
  fro   : B → A
  left  : ∀ a, fro (to a) = a
  right : ∀ b, to (fro b) = b

/-- An isomorphism is in particular a retraction `A ◁ B`. -/
def Iso.toRetraction {A B : Type} (e : Iso A B) : Retraction A B where
  i  := e.to
  j  := e.fro
  ji := e.left

/-- A reflexive domain whose retract is in fact an ISOMORPHISM
    `(D → D) ≅ D` -- Scott's distinguishing feature of `D_∞`
    ("(D_∞ → D_∞) not only a retract but an isomorph of D_∞"). -/
structure ExtensionalReflexiveDomain extends ReflexiveDomain where
  /-- `i ∘ j = 1_D` as well, so `(D → D) ≅ D`.  This is EXTENSIONALITY. -/
  section' : ∀ x, i (j x) = x

/-- An `ExtensionalReflexiveDomain` carries an isomorphism `(D → D) ≅ D`. -/
def ExtensionalReflexiveDomain.iso (M : ExtensionalReflexiveDomain) :
    Iso (M.D → M.D) M.D where
  to    := M.i
  fro   := M.j
  left  := M.retract
  right := M.section'

/-- MAIN CONSTRUCTION (D_∞).  Over any base domain there is an extensional
    reflexive domain `D_∞` -- the inverse limit of the `Dseq` system -- with
    `(D_∞ → D_∞) ≅ D_∞`.  The witness is the inverse-limit / colimit of the
    projections `D_{n+1} → D_n`, which needs the order-theoretic (continuous
    lattice / cpo) structure developed in Scott (1976). -/
theorem Dinfty_exists (D0 : Type) :
    ∃ M : ExtensionalReflexiveDomain, Nonempty (Iso (Dseq D0 0) M.D) := by
  -- TODO: build the inverse limit D_∞ = lim (D_n, projections) and its iso
  -- (D_∞ → D_∞) ≅ D_∞.  Requires the cpo/continuity theory (not core Lean).
  sorry

/-! ## §6.  Summary and Conclusions -- the MAIN relating theorems

    Scott's numbered conclusions.  These relate the four presentations:
      • typed λ-calculus  ≃  cartesian closed categories (c.c.c.);
      • type-free λ-calculus  ≃  reflexive domains in a c.c.c.;
      • conservative embedding of a c.c.c. into higher-order intuitionistic
        type theory (a topos, via the functor category Sᶜᵒᵖ).

    A full c.c.c. / topos formalization is beyond core Lean 4, so the categorical
    statements are recorded schematically as `Prop`s (opaque predicates), while
    the statements expressible over the structures above are given as theorems.
-/

/-- Abstract stand-in for "is (the theory of) a cartesian closed category". -/
opaque IsCCC (T : LambdaTheory) : Prop
/-- Abstract stand-in for "is a typed λ-calculus (with products, function
    spaces) equational theory". -/
opaque IsTypedTheory (T : LambdaTheory) : Prop
/-- Abstract stand-in for "embeds fully and faithfully, as a conservative
    extension, into higher-order intuitionistic type theory (a topos)". -/
opaque EmbedsInTopos (T : LambdaTheory) : Prop

/-- **Conclusion 1** (Lambek).  "A theory in typed λ-calculus is just the same as
    a cartesian closed category."  There is a perfect correspondence between
    (extensional) typed λ-calculi and c.c.c.'s. -/
theorem typed_theory_iff_ccc (T : LambdaTheory) :
    IsTypedTheory T ↔ IsCCC T := by
  -- TODO: Lambek's correspondence typed λ-calculus ⇄ c.c.c.
  sorry

/-- **Conclusion 2**.  "In a c.c.c. a reflexive domain provides an interpretation
    of the 'type-free' theory."  Every reflexive domain `M` induces a λ-theory
    (`M.theoryEqn`) satisfying the closure rules of §2.

    The three fully provable rules (reflexivity, symmetry, transitivity of
    "same interpretation") are discharged; the congruence/(β)/(ξ) fields depend
    on `interp_betaReduct` and substitution lemmas and are left as `sorry`. -/
theorem reflexive_domain_interprets (M : ReflexiveDomain) :
    ∃ T : LambdaTheory, T.Eqn = M.theoryEqn := by
  -- The relation itself:
  refine ⟨{ Eqn := M.theoryEqn
          , refl := ?_, symm := ?_, trans := ?_
          , appCongr := ?_, xi := ?_, beta := ?_ }, rfl⟩
  · intro t env; rfl
  · intro s t h env; exact (h env).symm
  · intro r s t h1 h2 env; exact (h1 env).trans (h2 env)
  · -- congruence for application: same interpretation is preserved by `j _ _`.
    intro s s' t t' hs ht env
    simp only [ReflexiveDomain.interp]
    rw [hs env, ht env]
  · -- rule (ξ): TODO -- needs ⟦s⟧_(d::env) = ⟦t⟧_(d::env) from ⟦s⟧ = ⟦t⟧
    -- under all environments, i.e. extensional agreement pointwise.
    sorry
  · -- rule (β): the interpretation validates the syntactic β-reduct.
    intro t u env; exact M.interp_betaReduct env t u

/-- **Conclusion 3**.  "Every type-free theory is the theory of a reflexive
    domain in a c.c.c."  (Proved in the paper "by the author's method of
    retracts".)  Conversely to Conclusion 2: every λ-theory arises as the
    `theoryEqn` of some reflexive domain -- nothing is lost in passing to typed
    theories. -/
theorem every_theory_is_reflexive_domain_theory (T : LambdaTheory) :
    ∃ M : ReflexiveDomain, ∀ s t, T.Eqn s t ↔ M.theoryEqn s t := by
  -- TODO: the term-model / retract construction of Scott §4 producing a
  -- reflexive domain U with (U → U) ◁ U whose induced theory is exactly T.
  sorry

/-- **Conclusion 4**.  "Every c.c.c. can be fully and faithfully embedded in an
    intuitionistic theory of types with the full (impredicative) power-set
    construct and function spaces."  A conservative extension result, via the
    functor category `Sᶜᵒᵖ` (an early example of a topos). -/
theorem ccc_embeds_in_topos (T : LambdaTheory) (h : IsCCC T) :
    EmbedsInTopos T := by
  -- TODO: Yoneda embedding C → Sᶜᵒᵖ; conservativity of the higher-order
  -- intuitionistic theory over the c.c.c.
  sorry

/-- Adjoining indeterminates: "every typed or untyped theory of λ-calculus has an
    extensional model.  This can also be put as a conservative extension result:
    ... every such equational theory can be expanded to a first-order theory
    without forcing any new equations on us."  Stated as the existence of an
    EXTENSIONAL reflexive domain (an `i∘j = 1` model, i.e. `(D → D) ≅ D`) that is
    conservative over `T`. -/
theorem every_theory_has_extensional_model (T : LambdaTheory) :
    ∃ M : ExtensionalReflexiveDomain,
      ∀ s t, T.Eqn s t → M.toReflexiveDomain.theoryEqn s t := by
  -- TODO: conservative expansion to an extensional (η) model by adjoining
  -- enough indeterminates (Barendregt 1980; Scott's "method of retracts").
  sorry

end Scott1980Relating
