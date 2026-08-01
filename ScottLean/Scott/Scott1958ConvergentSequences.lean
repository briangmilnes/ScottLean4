/-
  Convergent Sequences of Complete Theories (Lean 4 faithful skeleton)

  Faithful to:
    Dana Scott, "Convergent Sequences of Complete Theories",
    Ph.D. Dissertation, Princeton University, June 1958.

  Source text extracted from:
    DanaScottPapers/Scott-1958-Convergent-Sequences-of-Complete-Theories-dissertation.txt

  This is an auto-generated faithful skeleton.  It transcribes the core formal
  objects of the dissertation:

    * Part I, Section 1.  An abstract sentence algebra (S, ->, ~, L) with the
      Tarski-style closure conditions on the set `L` of logically valid
      sentences (p. 6-7).  Theories (Definition 1.2), logical closure
      (Definition 1.4), extensions (Definition 1.5), complete theories
      (Definition 1.6).  Theorem 1.3 (intersections and directed unions of
      theories are theories), Theorem 1.7 (finite complete extensions of an
      intersection of complete theories), Theorem 1.9 (equivalence of: unique
      infinite complete extension / completeness of the liminf / convergence).
    * limsup, liminf and convergence of a sequence of sets/theories (Section 0,
      p. 3-4).
    * Part I, Section 2.  n-ary relational systems (Definition 2.1),
      satisfaction (Definition 2.2), the theory `Th(R)` of a system
      (Definition 2.5), and *arithmetical extension of degree m*
      (Definition 2.6).  Theorems 2.7, 2.8, 2.9 give algebraic conditions.
    * Part II.  The main geometric application: an n-variable first-order
      sentence is true in Euclidean geometry of dimension n-1 iff it is true in
      all higher dimensions (abstract, p. i and Section 5).

  Core Lean 4 only; no Mathlib.  Set-theoretic and metamathematical notions are
  stated abstractly.  Deep theorems are left as `sorry` with `-- TODO`; no proof
  is fabricated.
-/

namespace Scott1958

/-! ## Section 0.  Sequences of sets: limsup, liminf, convergence

    For a family `X : I -> Set` indexed by `I`, Scott defines (p. 3):
      limsup X = ⋂_{F finite} ⋃_{i ∉ F} X i,
      liminf X = ⋃_{F finite} ⋂_{i ∉ F} X i,
    and the sequence *converges* when limsup = liminf, with that common value the
    *limit*.  We phrase this over predicates on a fixed carrier of "objects". -/

/-- A "set of objects" is a predicate on the ambient type `α`. -/
abbrev SetOf (α : Type) := α → Prop

/-- `i` lies outside the finite set `F` (represented as a list of indices). -/
def notIn {I : Type} [DecidableEq I] (F : List I) (i : I) : Prop := ¬ F.contains i

/-- `limsup` of an indexed family: for every finite `F` there is some `i ∉ F`
    with `x ∈ X i`. -/
def limsup {I α : Type} [DecidableEq I] (X : I → SetOf α) (a : α) : Prop :=
  ∀ F : List I, ∃ i, notIn F i ∧ X i a

/-- `liminf` of an indexed family: for some finite `F`, `x ∈ X i` for every
    `i ∉ F`. -/
def liminf {I α : Type} [DecidableEq I] (X : I → SetOf α) (a : α) : Prop :=
  ∃ F : List I, ∀ i, notIn F i → X i a

/-- A sequence of sets converges when its liminf and limsup coincide. -/
def Converges {I α : Type} [DecidableEq I] (X : I → SetOf α) : Prop :=
  ∀ a, liminf X a ↔ limsup X a

/-- liminf is always contained in limsup (elementary, p. 4). -/
theorem liminf_le_limsup {I α : Type} [DecidableEq I] (X : I → SetOf α)
    (a : α) (_hI : ∀ F : List I, ∃ i, notIn F i) :
    liminf X a → limsup X a := by
  sorry -- TODO liminf ⊆ limsup (needs that the index set is infinite)

/-! ## Section 1.  Abstract theories (Tarski-style)

    `S` is a non-empty set of sentences closed under implication `imp` and
    negation `neg`.  `Valid` is the set `L` of logically valid sentences with
    the three closure assumptions (p. 6-7):
      (i) L ⊆ S (here every term of `Sent` is a sentence, so this is automatic);
      (ii) L contains all sentential-calculus axiom instances;
      (iii) L is closed under modus ponens. -/

/-- The abstract sentence algebra of Section 1. -/
structure SentenceAlgebra where
  Sent      : Type
  imp       : Sent → Sent → Sent
  neg       : Sent → Sent
  Valid     : Sent → Prop
  /-- (iii) modus ponens: L is closed under detachment. -/
  valid_mp  : ∀ φ ψ, Valid φ → Valid (imp φ ψ) → Valid ψ
  /-- (ii) the axiom `φ → (ψ → φ)` is valid. -/
  ax_k      : ∀ φ ψ, Valid (imp φ (imp ψ φ))
  /-- (ii) the axiom `(φ → (ψ → χ)) → ((φ → ψ) → (φ → χ))` is valid. -/
  ax_s      : ∀ φ ψ χ, Valid (imp (imp φ (imp ψ χ)) (imp (imp φ ψ) (imp φ χ)))
  /-- (ii) the contraposition axiom `(¬ψ → ¬φ) → (φ → ψ)` is valid. -/
  ax_contra : ∀ φ ψ, Valid (imp (imp (neg ψ) (neg φ)) (imp φ ψ))

variable (𝒮 : SentenceAlgebra)

/-- Definition 1.2.  A (consistent) theory: a set of sentences containing all
    valid sentences and closed under modus ponens, and not all of `S`.  We
    record the two positive conditions; consistency `T ≠ S` is a side
    condition. -/
structure IsTheory (T : 𝒮.Sent → Prop) : Prop where
  contains_valid : ∀ φ, 𝒮.Valid φ → T φ
  modus_ponens   : ∀ φ ψ, T φ → T (𝒮.imp φ ψ) → T ψ

/-- Definition 1.6.  A theory is complete iff for every sentence, it or its
    negation belongs (the well-known characterization on p. 11). -/
def IsComplete (T : 𝒮.Sent → Prop) : Prop :=
  IsTheory 𝒮 T ∧ ∀ φ, T φ ∨ T (𝒮.neg φ)

/-- Definition 1.5(i).  `T₂` extends `T₁`. -/
def Extends (T₁ T₂ : 𝒮.Sent → Prop) : Prop := ∀ φ, T₁ φ → T₂ φ

/-- Theorem 1.3 (first half).  The intersection of a non-empty class of
    theories is a theory. -/
theorem inter_isTheory {J : Type} (𝒯 : J → (𝒮.Sent → Prop))
    (hJ : Nonempty J) (h : ∀ j, IsTheory 𝒮 (𝒯 j)) :
    IsTheory 𝒮 (fun φ => ∀ j, 𝒯 j φ) where
  contains_valid := fun _ hφ j => (h j).contains_valid _ hφ
  modus_ponens   := fun _ _ hφ hφψ j => (h j).modus_ponens _ _ (hφ j) (hφψ j)

/-- Theorem 1.7.  If `T = ⋂ Tᵢ` for complete theories `Tᵢ` and each `Tᵢ` is a
    finite extension (differing by the choice of a sentence `Aⱼ`), then the
    `Tⱼ` are exactly the finite complete extensions of `T`.  Stated abstractly:
    each complete `Tⱼ` extends the intersection `T`. -/
theorem inter_complete_extends {J : Type} (𝒯 : J → (𝒮.Sent → Prop))
    (_h : ∀ j, IsComplete 𝒮 (𝒯 j)) (j : J) :
    Extends 𝒮 (fun φ => ∀ k, 𝒯 k φ) (𝒯 j) :=
  fun _ hφ => hφ j

/-- Theorem 1.9.  For an infinite index set and complete `Tᵢ` with `T = ⋂ Tᵢ`,
    the three conditions are equivalent:
      (i)   `T` has a unique infinite complete extension;
      (ii)  the theory `T_∞ = liminf Tᵢ` is complete;
      (iii) the sequence of theories `Tᵢ` converges.
    We state the (ii) ⟺ (iii) core (the part whose proof, per the Remark on
    p. 12, uses only infiniteness and completeness of the `Tᵢ`). -/
theorem convergence_iff_liminf_complete {I : Type} [DecidableEq I]
    (𝒯 : I → (𝒮.Sent → Prop)) (_hcomplete : ∀ i, IsComplete 𝒮 (𝒯 i)) :
    IsComplete 𝒮 (fun φ => liminf 𝒯 φ) ↔ Converges 𝒯 := by
  sorry -- TODO Theorem 1.9, (ii) ⟺ (iii)

/-! ## Section 2.  Relational systems and arithmetical extensions

    An n-ary relational system (Definition 2.1) is a non-empty carrier `A` with
    an n-ary relation `R ⊆ Aⁿ`, here `R : (Fin n → A) → Prop`.  Satisfaction
    (Definition 2.2) is the usual Tarski recursion; we keep the object language
    abstract via `Formula` and record satisfaction as data. -/

/-- Definition 2.1(i).  An n-ary relational system.  (Non-emptiness is a side
    condition, witnessed by `pt`.) -/
structure RelSystem (n : Nat) where
  A  : Type
  pt : A
  R  : (Fin n → A) → Prop

/-- Definition 2.1(ii).  `G` is an extension of `R`: the carrier embeds and the
    relation is the restriction.  We record the carrier embedding `ι` and the
    two compatibility conditions. -/
structure IsExtension {n : Nat} (R G : RelSystem n) where
  ι        : R.A → G.A
  ι_inj    : ∀ a b, ι a = ι b → a = b
  rel_iff  : ∀ x : Fin n → R.A, R.R x ↔ G.R (fun i => ι (x i))

/-- An abstract object language: first-order formulas over one n-placed
    predicate symbol, together with the number of *distinct* variables occurring
    (both free and bound), as used in Definition 2.6. -/
structure Language (n : Nat) where
  Formula      : Type
  /-- number of distinct variables in a formula (Definition 2.6 remark). -/
  varCount     : Formula → Nat
  /-- satisfaction of a formula by an assignment in a relational system. -/
  Sat          : (R : RelSystem n) → Formula → (Nat → R.A) → Prop

variable {n : Nat} (Lang : Language n)

/-- Definition 2.6.  `G` is an *arithmetical extension of degree m* of `R` iff
    it is an extension and satisfaction agrees for every formula with at most
    `m` distinct variables. -/
structure ArithExtOfDegree (m : Nat) (R G : RelSystem n)
    (ext : IsExtension R G) : Prop where
  agree : ∀ φ : Lang.Formula, Lang.varCount φ ≤ m →
            ∀ x : Nat → R.A,
              Lang.Sat R φ x ↔ Lang.Sat G φ (fun i => ext.ι (x i))

/-- Theorem 2.7.  Sufficient condition: `G` extends `R`, and for every subset
    `A'` of `A` with fewer than `m` elements and every `b ∈ B` there is an
    automorphism of `G` fixing `A'` pointwise and sending `b` into (the image
    of) `A`.  Under these hypotheses `G` is an arithmetical extension of degree
    `m`. -/
theorem arithExt_of_automorphisms (m : Nat) (R G : RelSystem n)
    (ext : IsExtension R G)
    (_hyp : True) :  -- placeholder for the automorphism condition (ii)
    ArithExtOfDegree Lang m R G ext := by
  sorry -- TODO Theorem 2.7 (induction on formula complexity)

/-- Theorem 2.8.  If `G` has subsystems `Rᵢ` (`i = 1,2,3,…`) with `G` an
    arithmetical extension of degree `i` of each `Rᵢ`, then
    `Th(G) = lim Th(Rᵢ)`; in particular the sequence `Th(Rᵢ)` converges.
    Here `ThOf i` stands for `Th(Rᵢ)` as a set of sentences of `S`. -/
theorem arithExt_limit (S : SentenceAlgebra)
    (ThOf : Nat → (S.Sent → Prop))
    (_hsub : ∀ _i : Nat, True)  -- Rᵢ a subsystem, G an arith. ext. of degree i
    : Converges ThOf := by
  sorry -- TODO Theorem 2.8 (Th(G) = liminf Th(Rᵢ) and completeness ⇒ convergence)

/-! ## Part II.  The Euclidean geometry application (Section 5)

    Main theorem (Abstract, p. i): a first-order formula with at most `n`
    variables is true in Euclidean geometry of dimension `n-1` iff it is true in
    all higher dimensions.  We take `EuclidGeom d` as the relational system of
    d-dimensional Euclidean space and `TrueIn` as truth of a sentence there. -/

/-- Main geometric theorem: for `EuclidGeom d` the relational system of
    `d`-dimensional Euclidean space, an `n`-variable sentence holds in dimension
    `n-1` iff it holds in every higher dimension. -/
theorem euclid_dimension_stabilizes
    (EuclidGeom : Nat → RelSystem n)
    (TrueIn : RelSystem n → Lang.Formula → Prop)
    (φ : Lang.Formula) (_hφ : Lang.varCount φ ≤ n) :
    TrueIn (EuclidGeom (n - 1)) φ ↔ ∀ d, n - 1 ≤ d → TrueIn (EuclidGeom d) φ := by
  sorry -- TODO Part II main theorem (via arithmetical extensions of finite degree)

end Scott1958
