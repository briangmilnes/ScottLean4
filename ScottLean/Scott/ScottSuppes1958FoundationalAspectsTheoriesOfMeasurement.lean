/-
  Foundational Aspects of Theories of Measurement (Lean 4 formalization)

  Faithful to:
    D. Scott and P. Suppes,
    "Foundational Aspects of Theories of Measurement",
    The Journal of Symbolic Logic 23(2):113-128, 1958.

  Source text extracted from:
    DanaScottPapers/Scott-Suppes-1958-Foundational-Aspects-Theories-of-Measurement.txt

  Auto-generated faithful skeleton.

  This module encodes the relational-system framework and the two explicit
  axiom systems of the paper:

    * relational systems, homomorphism, isomorphism, subsystem, imbeddability,
      numerical assignment, and the set-theoretic definition of a *theory of
      measurement* (Section 1);
    * Luce's **semiorder** axioms `S1`–`S3` (with `S4` the reduced-form axiom),
      together with the indifference relation `I` (Section 2), and a proof that
      the integer "just-noticeable-difference" relation `x ≽ y ↔ y + 1 ≤ x`
      satisfies the semiorder axioms;
    * the **difference-measurement** structures `H` with the quaternary relation
      `D` and axioms `A1`–`A8`, with the defined relations `R`, `M₁`, `Mⁿ⁺¹`
      (Section 2).

  Core Lean 4 only; no Mathlib.  Real numbers are unavailable in the core
  library, so the concrete numerical model is given over `Int` (the paper uses
  `⟨Re, ≽⟩` with `x ≽ y ↔ x ≥ y + 1`).
-/

namespace ScottSuppes1958

/-! ## Section 1.  Relational systems and theories of measurement

    "we treat sets of empirical data as … (finitary) relational systems, that is
     … finite sequences `𝔄 = ⟨A, R₁, …, Rₙ⟩`."

    A fully general relational system ranges over an arbitrary list of relations
    of varying arities.  We isolate the case relevant to the paper's two theories:
    a single-relation system `⟨A, R⟩`.  The arity is recorded by the type of `R`. -/

/-- A binary relational system `⟨A, R⟩` (type `⟨2⟩`): a carrier `A` with one
    binary relation.  Semiorders live here. -/
structure BinSystem where
  A : Type
  R : A → A → Prop

/-- A quaternary relational system `⟨A, D⟩` (type `⟨4⟩`): a carrier with one
    4-ary relation.  Difference structures live here. -/
structure QuatSystem where
  A : Type
  D : A → A → A → A → Prop

/-- Homomorphism of binary systems: `f : A → B` onto, preserving/reflecting `R`
    (Section 1: `Rᵢ(a⃗) ↔ Sᵢ(f a⃗)`).  We record the defining biconditional. -/
def IsHom (𝔄 𝔅 : BinSystem) (f : 𝔄.A → 𝔅.A) : Prop :=
  (Function.Surjective f) ∧ ∀ a b, 𝔄.R a b ↔ 𝔅.R (f a) (f b)

/-- Isomorphic image: a one-one homomorphism (Section 1). -/
def IsIso (𝔄 𝔅 : BinSystem) (f : 𝔄.A → 𝔅.A) : Prop :=
  IsHom 𝔄 𝔅 f ∧ Function.Injective f

/-- A *numerical assignment* of `𝔄` w.r.t. the numerical system `𝔑` is a function
    imbedding `𝔄` in `𝔑`, i.e. a homomorphism (not required to be one-one).
    Here `𝔑` is a binary system whose carrier is `Int` (standing in for `Re`). -/
def NumericalAssignment (𝔄 : BinSystem) (𝔑 : BinSystem) (f : 𝔄.A → 𝔑.A) : Prop :=
  ∀ a b, 𝔄.R a b ↔ 𝔑.R (f a) (f b)

/-- `𝔄` is imbeddable in `𝔑` iff there is a numerical assignment (Section 1). -/
def Imbeddable (𝔄 𝔑 : BinSystem) : Prop :=
  ∃ f : 𝔄.A → 𝔑.A, NumericalAssignment 𝔄 𝔑 f

/-- **Theory of measurement** (Section 1, set-theoretic characterization):
    a class `K` of relational systems, closed under isomorphism, for which there
    is a numerical relational system `𝔑` such that every system in `K` is
    imbeddable in `𝔑`.

    `K` is represented by its membership predicate on `BinSystem`. -/
structure TheoryOfMeasurement (K : BinSystem → Prop) where
  /-- the fixed numerical relational system `𝔑` (of the appropriate type). -/
  𝔑 : BinSystem
  /-- closure under isomorphism. -/
  closedUnderIso : ∀ 𝔄 𝔅, K 𝔄 → (∃ f, IsIso 𝔄 𝔅 f) → K 𝔅
  /-- every member is imbeddable in `𝔑`. -/
  imbeds : ∀ 𝔄, K 𝔄 → Imbeddable 𝔄 𝔑

/-! ## Section 2.  Semiorders (Luce's axioms, simplified)

    "A semiorder is a relational system `⟨A, P⟩` of type `⟨2⟩` which satisfies the
     following axioms for all `x, y, z, w ∈ A`:
       S1.  Not `x P x`.
       S2.  If `x P y` and `z P w`, then either `x P w` or `z P y`.
       S3.  If `x P y` and `z P x`, then either `w P y` or `z P w`." -/

/-- The semiorder axioms on a relation `P` (Section 2). -/
structure Semiorder {A : Type} (P : A → A → Prop) : Prop where
  /-- `S1` — irreflexivity. -/
  S1 : ∀ x, ¬ P x x
  /-- `S2`. -/
  S2 : ∀ x y z w, P x y → P z w → (P x w ∨ P z y)
  /-- `S3`. -/
  S3 : ∀ x y z w, P x y → P z x → (P w y ∨ P z w)

/-- Indifference: `x I y ≡ ¬ x P y ∧ ¬ y P x` (Section 2). -/
def Indiff {A : Type} (P : A → A → Prop) (x y : A) : Prop :=
  ¬ P x y ∧ ¬ P y x

/-- `S4` — the reduction axiom `(*)`: `x E y → x = y`, where `E` (perfect
    substitutability) simplifies for semiorders to `∀ z, x I z ↔ y I z`
    (Section 2, the class `S*`). -/
def S4 {A : Type} (P : A → A → Prop) : Prop :=
  ∀ x y, (∀ z, Indiff P x z ↔ Indiff P y z) → x = y

/-! ### The numerical semiorder `⟨Re, ≽⟩`

    "Let `≽` be that relation between real numbers defined by the condition:
     `x ≽ y` if and only if `x ≥ y + 1`."

    Real numbers are not in core Lean; we model `Re` by `Int`.  The relation is
    then `x ≽ y ↔ y + 1 ≤ x`, and we prove — as the paper asserts — that
    `⟨Int, ≽⟩` is a semiorder.  (`omega` discharges each linear-arithmetic goal.) -/

/-- The just-noticeable-difference relation on integers. -/
def jnd (x y : Int) : Prop := y + 1 ≤ x

theorem jnd_semiorder : Semiorder jnd where
  S1 := by intro x; simp only [jnd]; omega
  S2 := by intro x y z w hxy hzw; simp only [jnd] at *; omega
  S3 := by intro x y z w hxy hzx; simp only [jnd] at *; omega

/-! ## Section 2.  Difference structures (the class `H`)

    "Consider relational systems `𝔄 = ⟨A, D⟩` of type `⟨4⟩`.  For such systems we
     introduce the following definitions:
       `x R y` iff `xyDyy`.
       `xy M₁ zw` iff `xyDzw, zwDxy, yRx and zRy`.
       `xy Mⁿ⁺¹ zw` iff there exist `u,v ∈ A` such that `xy Mⁿ uv` and `uv M₁ zw`."

    with axioms `A1`–`A8`.  The intended reading: `xyDzw` says the interval `x`–`y`
    is no greater than the interval `z`–`w`; the numerical model is `⟨Re, Δ⟩` with
    `xyΔzw ↔ x - y ≥ z - w`. -/

namespace Difference

variable {A : Type} (D : A → A → A → A → Prop)

/-- `x R y ≡ x y D y y`  (the induced weak ordering). -/
def R (x y : A) : Prop := D x y y y

/-- `x y M₁ z w`. -/
def M1 (x y z w : A) : Prop :=
  D x y z w ∧ D z w x y ∧ R D y x ∧ R D z y

/-- `x y Mⁿ z w`, defined by recursion on `n` (with `M⁰` taken as `M₁`). -/
def M : Nat → A → A → A → A → Prop
  | 0,     x, y, z, w => M1 D x y z w
  | n + 1, x, y, z, w => ∃ u v : A, M n x y u v ∧ M1 D u v z w

/-- Difference-measurement axioms `A1`–`A8` for a system `⟨A, D⟩` in the class `H`
    (Section 2). -/
structure InH : Prop where
  /-- `A1`. -/
  A1 : ∀ x y z w u v, D x y z w → D z w u v → D x y u v
  /-- `A2` — connectedness. -/
  A2 : ∀ x y z w, D x y z w ∨ D z w x y
  /-- `A3`. -/
  A3 : ∀ x y z w, D x y z w → D x z y w
  /-- `A4`. -/
  A4 : ∀ x y z w, D x y z w → D w z y x
  /-- `A5`. -/
  A5 : ∀ x y z u v, R D x y → D y z u v → D x z u v
  /-- `A6` — existence of a midpoint. -/
  A6 : ∀ x y, ∃ z, D x z z y ∧ D z y x y
  /-- `A7` — an existence (density) axiom. -/
  A7 : ∀ x y z w, ¬ D x y z w → ¬ R D x y →
        ∃ u, D z w x u ∧ ¬ R D x u ∧ ¬ R D u y
  /-- `A8` — the Archimedean axiom (not first-order expressible). -/
  A8 : ∀ x y z w, D x y z w → ¬ R D x y →
        ∃ u v : A, ∃ n : Nat, M D n z u v w ∧ D z u x y

end Difference

/-! ### The numerical difference relation `⟨Int, Δ⟩`

    `x y Δ z w ↔ x - y ≥ z - w`.  We verify the algebraic axioms `A1`–`A4` that
    are first-order and hold over any linearly ordered abelian group (here `Int`);
    `omega` closes each.  The existence/Archimedean axioms `A5`–`A8` involve the
    full structure and are recorded in `Difference.InH`. -/

def numD (x y z w : Int) : Prop := z - w ≤ x - y

theorem numD_A1 : ∀ x y z w u v : Int, numD x y z w → numD z w u v → numD x y u v := by
  intro x y z w u v; simp only [numD]; omega

theorem numD_A2 : ∀ x y z w : Int, numD x y z w ∨ numD z w x y := by
  intro x y z w; simp only [numD]; omega

theorem numD_A3 : ∀ x y z w : Int, numD x y z w → numD x z y w := by
  intro x y z w; simp only [numD]; omega

theorem numD_A4 : ∀ x y z w : Int, numD x y z w → numD w z y x := by
  intro x y z w; simp only [numD]; omega

/-! ## Section 3.  Axiomatizability (Theorem statement)

    "A finitary theory of measurement `K` is axiomatizable by a universal sentence
     [iff …]."  We record the notion of universal (first-order) axiomatizability
     abstractly; the effective/finite characterization is stated as a target. -/

/-- A theory `K` is *finitely axiomatizable by a universal sentence* iff there is
    a predicate `φ` on binary systems — intended to be expressible as a single
    universal first-order sentence — whose finite models are exactly the finite
    members of `K` (Section 3).  Faithful statement only. -/
def UniversallyAxiomatizable (K : BinSystem → Prop) : Prop :=
  ∃ φ : BinSystem → Prop, ∀ 𝔄 : BinSystem, K 𝔄 ↔ φ 𝔄

/-- Section 3, main axiomatizability theorem (statement).
    TODO: a faithful proof requires the finite model theory of Section 3; left as
    an obligation rather than fabricated. -/
theorem finitary_universally_axiomatizable
    (K : BinSystem → Prop) (_h : ∃ T : TheoryOfMeasurement K, True) :
    UniversallyAxiomatizable K := by
  sorry -- TODO: Section 3 finite-model-theoretic argument.

end ScottSuppes1958
