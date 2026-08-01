/-
  On Completing Ordered Fields — the order-density completion of an
  arbitrary ordered field

  Faithful to:
    D. Scott, "On Completing Ordered Fields",
    in Applications of Model Theory to Algebra, Analysis, and Probability
    (W. A. J. Luxemburg, ed.), Holt, Rinehart & Winston, 1969, pp. 274-278.

  Source text extracted from:
    DanaScottPapers/Scott-1969-On-Completing-Ordered-Fields.txt

  Auto-generated faithful skeleton (core Lean 4 only; no Mathlib).

  Scott shows that *every* ordered field K — not only ℚ — has a completion:
  a complete ordered field K̂ in which K is order-dense, unique up to a unique
  K-fixing isomorphism.  The right notion of completeness for arbitrary
  cardinality is:

    Definition.  An ordered field is *complete* if it has no proper extension
    to an ordered field in which the given field is order-dense.

  with the auxiliary notions (K ⊆ L):
    • K is *dense* in L        : between any two distinct elements of L lies one of K;
    • K is *cofinal* in L      : every element of L is exceeded by an element of K;
    • K is *coinitial* in L    : for every ε > 0 in L there is 0 < δ < ε in K.

  We axiomatize an ordered field from scratch (`class OrderedField`), model the
  inclusion `K ⊆ L` as a strictly-monotone field embedding `Hom K L`, and state
  Scott's two theorems as targets:

    Theorem 1.  Every K has a complete ordered field K̂ in which K is dense;
                any two such are isomorphic by a unique K-fixing isomorphism.
    Theorem 2.  If K is dense in L, then K̂ is dense in L̂ (real-closures).

  We prove the tractable structural facts (e.g. a field embedding is injective).
-/

namespace OnCompletingOrderedFields

/-! ## Ordered fields, axiomatized in core Lean

    We bundle the ring, field, and order operations via the core classes
    `Add, Mul, Neg, Zero, One, Inv, LT` so the usual notation is available. -/
class OrderedField (K : Type)
    extends Add K, Mul K, Neg K, Zero K, One K, Inv K, LT K where
  add_assoc : ∀ a b c : K, (a + b) + c = a + (b + c)
  add_comm : ∀ a b : K, a + b = b + a
  zero_add : ∀ a : K, 0 + a = a
  neg_add_cancel : ∀ a : K, -a + a = 0
  mul_assoc : ∀ a b c : K, (a * b) * c = a * (b * c)
  mul_comm : ∀ a b : K, a * b = b * a
  one_mul : ∀ a : K, 1 * a = a
  /-- Nonzero elements are invertible. -/
  mul_inv_cancel : ∀ a : K, a ≠ 0 → a * a⁻¹ = 1
  left_distrib : ∀ a b c : K, a * (b + c) = a * b + a * c
  zero_ne_one : (0 : K) ≠ 1
  lt_irrefl : ∀ a : K, ¬ a < a
  lt_trans : ∀ {a b c : K}, a < b → b < c → a < c
  /-- Linearity: the order is total (trichotomy). -/
  lt_trichotomy : ∀ a b : K, a < b ∨ a = b ∨ b < a
  /-- Translation invariance of `<`. -/
  add_lt_add_left : ∀ {a b : K}, a < b → ∀ c : K, c + a < c + b
  /-- Positivity is closed under multiplication. -/
  mul_pos : ∀ {a b : K}, 0 < a → 0 < b → 0 < a * b

namespace OrderedField

variable {K : Type} [OrderedField K]

/-- `<` is asymmetric: `a < b` rules out `b < a`. -/
theorem lt_asymm {a b : K} (h : a < b) : ¬ b < a := by
  intro h'
  exact lt_irrefl a (lt_trans h h')

end OrderedField

/-! ## Inclusions of ordered fields as strictly-monotone embeddings

    We model `K ⊆ L` by a strictly-monotone ring homomorphism `Hom K L`.
    Strict monotonicity encodes both order-preservation and injectivity. -/
structure Hom (K L : Type) [OrderedField K] [OrderedField L] where
  toFun : K → L
  map_add : ∀ a b, toFun (a + b) = toFun a + toFun b
  map_mul : ∀ a b, toFun (a * b) = toFun a * toFun b
  map_zero : toFun 0 = 0
  map_one : toFun 1 = 1
  /-- Strict order preservation. -/
  strictMono : ∀ {a b}, a < b → toFun a < toFun b

namespace Hom

variable {K L : Type} [OrderedField K] [OrderedField L]

/-- A strictly-monotone field embedding is injective (Scott takes `K ⊆ L`
    literally; injectivity is what licenses that). -/
theorem injective (e : Hom K L) : Function.Injective e.toFun := by
  intro a b hab
  rcases OrderedField.lt_trichotomy a b with h | h | h
  · exact absurd (hab ▸ e.strictMono h) (OrderedField.lt_irrefl _)
  · exact h
  · exact absurd (hab ▸ e.strictMono h) (OrderedField.lt_irrefl _)

end Hom

/-! ## Density, cofinality, coinitiality, completeness

    All relative to an embedding `e : Hom K L`, i.e. to an inclusion `K ⊆ L`. -/

variable {K L : Type} [OrderedField K] [OrderedField L]

/-- `K` is order-*dense* in `L`: between any two distinct elements of `L`
    there lies an element of `K`. -/
def Dense (e : Hom K L) : Prop :=
  ∀ u v : L, u < v → ∃ k : K, u < e.toFun k ∧ e.toFun k < v

/-- `K` is *cofinal* in `L`: every element of `L` is exceeded by one of `K`. -/
def Cofinal (e : Hom K L) : Prop :=
  ∀ v : L, ∃ k : K, v < e.toFun k

/-- `K` is *coinitial* in `L`: below every positive `ε ∈ L` sits a positive
    element of `K`. -/
def Coinitial (e : Hom K L) : Prop :=
  ∀ ε : L, 0 < ε → ∃ k : K, 0 < e.toFun k ∧ e.toFun k < ε

/-- An embedding is an *isomorphism* (onto) — used to say "no proper
    extension". -/
def IsIso (e : Hom K L) : Prop := Function.Surjective e.toFun

/-! ## Completeness (Scott's Definition)

    "An ordered field is complete if it has no proper extension to an ordered
    field in which the given field is order-dense."  Equivalently: every dense
    extension is already onto. -/

/-- `K` is *complete* iff every ordered field `L` in which `K` sits densely is
    reached in full — no proper dense extension exists. -/
def Complete (K : Type) [OrderedField K] : Prop :=
  ∀ (L : Type) (_ : OrderedField L) (e : Hom K L), Dense e → IsIso e

/-! ## Theorem 1 — existence and uniqueness of the completion

    "Given any ordered field K, there is a complete ordered field K̂ in which K
     is dense.  Any other complete ordered field in which K is dense is
     isomorphic to K̂ by a unique isomorphism that is the identity on K." -/

/-- Existence half of Theorem 1: every ordered field has a complete
    dense extension (its completion `K̂`). -/
def theorem1_existence (K : Type) [OrderedField K] : Prop :=
  ∃ (Khat : Type) (_ : OrderedField Khat) (e : Hom K Khat),
    Dense e ∧ Complete Khat
-- TODO: prove.  Scott's construction: extend K to a field M filling all cuts
-- (compactness / ultrapowers / adjoining indeterminates), pass to the ordered
-- quotient K' = F/I of K-finite elements modulo K-infinitesimals, then take
-- the maximal subfield K̂ ⊆ K' in which K is dense (elements = cuts not
-- invariant under a nonzero translation).  Closure of K̂ under +, −, ×, ⁻¹ and
-- its completeness are the substance of the paper.

/-- Uniqueness half of Theorem 1: any two complete dense extensions of `K` are
    isomorphic by a unique isomorphism fixing `K` — determined by the cuts. -/
def theorem1_uniqueness (K : Type) [OrderedField K] : Prop :=
  ∀ (L₁ : Type) (_ : OrderedField L₁) (e₁ : Hom K L₁)
    (L₂ : Type) (_ : OrderedField L₂) (e₂ : Hom K L₂),
    Dense e₁ → Complete L₁ → Dense e₂ → Complete L₂ →
    ∃ φ : Hom L₁ L₂, IsIso φ ∧ (∀ a : K, φ.toFun (e₁.toFun a) = e₂.toFun a)
-- TODO: prove; the map sends x ∈ L₁ to the L₂-element with the same cut in K,
-- and density forces it to preserve order and the field operations uniquely.

/-! ## Theorem 2 — density is preserved by real-closure

    "If K is dense in L, then passing to the real-closures we have K̂ dense in
     L̂."  (Consequence: K is real-closed iff K is dense in its real-closure.)

    Real-closedness is itself a substantial notion (every positive element a
    square, odd-degree polynomials have roots); we keep it abstract as a
    predicate `RealClosure`. -/

/-- `RealClosure K R e` records that `R`, via `e : Hom K R`, is a real-closure
    of `K` (kept abstract in this skeleton). -/
def RealClosure (K R : Type) [OrderedField K] [OrderedField R]
    (_e : Hom K R) : Prop := True  -- abstract placeholder; see paper for axioms

/-- Theorem 2: density transfers to real-closures. -/
def theorem2 : Prop :=
  ∀ (K L KR LR : Type) (_ : OrderedField K) (_ : OrderedField L)
    (_ : OrderedField KR) (_ : OrderedField LR)
    (e : Hom K L) (rK : Hom K KR) (rL : Hom L LR)
    (jn : Hom KR LR),
    Dense e → RealClosure K KR rK → RealClosure L LR rL →
    Dense jn
-- TODO: prove via "roots depend continuously on the coefficients": given
-- z ∈ LR and η ∈ K⁺, perturb the (monic, simple-rooted) minimal polynomial of
-- z slightly to coefficients in KR, obtaining a root within η of z in KR.

end OnCompletingOrderedFields
