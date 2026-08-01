/-
  Quine's Individuals — NF, Quine atoms, and reinterpretation by
  permutations

  Faithful to:
    D. Scott, "Quine's Individuals",
    in Logic, Methodology and Philosophy of Science (Nagel, Suppes, Tarski,
    eds.), Stanford Univ. Press, 1962, pp. 111-115.

  Source text extracted from:
    DanaScottPapers/Scott-1962-Quines-Individuals.txt

  Auto-generated faithful skeleton (core Lean 4 only; no Mathlib).

  This is a short technical note, and most of its content resists a shallow
  Lean encoding.  Scott proves that the sentence

    (*)   ∃y ∀x (x ∈ y ↔ x = y)          — "there exists an individual"

  is *independent* of Quine's New Foundations (NF): if NF is consistent, so are
  NF + (*) and NF + ¬(*).  The proof is a finitary permutation argument: one
  exhibits a *level term* τ (a definable involution) and reinterprets `x ∈ y`
  as `x ∈ τ(y)`; a metatheorem shows that if τ is a "permutation" then this
  reinterpretation carries theorems of NF to theorems of NF, so a proof of Ψᵗ
  yields the relative consistency of Ψ.

  The load-bearing notions — *stratified* formulas and *level* terms — are
  syntactic (they constrain how numerals may be assigned to variables), and a
  faithful treatment needs a deep embedding of NF's syntax and its proof
  system.  That is out of scope for a skeleton.  We therefore transcribe only
  the genuinely concrete pieces: NF extensionality, the sentence (*) (a Quine
  atom is a self-singleton), and the *semantic* core of the permutation method
  — reinterpreting membership through a map τ and the notion of an involution.
-/

namespace QuinesIndividuals

variable {Obj : Type}

/-- Membership `∈` of a model of NF. -/
abbrev Mem (M : Obj → Obj → Prop) (x y : Obj) : Prop := M x y

/-! ## Axiom (I): extensionality

    "∀a ∀b (∀z (z ∈ a ↔ z ∈ b) → a = b)". -/
def Extensionality (M : Obj → Obj → Prop) : Prop :=
  ∀ a b, (∀ z, M z a ↔ M z b) → a = b

/-! ## The sentence (*): existence of a Quine individual

    `x ∈ y ↔ x = y` says the sole member of `y` is `y` itself — `y` is a Quine
    atom (a self-singleton).  (*) asserts such a `y` exists. -/
def StarSentence (M : Obj → Obj → Prop) : Prop :=
  ∃ y, ∀ x, M x y ↔ x = y

/-- Being a Quine atom (individual): `y` is its own unique member. -/
def IsQuineAtom (M : Obj → Obj → Prop) (y : Obj) : Prop :=
  ∀ x, M x y ↔ x = y

/-- (*) holds iff some object is a Quine atom. -/
theorem star_iff_exists_atom (M : Obj → Obj → Prop) :
    StarSentence M ↔ ∃ y, IsQuineAtom M y := Iff.rfl

/-! ## Reinterpreting membership through a term τ

    For a (level) term τ, Scott replaces the atomic formula `x ∈ y` by
    `x ∈ τ(y)`.  Semantically this is a new membership relation `Memτ`. -/
def Memτ (M : Obj → Obj → Prop) (τ : Obj → Obj) (x y : Obj) : Prop :=
  M x (τ y)

/-- τ is an *involution* (Scott's permutations are involutions):
    `τ(τ(x)) = x`. -/
def Involution (τ : Obj → Obj) : Prop := ∀ x, τ (τ x) = x

/-- If `τ` is an involution and `M` is extensional, the reinterpreted
    membership `Memτ` is again extensional — a small semantic fragment of the
    permutation metatheorem (the extensionality-preservation case). -/
theorem memτ_extensional (M : Obj → Obj → Prop) (τ : Obj → Obj)
    (hτinj : Function.Injective τ) (hExt : Extensionality M) :
    Extensionality (Memτ M τ) := by
  intro a b h
  -- `∀ z, M z (τ a) ↔ M z (τ b)` gives `τ a = τ b` by extensionality of `M`,
  -- and injectivity of `τ` gives `a = b`.
  exact hτinj (hExt (τ a) (τ b) h)

/-! ## The metatheorem and independence (targets)

    METATHEOREM (Scott, p. 113).  If τ is a level term with
      NF ⊢ ∀y ∃z ∀x (y = τ(x) ↔ x = z),
    then for every Ψ, `NF ⊢ Ψ` implies `NF ⊢ Ψᵗ`, where Ψᵗ replaces every
    `φ ∈ ψ` by `φ ∈ τ(ψ)`.

    COROLLARY.  If τ is such a *permutation* and `NF ⊢ Ψᵗ`, then Ψ is
    consistent with NF (a finitary relative-consistency proof).

    Scott exhibits permutations making (**) `∃y τ(y) = ι(y)` provable and
    others making its negation provable, whence (*) is independent of NF.

    A faithful statement needs NF's proof relation `⊢`, stratified
    comprehension (axiom schema II, syntactic), and the substitution Ψ ↦ Ψᵗ on
    the deep-embedded syntax.  We record the independence conclusion only
    informally here. -/

-- TODO (needs a deep embedding of NF syntax + `⊢` + stratification):
--   * axiom schema (II): stratified comprehension `∃y ∀x (x ∈ y ↔ Φ)`,
--       for stratified Φ with `y` not free;
--   * the reinterpretation Ψ ↦ Ψᵗ and the permutation metatheorem;
--   * both `Con(NF) → Con(NF + (*))` and `Con(NF) → Con(NF + ¬(*))`.

end QuinesIndividuals
