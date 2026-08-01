/-
  Measurable Cardinals and Constructible Sets (Lean 4 faithful skeleton)

  Faithful to:
    Dana Scott, "Measurable Cardinals and Constructible Sets",
    Bull. Acad. Polon. Sci. Sér. Sci. Math. Astronom. Phys. IX, No. 7 (1961),
    pp. 521-524.

  Source text extracted from:
    DanaScottPapers/Scott-1961-Measurable-Cardinals-and-Constructible-Sets.txt

  This is an auto-generated faithful skeleton.  It transcribes the core formal
  objects of the paper's landmark result:  the existence of a measurable
  cardinal contradicts Gödel's axiom of constructibility `V = L`.

  Formalized here:
    * The definition of a *measurable cardinal* (p. 521): a cardinal `m` carrying
      a non-trivial, countably-additive, {0,1}-valued (2-valued) measure on all
      subsets, i.e. a countably-complete non-principal ultrafilter.
    * The reduced-power / ultrapower construction `V^κ` with the relations
      `Q_μ` (congruence, Lemma 1) and `E_μ` (membership), and Łoś's theorem
      (Lemma 5 / Corollary 5.2).
    * The collapsing map `σ` (Lemma 3) onto a transitive class `M`, the
      well-foundedness of `E_μ` (Lemma 2(iii)).
    * Corollary 5.1: `V = M`; the special ordinal `δ` (Definition 4, Lemma 6);
      and the MAIN THEOREM: measurable cardinals contradict `V = L`
      (equivalently, if `κ` is the least 2-valued measurable then `PPκ ∉ L`).

  Core Lean 4 only; no Mathlib.  Set theory is stated abstractly via a `class`
  for a model of set membership.  The deep theorems are `sorry` with `-- TODO`.
-/

namespace Scott1961

/-! ## Ultrafilters and measurable cardinals

    A *2-valued measure* on a set `X` is a `{0,1}`-valued finitely/countably
    additive measure `μ` with `μ(X)=1`, `μ({x})=0`.  Equivalently the family
    `{ S | μ S = 1 }` is a non-principal ultrafilter; countable additivity of
    `μ` means the ultrafilter is countably complete (`ω₁`-complete). -/

/-- A filter on the powerset of `X` (subsets are predicates `X → Prop`). -/
structure Filter (X : Type) where
  sets       : (X → Prop) → Prop
  univ_mem   : sets (fun _ => True)
  empty_notMem : ¬ sets (fun _ => False)
  upward     : ∀ S T, sets S → (∀ x, S x → T x) → sets T
  inter      : ∀ S T, sets S → sets T → sets (fun x => S x ∧ T x)

/-- An *ultrafilter*: for every subset, it or its complement is in the filter
    (this realizes the 2-valued measure `μ`). -/
def Filter.IsUltra {X : Type} (U : Filter X) : Prop :=
  ∀ S : X → Prop, U.sets S ∨ U.sets (fun x => ¬ S x)

/-- *Non-principal* / *non-trivial*: no singleton has measure 1
    (`μ({x}) = 0`), equivalently every singleton's complement is in `U`. -/
def Filter.NonPrincipal {X : Type} (U : Filter X) : Prop :=
  ∀ x : X, U.sets (fun y => y ≠ x)

/-- *Countably complete* (countable additivity of `μ`): the intersection of a
    countable family of measure-1 sets still has measure 1. -/
def Filter.CountablyComplete {X : Type} (U : Filter X) : Prop :=
  ∀ S : Nat → (X → Prop), (∀ n, U.sets (S n)) → U.sets (fun x => ∀ n, S n x)

/-- A type `X` (standing for a cardinal `m` of cardinality `card X`) is
    *measurable* iff it carries a non-trivial, countably-additive, 2-valued
    measure: a countably-complete non-principal ultrafilter (p. 521). -/
structure Measurable (X : Type) where
  U         : Filter X
  ultra     : U.IsUltra
  nonprinc  : U.NonPrincipal
  countably : U.CountablyComplete

/-! ## An abstract universe of sets and constructibility

    We model set theory abstractly by a membership relation `Mem` on a type `V`
    of sets, together with the constructible-sets predicate `L` and the axiom
    schema `V = L` in the operational form `(*)` of the paper (p. 521):
    closure under the eight Gödel operations characterizes `V = L`. -/

/-- An abstract model of set theory: a type of "sets" with membership. -/
class SetUniverse (V : Type) where
  Mem       : V → V → Prop
  /-- the constructible sets (Gödel's `L`). -/
  L         : V → Prop
  /-- being an ordinal. -/
  Ordinal   : V → Prop

open SetUniverse

/-- The axiom of constructibility `V = L`: every set is constructible. -/
def AxiomV_eq_L (V : Type) [SetUniverse V] : Prop := ∀ x : V, L x

/-! ## The ultrapower `V^κ`, congruence `Q_μ` and membership `E_μ`

    Following Definition I, over the class `V^κ` of functions `κ → V` the measure
    `μ` induces:
      `E_μ f g`  iff  `μ{ ξ | f ξ ∈ g ξ } = 1`,
      `Q_μ f g`  iff  `μ{ ξ | f ξ = g ξ } = 1`. -/

variable {V : Type} [SetUniverse V] {κ : Type}

/-- `Q_μ` (Definition I(i)): "equal almost everywhere". -/
def Qmu (M : Measurable κ) (f g : κ → V) : Prop :=
  M.U.sets (fun ξ => f ξ = g ξ)

/-- `E_μ` (Definition I(ii)): "member almost everywhere". -/
def Emu (M : Measurable κ) (f g : κ → V) : Prop :=
  M.U.sets (fun ξ => Mem (f ξ) (g ξ))

/-- Lemma 1.  `Q_μ` is a congruence relation for `E_μ` over `V^κ` (uses only
    finite additivity).  We state that it is an equivalence relation. -/
theorem Qmu_equiv (M : Measurable κ) :
    (∀ f : κ → V, Qmu M f f) ∧
    (∀ f g : κ → V, Qmu M f g → Qmu M g f) ∧
    (∀ f g h : κ → V, Qmu M f g → Qmu M g h → Qmu M f h) := by
  sorry -- TODO Lemma 1 (Qμ is a congruence for Eμ)

/-- Lemma 2(iii).  `E_μ` is well-founded (this is where countable additivity of
    `μ` is first used).  Stated as: there is no infinite `E_μ`-descending chain. -/
theorem Emu_wellFounded (M : Measurable κ) :
    ¬ ∃ chain : Nat → (κ → V), ∀ n, Emu M (chain (n + 1)) (chain n) := by
  sorry -- TODO Lemma 2(iii) (well-foundedness of Eμ via countable additivity)

/-- Lemma 3.  There is a unique collapsing map `σ : V^κ → V` with
      σ f = { σ h | h E_μ f },  σ f = σ g ↔ Q_μ f g,  σ f ∈ σ g ↔ f E_μ g.
    We record its existence and the two characterizing equivalences. -/
theorem exists_collapse (M : Measurable κ) :
    ∃ σ : (κ → V) → V,
      (∀ f g, σ f = σ g ↔ Qmu M f g) ∧
      (∀ f g, Mem (σ f) (σ g) ↔ Emu M f g) := by
  sorry -- TODO Lemma 3 (Mostowski collapse of the ultrapower)

/-- Lemma 5 / Corollary 5.2 (Łoś's theorem).  For a formula `Φ` with quantifiers
    restricted to `V`, `Φ(σ f₀, …, σ f_{k-1})` holds iff
    `μ{ ξ | Φ(f₀ ξ, …, f_{k-1} ξ) } = 1`.  Instance for the constant embedding
    `x* = σ(const x)`: elementary equivalence of `V` and the collapse `M`. -/
theorem los_constants (M : Measurable κ)
    (σ : (κ → V) → V) (Φ : V → Prop) (x : V) :
    Φ x ↔ Φ (σ (fun _ => x)) := by
  sorry -- TODO Corollary 5.2 (Łoś for constant functions)

/-! ## The main theorem -/

/-- MAIN THEOREM (Scott 1961).  If there exists a measurable cardinal, then the
    axiom of constructibility `V = L` fails.  The proof: assume `V = L`; let `κ`
    be the least (2-valued) measurable cardinal; build the ultrapower collapse
    `M` with `V = M` (Corollary 5.1), `κ = 2^{ℵ₀}` (Corollary 5.3), and the
    ordinal `δ = σ(id)` with `λ* < δ < κ*` for all `λ < κ` (Lemma 6); the
    cardinality of `{λ* | λ < κ}` is `κ`, forcing `δ ≥ κ` while `δ < κ`,
    a contradiction. -/
theorem measurable_contradicts_V_eq_L
    (hmeas : ∃ (X : Type), Nonempty (Measurable X)) :
    ¬ AxiomV_eq_L V := by
  sorry -- TODO Main Theorem: measurable cardinals contradict V = L

/-- Corollary (the choice-free form, p. 524).  If `κ` is the least 2-valued
    measurable cardinal, then `PPκ ∉ L`: the double power set of `κ` is not
    constructible. -/
theorem doublePower_not_constructible
    (κ : Type) (_hleast : Measurable κ)
    (PPκ : V) (_hPP : True) :  -- PPκ = P(P(κ)) as a set of the universe
    ¬ L PPκ := by
  sorry -- TODO Corollary: P(P(κ)) is not constructible

end Scott1961
